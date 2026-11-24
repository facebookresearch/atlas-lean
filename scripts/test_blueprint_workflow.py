#!/usr/bin/env python3
"""Security/correctness regressions for the upstream blueprint workflow."""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

from scripts import next_task

ROOT = Path(__file__).resolve().parent.parent
# The card files: their tests run in the card job (scripts/test_cards.py), not in the wiki job.
CARD_INPUTS = ("scripts/cards.py", "scripts/card-moves.jsonl", "scripts/test_cards.py", "docs/cards.md")
WORKFLOW = ROOT / ".github" / "workflows" / "blueprint-pages.yml"
GRAPH_SYNC = ROOT / ".github" / "workflows" / "graph-sync.yml"


class BlueprintWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = WORKFLOW.read_text()
        # BaseLoader preserves "on" and expressions without evaluating them.
        cls.workflow = yaml.load(cls.text, Loader=yaml.BaseLoader)
        cls.job = cls.workflow["jobs"]["wiki"]
        cls.steps = cls.job["steps"]

    def step(self, name):
        return next(step for step in self.steps if step.get("name") == name)

    def test_pull_requests_run_the_check_on_wiki_paths_and_merge_groups_never(self):
        events = self.workflow["on"]
        # Not a required check, so a merge-group run could not stop a merge; CI's
        # required build imports every v2 module together on each merge group.
        self.assertEqual(set(events), {"schedule", "pull_request", "workflow_dispatch"})
        # main is built once a day at 03:17 UTC (GitHub reads cron in UTC), not on every push.
        self.assertEqual(events["schedule"], [{"cron": "17 3 * * *"}])
        paths = events["pull_request"]["paths"]
        for path in (
            "blueprint/**", "scripts/generate_wiki.py", "scripts/sync_wiki.py",
            "scripts/extract_v2_lean_dependencies.py", "scripts/dump_v2_dependencies.lean",
            "scripts/list_v2_modules.sh",
            "scripts/check_blueprint_site.py", "scripts/taxonomy.json", "scripts/wiki-sync.json",
            "scripts/mathgraph-map.jsonl", "scripts/import_mathgraph.py", "scripts/check_public_references.py",
            "scripts/requirements-blueprint.txt", "mkdocs.yml", "theme/**", "hooks/**",
            "docs/BLUEPRINT.md", "docs/mathgraph-import.md", ".github/workflows/blueprint-pages.yml",
            ".github/autoform-ref",
            "lean-toolchain", "lake-manifest.json", "lakefile.toml",
        ):
            self.assertIn(path, paths)
        # The reader of the list the job writes: changing it runs the tests that hold the two to one format.
        self.assertIn("scripts/next_task.py", paths)
        # Every test module the job runs is in the filter, so changing a test runs it.
        tests = self.step("Test the wiki scripts")["run"]
        for module in re.findall(r"scripts\.(test_\w+)", tests):
            self.assertIn(f"scripts/{module}.py", paths)
        # So is every module of scripts/ the importer imports, whose tests run only in this job.
        importer = (ROOT / "scripts" / "import_mathgraph.py").read_text()
        modules = re.findall(r"(?m)^    from \. import (\w+)", importer)
        self.assertIn("check_public_references", modules)
        for module in modules:
            self.assertIn(f"scripts/{module}.py", paths)
        # A path that no longer exists would silently stop triggering the check. The sync baseline
        # scripts/wiki-sync.json arrives with the wiki's last page batch, and the import map
        # scripts/mathgraph-map.jsonl with the first imported manifest, so they may not exist yet. The card
        # inputs are checked by the card tests, in their own job, so that no card file can fail this one.
        for path in paths:
            if path in ("scripts/wiki-sync.json", "scripts/mathgraph-map.jsonl") or path in CARD_INPUTS:
                continue
            target = ROOT / path.removesuffix("/**")
            self.assertTrue(target.is_dir() if path.endswith("/**") else target.is_file(), path)
        for name, event in events.items():
            if isinstance(event, dict):
                self.assertNotIn("paths-ignore", event)
                if name != "pull_request":
                    self.assertNotIn("paths", event)
        self.assertNotIn("if", self.job)

    def test_reviewed_pin_is_a_full_sha(self):
        pin = (ROOT / ".github" / "autoform-ref").read_text().strip()
        self.assertRegex(pin, r"\A[0-9a-f]{40}\Z")
        self.assertIn("^[0-9a-f]{40}$", self.step(
            "Read the reviewed Autoform pin")["run"])
        self.assertNotIn("git ls-remote", self.text)
        self.assertNotIn("AUTOFORM_AUTOPIN", self.text)
        self.assertNotIn("pin", self.workflow["jobs"])

    def test_every_action_is_sha_pinned(self):
        for job in self.workflow["jobs"].values():
            for step in job["steps"]:
                if "uses" in step:
                    self.assertRegex(step["uses"], r"@[0-9a-f]{40}\Z")

    def test_untrusted_build_has_no_write_token_or_persistent_credentials(self):
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertNotIn("permissions", self.job)
        checkout = self.step("Check out project")
        self.assertEqual(checkout["with"]["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["with"]["sparse-checkout"])
        self.assertIn("!/Atlas/", checkout["with"]["sparse-checkout"])
        self.assertNotIn("secrets.", self.text)

    def test_current_build_and_dump_fail_closed(self):
        build = self.step("Build the current v2 libraries")
        self.assertEqual(build["run"],
                         "lake build MathlibExt CSLibExt PhyslibExt Domains WantedExt")
        dump = self.step("Dump declaration dependencies")
        self.assertNotIn("continue-on-error", build)
        self.assertNotIn("continue-on-error", dump)
        self.assertNotIn("if", dump)
        self.assertIn("set -euo pipefail", dump["run"])
        self.assertNotIn("set +e", self.text)
        self.assertNotIn("collisions", dump["run"])
        positions = {s.get("name"): i for i, s in enumerate(self.steps)}
        self.assertLess(positions[build["name"]], positions[dump["name"]])
        self.assertLess(positions[dump["name"]], positions[
            "Collapse dependencies onto the wiki articles"])

    def test_memory_heavy_production_targets_are_serialized(self):
        script = self.step("Build memory-heavy modules one at a time")["run"]
        commands = [row for row in script.splitlines() if row.startswith("lake build ")]
        self.assertEqual(commands, [
            "lake build MathlibExt.Combinatorics.Enumerative.Nontrivial1234_3412Classes",
            "lake build MathlibExt.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound",
        ])

    @staticmethod
    def dump_fixture(root):
        """A repository with the dump step's module-listing script."""
        (root / "scripts").mkdir()
        shutil.copy2(ROOT / "scripts/list_v2_modules.sh", root / "scripts")

    def test_dump_refuses_missing_compiled_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.dump_fixture(root)
            (root / ".lake/build/lib/lean").mkdir(parents=True)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "MathlibExt").mkdir()
            (root / "MathlibExt/Example.lean").write_text("-- fixture\n")
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            result = subprocess.run(
                ["bash", "-c", self.step("Dump declaration dependencies")["run"]],
                cwd=root, text=True, capture_output=True, check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Missing compiled module: MathlibExt/Example.lean",
                          result.stderr)
            self.assertFalse((root / "v2-dependencies.jsonl").exists())

    def test_dump_reads_non_ascii_paths_literally(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.dump_fixture(root)
            (root / ".lake/build/lib/lean/MathlibExt").mkdir(parents=True)
            (root / ".lake/build/lib/lean/MathlibExt/Étale.olean").write_text("")
            (root / "bin").mkdir()
            (root / "bin/lake").write_text("#!/usr/bin/env bash\necho '{}'\n")
            (root / "bin/lake").chmod(0o755)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "MathlibExt").mkdir()
            (root / "MathlibExt/Étale.lean").write_text("-- fixture\n")
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            result = subprocess.run(
                ["bash", "-c", self.step("Dump declaration dependencies")["run"]],
                cwd=root, text=True, capture_output=True, check=False,
                env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}"},
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((root / "v2-modules.txt").read_text(encoding="utf-8"),
                             "MathlibExt.Étale\n")

    def test_dump_refuses_a_partial_module_list(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.dump_fixture(root)
            (root / ".lake/build/lib/lean/MathlibExt").mkdir(parents=True)
            (root / ".lake/build/lib/lean/MathlibExt/Example.olean").write_text("")
            (root / "bin").mkdir()
            # `git ls-files` lists one module, then fails.
            (root / "bin/git").write_text(
                "#!/usr/bin/env bash\nprintf 'MathlibExt/Example.lean\\0'\nexit 74\n")
            (root / "bin/lake").write_text("#!/usr/bin/env bash\necho '{}'\n")
            for name in ("git", "lake"):
                (root / "bin" / name).chmod(0o755)
            result = subprocess.run(
                ["bash", "-c", self.step("Dump declaration dependencies")["run"]],
                cwd=root, text=True, capture_output=True, check=False,
                env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}"},
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((root / "v2-dependencies.jsonl").exists())
            self.assertFalse((root / "v2-dependencies.jsonl.gz").exists())

    def test_the_import_map_only_grows(self):
        # Right after the wiki tests: every line of scripts/mathgraph-map.jsonl is checked, and on a PR the base
        # commit's map, which the checkout of the merge commit lacks until it is fetched, must be its start, each line
        # appended since recording a page the PR adds.
        name = "Check that the import map only grows"
        names = [step.get("name") for step in self.steps]
        self.assertEqual(names.index(name), names.index("Test the wiki scripts") + 1)
        step = self.step(name)
        self.assertNotIn("continue-on-error", step)
        # The base commit arrives through the environment, never interpolated into the script.
        self.assertEqual(step["env"], {"BASE_SHA": "${{ github.event.pull_request.base.sha || '' }}"})
        self.assertNotIn("merge_group", step["env"]["BASE_SHA"])
        self.assertNotIn("${{", step["run"])
        # The importer imports Autoform: the step runs with the wiki tests' packages.
        def packages(script):
            return re.findall(r"--with (\S+)", script)

        self.assertEqual(packages(step["run"]), packages(self.step("Test the wiki scripts")["run"]))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "bin").mkdir()
            for tool in ("git", "uv"):
                (root / "bin" / tool).write_text(f'#!/usr/bin/env bash\nprintf \'%s\\n\' "{tool} $*" >> calls.txt\n')
                (root / "bin" / tool).chmod(0o755)
            for base in ("", "0123456789abcdef0123456789abcdef01234567"):
                with self.subTest(base=base):
                    (root / "calls.txt").write_text("")
                    result = subprocess.run(
                        ["bash", "-c", step["run"]], cwd=root, text=True, capture_output=True, check=False,
                        env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}", "BASE_SHA": base,
                             "AUTOFORM_SOURCE": "https://example.com/autoform.git", "AUTOFORM_REF": "0" * 40},
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    calls = (root / "calls.txt").read_text().splitlines()
                    command = "python scripts/import_mathgraph.py --check-map"
                    if base:
                        self.assertEqual(calls[0], f"git fetch --no-tags --depth=1 origin {base}")
                        self.assertTrue(calls[1].startswith("uv run --no-project"))
                        self.assertTrue(calls[1].endswith(f"{command} --base {base}"))
                    else:
                        self.assertEqual(len(calls), 1)
                        self.assertTrue(calls[0].endswith(command))

    def test_ci_builds_are_restored_and_only_the_mathlib_dump_is_saved_outside_pull_requests(self):
        # CI's keys and paths, so that both workflows read the entries CI saves from main (ci.yml): the build of the
        # commit a pull request is tested against, else main's newest, and the package builds, which only change with
        # the pins. They are restored after `lake exe cache get` clones the packages.
        names = [step.get("name") for step in self.steps]
        pins = "${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}"
        restore = self.step("Restore local build")
        self.assertIn("actions/cache/restore@", restore["uses"])
        self.assertEqual(restore["with"]["path"], ".lake/build")
        self.assertEqual(restore["with"]["key"], f"lake-build-{pins}-${{{{ steps.base.outputs.sha }}}}")
        self.assertEqual(restore["with"]["restore-keys"].strip(), f"lake-build-{pins}-")
        packages = self.step("Restore the package builds")
        self.assertIn("actions/cache/restore@", packages["uses"])
        self.assertEqual(packages["with"]["path"].splitlines(),
                         [".lake/packages/cslib/.lake/build", ".lake/packages/Physlib/.lake/build"])
        self.assertEqual(packages["with"]["key"], f"lake-deps-{pins}")
        self.assertNotIn("restore-keys", packages["with"])
        self.assertLess(names.index("Fetch Mathlib cache"), names.index("Restore the package builds"))
        self.assertLess(names.index("Find the base build"), names.index("Restore local build"))
        # A restore that fails part-way keeps what it extracted and reports no key: Lake must not trust it.
        removal = self.step("Remove a failed restore")
        self.assertEqual(removal["env"], {
            "PACKAGE_BUILDS": "${{ steps.package-builds.outputs.cache-matched-key }}",
            "LOCAL_BUILD": "${{ steps.build-cache.outputs.cache-matched-key }}",
        })
        self.assertEqual(packages["id"], "package-builds")
        self.assertEqual(restore["id"], "build-cache")
        self.assertEqual(names.index("Remove a failed restore"), names.index("Restore local build") + 1)
        self.assertLess(names.index("Restore the package builds"), names.index("Remove a failed restore"))
        self.assertLess(names.index("Remove a failed restore"), names.index("Build memory-heavy modules one at a time"))
        builds = (".lake/packages/cslib/.lake/build", ".lake/packages/Physlib/.lake/build", ".lake/build")
        for matched, kept in ((("", ""), ()), (("lake-deps-k", ""), builds[:2]), (("", "lake-build-k"), builds[2:]),
                              (("lake-deps-k", "lake-build-k"), builds)):
            with tempfile.TemporaryDirectory() as directory:
                for build in builds:
                    (Path(directory) / build / "lib").mkdir(parents=True)
                subprocess.run(["bash", "-c", removal["run"]], cwd=directory, check=True,
                               env={**os.environ, "PACKAGE_BUILDS": matched[0], "LOCAL_BUILD": matched[1]})
                self.assertEqual([b for b in builds if (Path(directory) / b / "lib").is_dir()], list(kept), matched)
        # A pull request's checkout is a merge commit whose first parent is the commit it is tested against; other
        # runs look for their own commit.
        with tempfile.TemporaryDirectory() as directory:
            def git(*args):
                return subprocess.run(["git", "-C", directory, "-c", "user.name=t", "-c", "user.email=t@t", *args],
                                      check=True, capture_output=True, text=True).stdout.strip()

            git("init", "-q")
            git("commit", "-q", "--allow-empty", "-m", "base")
            base = git("rev-parse", "HEAD")
            git("checkout", "-q", "-b", "topic")
            git("commit", "-q", "--allow-empty", "-m", "change")
            git("checkout", "-q", base)
            git("merge", "-q", "--no-ff", "-m", "merge", "topic")
            merge = git("rev-parse", "HEAD")
            # The checkout is a depth-one clone, where `HEAD^1` does not resolve.
            clone = Path(directory) / "clone"
            subprocess.run(["git", "clone", "-q", "--depth", "1", f"file://{directory}", str(clone)], check=True)
            for event, expected in (("pull_request", base), ("schedule", merge), ("workflow_dispatch", merge)):
                output = Path(directory) / f"{event}.out"
                subprocess.run(["bash", "-c", self.step("Find the base build")["run"]], cwd=clone, check=True,
                               env={**os.environ, "GITHUB_EVENT_NAME": event, "GITHUB_SHA": merge,
                                    "GITHUB_OUTPUT": str(output)})
                self.assertEqual(output.read_text(), f"sha={expected}\n", event)
        # The Mathlib dump and the graph built from it depend only on the pins and the scripts that make them. Runs
        # other than pull requests save them once per key; a restored graph skips the dump and the graph. No other
        # cache is saved here.
        mathlib = {step.get("name"): step for step in self.workflow["jobs"]["mathlib"]["steps"]}
        cached = mathlib["Restore the Mathlib graph"]
        self.assertIn("actions/cache/restore@", cached["uses"])
        self.assertEqual(cached["with"]["key"], "mathlib-graph-${{ runner.os }}-${{ hashFiles('lean-toolchain', "
                         "'lake-manifest.json', 'scripts/dump_mathlib_dependencies.lean', "
                         "'scripts/extract_mathlib_graph.py', 'scripts/extract_v2_lean_dependencies.py') }}")
        self.assertNotIn("restore-keys", cached["with"])
        self.assertEqual(cached["with"]["path"].splitlines(), [
            f"mathlib-graph/{name}" for name in ("mathlib-dump.jsonl.gz", "mathlib-dump-meta.json", "nodes.jsonl.gz",
                                                 "edges.jsonl.gz", "graph-meta.json")])
        order = list(mathlib)
        miss = "steps.mathlib-graph.outputs.cache-hit != 'true'"
        self.assertEqual([name for name, step in mathlib.items() if "if" in step and "cache-hit" in step["if"]],
                         ["Dump the Mathlib declarations", "Build the Mathlib graph", "Save the Mathlib graph"])
        for name in ("Dump the Mathlib declarations", "Build the Mathlib graph"):
            self.assertEqual(mathlib[name]["if"], miss, name)
            self.assertLess(order.index("Restore the Mathlib graph"), order.index(name), name)
        self.assertIn("extract_mathlib_graph.py graph", mathlib["Build the Mathlib graph"]["run"])
        save = mathlib["Save the Mathlib graph"]
        self.assertEqual(save["if"], f"{miss} && github.event_name != 'pull_request'")
        self.assertEqual(save["with"], {"path": cached["with"]["path"],
                                        "key": "${{ steps.mathlib-graph.outputs.cache-primary-key }}"})
        self.assertEqual(order.index("Save the Mathlib graph"), order.index("Build the Mathlib graph") + 1)
        self.assertEqual(order.index("Build the Mathlib graph"), order.index("Dump the Mathlib declarations") + 1)
        saves = [step for job in self.workflow["jobs"].values() for step in job["steps"]
                 if step.get("uses", "").startswith(("actions/cache@", "actions/cache/save@"))]
        self.assertEqual(saves, [save])

    def test_deployment_is_opt_in_and_never_runs_on_pr_or_merge_group(self):
        jobs = self.workflow["jobs"]
        deploy, promote = jobs["deploy"], jobs["promote"]
        self.assertEqual(deploy["needs"], "wiki")
        for job in (deploy, promote):
            self.assertEqual(job["permissions"], {
                "pages": "write", "id-token": "write", "deployments": "read", "contents": "read",
            })
            self.assertEqual(job["environment"]["name"], "github-pages")
        upload = next(step for step in jobs["mathlib-pages"]["steps"] if step.get("name") == "Upload the packed site")
        conditions = [deploy["if"], promote["if"], self.step("Upload Pages artifact")["if"], upload["if"]]
        for condition in conditions:
            for clause in ("vars.BLUEPRINT_PAGES == 'true'",
                           "github.ref == 'refs/heads/main'",
                           "github.event_name != 'pull_request'",
                           "github.event_name != 'merge_group'"):
                self.assertIn(clause, condition)
            # Scheduled and manual runs of main publish, so no clause may require a push.
            self.assertNotIn("push", condition)
        # Each job first reads the commit of the published site and fails, publishing nothing, unless the site is of
        # this run's commit or of an ancestor: a re-run never takes the site back, and a deployment job that succeeds
        # is one that published. It runs no repository code.
        for job in (deploy, promote):
            check, *publish = job["steps"]
            self.assertEqual(check["name"], "Check the commit of the published site")
            self.assertEqual(check["run"], deploy["steps"][0]["run"])
            self.assertEqual(check["env"], {"GH_TOKEN": "${{ github.token }}"})
            self.assertEqual([step["name"] for step in publish], ["Configure GitHub Pages", "Deploy"])
            for step in publish:
                self.assertIn("uses", step)
                self.assertNotIn("if", step)
                self.assertNotIn("continue-on-error", step)
            self.assertNotIn("continue-on-error", check)
            self.assertNotIn("run_attempt", job["if"])
        # GitHub Pages publishes at most 1 GB: the wiki job's site is packed for it, checked to give back every file
        # of the site, and measured as its upload packs it, before the upload.
        names = [step.get("name") for step in self.steps]
        pack, checked, upload = (self.step(name) for name in
                                 ("Pack the site for GitHub Pages", "Check the packed site", "Upload Pages artifact"))
        self.assertEqual(pack["run"], "python scripts/pack_pages_site.py pack site site-pages")
        self.assertIn("python scripts/pack_pages_site.py check site site-pages", checked["run"])
        self.assertIn("bash scripts/pages_size.sh site-pages 950000000", checked["run"])
        self.assertEqual(upload["with"]["path"], "site-pages")
        for step in (pack, checked):
            self.assertEqual(step["if"], upload["if"])
        self.assertEqual([names.index(name) for name in ("Keep the built site", "Pack the site for GitHub Pages",
                                                          "Check the packed site", "Upload Pages artifact")],
                         list(range(names.index("Keep the built site"), names.index("Keep the built site") + 4)))

    def test_a_site_is_published_only_over_one_of_the_same_or_an_earlier_commit(self):
        script = self.workflow["jobs"]["deploy"]["steps"][0]["run"]
        fake_gh = """#!/usr/bin/env python3
import json, os, sys
path = next(arg for arg in sys.argv[1:] if arg.startswith("repos/"))
state = json.loads(os.environ["FAKE"])
if state.get("fail"):
    sys.exit(1)
if "/statuses" in path:
    print(state["states"].get(path.split("/deployments/")[1].split("/")[0], ""))
elif "/deployments?" in path:
    print("\\n".join(state["deployments"]))
elif "/deployments/" in path:
    print(state["shas"][path.rsplit("/", 1)[1]])
elif "/compare/" in path:
    print(state["compare"])
"""
        live = {"shas": {"2": "b" * 40}}
        cases = [
            # Nothing was ever published, or only this job's own deployment is under way.
            ({"deployments": []}, 0),
            ({"deployments": ["4", "3"], "states": {"4": "in_progress", "3": "failure"}}, 0),
            ({"deployments": ["4", "3", "2"], "states": {"4": "in_progress", "3": "failure", "2": "success"},
              "compare": "ahead", **live}, 0),
            ({"deployments": ["2"], "states": {"2": "success"}, "compare": "identical", **live}, 0),
            ({"deployments": ["2"], "states": {"2": "success"}, "compare": "behind", **live}, 1),
            ({"deployments": ["2"], "states": {"2": "success"}, "compare": "diverged", **live}, 1),
            # Some deployment was live once and none is now: the published commit is unknown.
            ({"deployments": ["3", "2"], "states": {"3": "failure", "2": "inactive"}}, 1),
            ({"fail": True}, 1),
        ]
        with tempfile.TemporaryDirectory() as directory:
            bin_dir = Path(directory) / "bin"
            bin_dir.mkdir()
            (bin_dir / "gh").write_text(fake_gh)
            (bin_dir / "gh").chmod(0o755)
            for fake, expected in cases:
                env = {**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}", "FAKE": json.dumps(fake),
                       "GITHUB_REPOSITORY": "owner/repo", "GITHUB_SHA": "a" * 40}
                run = subprocess.run(["bash", "-c", script], env=env, capture_output=True, text=True)
                self.assertEqual(run.returncode, expected, (fake, run.stdout, run.stderr))
                if expected:
                    self.assertTrue("::error::" in run.stdout or fake.get("fail"), run.stdout)

    def test_the_pages_size_check_measures_the_archive_and_refuses_one_over_its_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory) / "site"
            site.mkdir()
            (site / "index.html").write_text("x" * 1000)
            (site / ".hidden").write_text("not uploaded")
            summary = Path(directory) / "summary.md"
            env = {**os.environ, "GITHUB_STEP_SUMMARY": str(summary)}
            script = ROOT / "scripts" / "pages_size.sh"
            fits = subprocess.run(["bash", str(script), str(site), "10240"], env=env, capture_output=True, text=True)
            over = subprocess.run(["bash", str(script), str(site), "1000"], env=env, capture_output=True, text=True)
            receipts = summary.read_text()
        self.assertEqual(fits.returncode, 0, fits.stderr)
        self.assertIn("2 files, 1012 bytes; Pages archive 10240 bytes; limit 10240 bytes", fits.stdout)
        self.assertEqual(over.returncode, 1)
        self.assertIn("::error::", over.stdout)
        self.assertEqual(len(receipts.splitlines()), 2)

    def test_the_mathlib_layer_cannot_hold_back_the_site(self):
        # The layer has its own job and check beside the wiki job, and deployment waits for the wiki job alone.
        jobs = self.workflow["jobs"]
        mathlib = jobs["mathlib"]
        self.assertNotIn("needs", mathlib)
        self.assertEqual(mathlib["timeout-minutes"], self.job["timeout-minutes"])
        self.assertDeploysWhateverTheMathlibJobsDo()
        self.assertNotIn("permissions", mathlib)
        self.assertNotIn("continue-on-error", mathlib)
        checkout = next(step for step in mathlib["steps"] if step.get("name") == "Check out project")
        self.assertEqual(checkout["with"]["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["with"]["sparse-checkout"])
        self.assertIn("!/Atlas/", checkout["with"]["sparse-checkout"])
        # The layer's job sets up Lean, restores CI's builds, builds what they lack and makes the v2 extraction with
        # the wiki job's own steps, so that `bridge` checks the layer against the extraction the site uses. It
        # downloads nothing from the wiki job, which no longer runs the layer's dump.
        steps = {step.get("name"): step for step in mathlib["steps"]}
        order = list(steps)
        names = [step.get("name") for step in self.steps]
        shared = names[names.index("Free disk space for Lean caches"):names.index("Add the Lean-owned facts to the articles")]
        self.assertEqual(shared[-1], "Collapse dependencies onto the wiki articles")
        self.assertEqual(order[order.index(shared[0]):order.index(shared[0]) + len(shared)], shared)
        for name in shared:
            self.assertEqual(steps[name], self.step(name), name)
        self.assertFalse([step for step in mathlib["steps"] if "download-artifact" in step.get("uses", "")])
        self.assertFalse([step["name"] for step in self.steps if "extract_mathlib_graph.py" in step.get("run", "")])
        # Its dump of the v2 declarations with their Mathlib uses follows the extraction, runs one Lean process and
        # has a timeout, so a hang cannot hold the job until its own; a failure fails the layer's check. The upload
        # keeps it as before and cannot fail the job.
        dump, upload = "Dump the v2 declarations with their Mathlib uses", "Keep the v2 declarations with their Mathlib uses"
        self.assertEqual(order.index(dump), order.index(shared[-1]) + 1)
        self.assertEqual(order.index(upload), order.index(dump) + 1)
        self.assertLessEqual(int(steps[dump]["timeout-minutes"]), 30)
        self.assertIn("--jobs 1 --shards 1", steps[dump]["run"])
        self.assertIn("--modules v2-modules.txt", steps[dump]["run"])
        self.assertEqual(steps[upload]["continue-on-error"], "true")
        self.assertEqual(steps[upload]["with"]["name"], "v2-mathlib-dump")
        self.assertNotIn("mathlib-graph", self.step("Keep dependency diagnostics")["with"]["path"])
        extract = steps["Extract the Mathlib layer"]["run"]
        self.assertIn("set -euo pipefail", extract)
        self.assertIn("test -s mathlib-graph/v2-mathlib-dump.jsonl.gz", extract)
        self.assertIn("--check-v2 build/lean-dependencies.json", extract)
        self.assertIn("join --strict", extract)
        for command in ("dump", "graph", "bridge", "stats"):
            self.assertTrue(any(f"extract_mathlib_graph.py {command}" in step.get("run", "")
                                for step in mathlib["steps"]), command)
        # Only the uploads may fail without failing the layer's check.
        self.assertEqual([name for name, step in steps.items() if "continue-on-error" in step],
                         [upload, "Keep the Mathlib layer"])
        self.assertEqual(steps["Keep the Mathlib layer"]["with"]["name"], "mathlib-graph")
        self.assertEqual(steps["Keep the Mathlib layer"]["if"], "always()")

    def test_the_ready_tasks_are_published_with_the_site_and_kept_on_every_run(self):
        # What the tools own (docs/BLUEPRINT.md): Autoform's task list on the checkout after lean-facts, published
        # as tasks.json.
        name = "List the ready formalization tasks"
        step = self.step(name)
        script = step["run"]
        self.assertIn("set -euo pipefail", script)
        self.assertIn('uvx --from "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}" autoform work list . --json', script)
        self.assertIn("cp build/tasks.json site-src/tasks.json", script)
        # The format it accepts is the one next_task.py reads.
        self.assertIn(f'.schema != "{next_task.SCHEMA}"', script)
        self.assertNotIn("continue-on-error", step)
        self.assertNotIn("if", step)
        names = [s.get("name") for s in self.steps]
        # After lean-facts and the render, which writes site-src/, and before MkDocs copies it into the site.
        for before in ("Add the Lean-owned facts to the articles", "Render the blueprint"):
            self.assertLess(names.index(before), names.index(name))
        self.assertLess(names.index(name), names.index("Build the Markdown site"))
        # Kept as the `tasks` artifact right after it is written, whatever the later steps do; a missing file fails.
        keep = self.step("Keep the task list")
        self.assertEqual(names.index("Keep the task list"), names.index(name) + 1)
        self.assertNotIn("if", keep)
        self.assertNotIn("continue-on-error", keep)
        self.assertEqual((keep["with"]["name"], keep["with"]["path"], keep["with"]["if-no-files-found"]),
                         ("tasks", "build/tasks.json", "error"))

    def run_task_step(self, output: str, status: int = 0):
        """Run the task step in a fixture checkout, with an Autoform that writes *output* and exits with *status*."""
        if shutil.which("jq") is None:
            self.skipTest("jq is not installed")
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q",
                        "--allow-empty", "-m", "fixture"], check=True)
        for folder in ("build", "site-src", "bin"):
            (root / folder).mkdir()
        (root / "output.json").write_text(output)
        (root / "bin" / "uvx").write_text(f'#!/bin/sh\necho "$@" > uvx-arguments\ncat output.json\nexit {status}\n')
        (root / "bin" / "uvx").chmod(0o755)
        environment = {**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}",
                       "AUTOFORM_SOURCE": "https://example.invalid/autoform.git", "AUTOFORM_REF": "a" * 40}
        result = subprocess.run(["bash", "-c", self.step("List the ready formalization tasks")["run"]], cwd=root,
                                env=environment, text=True, capture_output=True, check=False)
        git = lambda *args: subprocess.run(["git", "-C", str(root), *args], text=True, capture_output=True,
                                           check=True).stdout.strip()
        return root, result, git("rev-parse", "HEAD"), git("log", "-1", "--format=%cI", "HEAD")

    def test_tasks_json_is_autoforms_list_with_the_commit_and_the_pin(self):
        work = {"schema": next_task.SCHEMA, "open_statements": False, "source_revision": "f" * 64,
                "items": [{"article_id": "af_" + "0" * 24, "node_id": "Algebra/t", "phase": "proof", "ready": True,
                           "state": "can_prove", "lean_targets": [{"declaration": "Ext.t", "source_file": None}]}]}
        root, result, commit, date = self.run_task_step(json.dumps(work))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((root / "uvx-arguments").read_text().split(), [
            "--from", "git+https://example.invalid/autoform.git@" + "a" * 40,
            "autoform", "work", "list", ".", "--json"])
        published = json.loads((root / "site-src" / "tasks.json").read_text())
        self.assertEqual(published, {**work, "commit": commit, "commit_date": date, "autoform_ref": "a" * 40})
        self.assertEqual((root / "build" / "tasks.json").read_text(), (root / "site-src" / "tasks.json").read_text())

    def test_a_refused_or_unknown_task_list_fails_the_build(self):
        task = {"article_id": "af_" + "0" * 24, "node_id": "Algebra/t", "phase": "proof", "ready": True,
                "state": "can_prove", "lean_targets": [{"declaration": "Ext.t", "source_file": None}]}

        def listing(*items: dict) -> str:
            return json.dumps({"schema": next_task.SCHEMA, "items": list(items)})

        def picked(output: str) -> bool:
            # Whether next_task.py reads the list, as the step would publish it.
            with tempfile.TemporaryDirectory() as folder:
                path = Path(folder) / "tasks.json"
                path.write_text(output)
                try:
                    next_task.load_tasks(str(path))
                except next_task.Failure:
                    return False
                return True

        # A statement still to write may have no Lean declaration yet; a proof (below) may not.
        good = listing(task, {**task, "article_id": "af_" + "1" * 24, "node_id": "Algebra/u", "phase": "statement",
                              "state": "can_state", "lean_targets": []})
        root, result, _, _ = self.run_task_step(good)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(picked((root / "build" / "tasks.json").read_text()))
        broken = [{}, {**task, "node_id": None}, {**task, "node_id": " "}, {**task, "article_id": "af_" + "0" * 23},
                  {**task, "article_id": "af_" + "0" * 24 + "\n"}, {**task, "phase": None},
                  {**task, "ready": False, "state": "proved"}, {**task, "phase": "statement"},
                  {**task, "lean_targets": None}, {**task, "lean_targets": [{"declaration": 1}]},
                  {**task, "lean_targets": [{"declaration": ""}]}, {**task, "lean_targets": []}]
        # next_task.py refuses the tasks the step refuses (below).
        for bad in broken:
            self.assertFalse(picked(listing(bad)), bad)
        # A refusal, no output, two objects, another format, no items, an empty list (the checkout holds thousands
        # of ready tasks, so none means the list is wrong), a task without what next_task.py reads, and a node or an
        # article id twice.
        for output, status in (("", 2), ("", 0), (good + "\n" + good, 0),
                               (json.dumps({"schema": "autoform-work/v3", "items": [task]}), 0),
                               (json.dumps({"schema": next_task.SCHEMA}), 0), (listing(), 0),
                               *((listing(bad), 0) for bad in broken),
                               (listing(task, {**task, "node_id": "A/u"}), 0),
                               (listing(task, {**task, "article_id": "af_" + "1" * 24}), 0)):
            root, result, _, _ = self.run_task_step(output, status)
            self.assertNotEqual(result.returncode, 0, output)
            for path in ("build/tasks.json", "site-src/tasks.json"):
                self.assertFalse((root / path).exists(), (output, path))

    def test_the_cards_cannot_hold_back_the_site(self):
        # The card check has its own job after the wiki job; the wiki job and deployment never wait for it.
        jobs = self.workflow["jobs"]
        cards = jobs["cards"]
        self.assertEqual(cards["name"], "check the cards")
        self.assertEqual(cards["needs"], "wiki")
        self.assertEqual(jobs["deploy"]["needs"], "wiki")
        self.assertNotIn("permissions", cards)
        self.assertNotIn("continue-on-error", cards)
        # The card tests do not run in the wiki job. It checks the move ledger the site serves and derives the card
        # data its site shows in two steps, after lean-facts and before render, each of which can neither fail the
        # job nor hold it past its timeout.
        self.assertFalse(any("test_cards" in step.get("run", "") for step in self.steps))
        moves, derive = "Check the move ledger the site serves", "Derive the card data the site shows"
        self.assertEqual([step["name"] for step in self.steps if "cards.py" in step.get("run", "")], [moves, derive])
        wiki_names = [step.get("name") for step in self.steps]
        for name in (moves, derive):
            self.assertEqual(self.step(name)["continue-on-error"], "true")
            self.assertLessEqual(int(self.step(name)["timeout-minutes"]), 15)
            self.assertLess(wiki_names.index("Add the Lean-owned facts to the articles"), wiki_names.index(name))
            self.assertLess(wiki_names.index(name), wiki_names.index("Render the blueprint"))
        # The ledger check, independent of the strict card check, removes any earlier receipt before it runs.
        check_moves = self.step(moves)["run"]
        self.assertLess(check_moves.index("rm -f build/card-moves.json"),
                        check_moves.index("python scripts/cards.py moves build/card-moves.json"))
        self.assertIn('uv run --no-project --with "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}"', check_moves)
        checkout = next(step for step in cards["steps"] if step.get("name") == "Check out project")
        self.assertEqual(checkout["with"]["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["with"]["sparse-checkout"])
        steps = {step.get("name"): step for step in cards["steps"]}
        self.assertEqual(steps["Fetch the v2 extraction"]["with"]["name"], "blueprint-dependencies")
        names = list(steps)
        self.assertLess(names.index("Add the Lean-owned facts to the articles"),
                        names.index("Check the cards and derive their edges"))
        self.assertIn("python -m unittest scripts.test_cards", steps["Test the card scripts"]["run"])
        self.assertLess(names.index("Test the card scripts"), names.index("Check the cards and derive their edges"))
        check = steps["Check the cards and derive their edges"]["run"]
        self.assertIn("scripts/cards.py rollup build/cards.json", check)
        self.assertIn("--dependencies build/lean-dependencies.json", check)
        # The check renders card pages as the site does: with the site build's exact Markdown pins. So does the wiki
        # job's step that derives the card data its site shows.
        site = next(step["run"] for job in jobs.values() for step in job.get("steps", [])
                    if step.get("name") == "Build the Markdown site")
        for package in ("markdown", "pymdown-extensions"):
            pin = re.search(rf"--with ({re.escape(package)}==[^\s]+)", site).group(1)
            for run in (steps["Test the card scripts"]["run"], check, self.step(derive)["run"]):
                self.assertIn(f"--with {pin}", run)
        # The site's card data comes from the same inputs as the strict check: its command, without the moves since
        # the base commit, which only the card job checks.
        def command(script: str) -> list[str]:
            return [word for word in shlex.split(script[script.index("uv run"):].replace("\\\n", " "))
                    if word != "${base[@]}"]

        self.assertEqual(command(self.step(derive)["run"]), command(check))
        # The ledger the base commit published must stay a prefix on a PR (the workflow runs in no merge group).
        ledger = steps["Read the move ledger and annotations the base commit published"]
        self.assertIn("github.event.pull_request.base.sha", ledger["env"]["BASE"])
        self.assertNotIn("merge_group", ledger["env"]["BASE"])
        self.assertIn('git show "$BASE:scripts/card-moves.jsonl"', ledger["run"])
        self.assertIn('git archive "$BASE" blueprint/links', ledger["run"])
        self.assertIn('echo "BASE_LINKS=build/base/blueprint/links"', ledger["run"])
        self.assertIn('diff --name-status -M "$BASE" HEAD -- blueprint/roadmap', ledger["run"])
        self.assertIn('echo "BASE_RENAMES=build/base-renames.tsv"', ledger["run"])
        self.assertIn('base=(--base-ledger "$BASE_LEDGER" --base-links "$BASE_LINKS" --renames "$BASE_RENAMES")', check)
        self.assertIn('"${base[@]}"', check)
        self.assertLess(names.index("Read the move ledger and annotations the base commit published"),
                        names.index("Check the cards and derive their edges"))
        # Only the upload may fail without failing the check.
        self.assertEqual([name for name, step in steps.items() if "continue-on-error" in step], ["Keep the card data"])
        self.assertEqual(steps["Keep the card data"]["with"]["name"], "cards")
        self.assertEqual(steps["Keep the card data"]["if"], "always()")

    def test_mathlib_credited_pages_get_their_edges_from_the_same_dump(self):
        # The credited Mathlib names are listed before the dump, which records their uses; the extraction writes the
        # registry beside the unchanged v2 extraction, and lean-facts reads it in both jobs that run it.
        names = [step.get("name") for step in self.steps]
        listing = "List the Mathlib declarations the wiki credits"
        self.assertIn("scripts/sync_wiki.py mathlib-names build/mathlib-names.txt", self.step(listing)["run"])
        self.assertLess(names.index(listing), names.index("Dump declaration dependencies"))
        dump = " ".join(self.step("Dump declaration dependencies")["run"].replace("\\\n", " ").split())
        self.assertIn("dump_v2_dependencies.lean v2-modules.txt build/mathlib-names.txt > v2-dependencies.jsonl", dump)
        self.assertIn("--registry build/mathlib-registry.json --names build/mathlib-names.txt",
                      self.step("Collapse dependencies onto the wiki articles")["run"])
        facts = "lean-facts build/lean-dependencies.json --registry build/mathlib-registry.json"
        self.assertIn(facts, self.step("Add the Lean-owned facts to the articles")["run"])
        self.assertIn("build/mathlib-registry.json", self.step("Keep dependency diagnostics")["with"]["path"])
        cards = {step.get("name"): step for step in self.workflow["jobs"]["cards"]["steps"]}
        self.assertIn(facts, cards["Add the Lean-owned facts to the articles"]["run"])
        self.assertIn("--registry build/mathlib-registry.json", cards["Check the cards and derive their edges"]["run"])
        # The card data the site shows comes from the same registry, so a Mathlib-credited main shows its edges.
        names = [step.get("name") for step in self.steps]
        derive = "Derive the card data the site shows"
        self.assertIn("--registry build/mathlib-registry.json", self.step(derive)["run"])
        self.assertLess(names.index("Collapse dependencies onto the wiki articles"), names.index(derive))

    def test_every_build_keeps_its_site_and_only_main_keeps_the_full_site(self):
        # The built site is a one-day artifact of every successful build, which the Mathlib pages job reads; only
        # main keeps the site with its Mathlib pages, and neither is a Pages upload.
        keep = self.step("Keep the built site")
        self.assertEqual(keep["if"], "success()")
        self.assertEqual((keep["with"]["name"], keep["with"]["retention-days"]), ("blueprint-site", "1"))
        steps = {step.get("name"): step for step in self.workflow["jobs"]["mathlib-pages"]["steps"]}
        full = steps["Keep the site with its Mathlib pages"]
        self.assertIn("actions/upload-artifact@", full["uses"])
        self.assertEqual((full["with"]["name"], full["with"]["path"]), ("blueprint-site-full", "site-full"))
        for clause in ("github.ref == 'refs/heads/main'",
                       "github.event_name != 'pull_request'",
                       "github.event_name != 'merge_group'"):
            self.assertIn(clause, full["if"])
        self.assertNotIn("BLUEPRINT_PAGES", full["if"])
        self.assertNotIn("push", full["if"])

    def test_the_mathlib_pages_cannot_hold_back_the_site(self):
        # The pages have their own read-only job after the wiki and the Mathlib layer; deployment waits for the
        # wiki job alone, and the wiki job never runs the pages script.
        jobs = self.workflow["jobs"]
        pages = jobs["mathlib-pages"]
        self.assertEqual(pages["needs"], ["wiki", "mathlib"])
        self.assertDeploysWhateverTheMathlibJobsDo()
        for key in ("permissions", "continue-on-error", "if"):
            self.assertNotIn(key, pages)
        self.assertFalse(any("build_mathlib_pages" in step.get("run", "") for step in self.steps))
        steps = {step.get("name"): step for step in pages["steps"]}
        checkout = steps["Check out project"]["with"]
        self.assertEqual(checkout["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["sparse-checkout"])
        self.assertIn("!/Atlas/", checkout["sparse-checkout"])
        fetched = {(s["with"]["name"], s["with"]["path"]) for s in pages["steps"] if "download-artifact@" in s.get("uses", "")}
        self.assertEqual(fetched, {("blueprint-site", "site"), ("mathlib-graph", "mathlib-graph")})
        self.assertIn("python -m unittest scripts.test_build_mathlib_pages", steps["Test the Mathlib pages script"]["run"])
        self.assertIn("scripts/test_build_mathlib_pages.py", self.workflow["on"]["pull_request"]["paths"])
        build = steps["Build the Mathlib pages"]["run"]
        self.assertIn("build_mathlib_pages.py build", build)
        self.assertIn("github.event_name == 'pull_request' && '--strict-links' || ''", build)
        self.assertIn("build_mathlib_pages.py check site mathlib-graph site-full", steps["Check the site with its Mathlib pages"]["run"])
        for step in pages["steps"]:
            self.assertNotIn("continue-on-error", step)
            self.assertFalse(step.get("uses", "").startswith("actions/deploy-pages@"))
        # The full site, packed for GitHub Pages, goes up as a second Pages artifact, under the same conditions as the
        # wiki job's, after the check that it gives back every file of the full site and of its size. The full site is
        # kept as it is before it is packed.
        self.assertIn("python -m unittest scripts.test_pack_pages_site", steps["Test the Pages packing script"]["run"])
        self.assertIn("scripts/test_pack_pages_site.py", self.workflow["on"]["pull_request"]["paths"])
        for path in ("scripts/pack_pages_site.py", "scripts/pages_packing.js", "scripts/pages_size.sh"):
            self.assertIn(path, self.workflow["on"]["pull_request"]["paths"])
        self.assertEqual(steps["Pack the full site for GitHub Pages"]["run"],
                         "python scripts/pack_pages_site.py pack site-full site-pages")
        checked = steps["Check the packed site"]["run"]
        self.assertIn("python scripts/pack_pages_site.py check site-full site-pages", checked)
        self.assertIn("bash scripts/pages_size.sh site-pages 950000000", checked)
        upload = steps["Upload the packed site"]
        self.assertIn("actions/upload-pages-artifact@", upload["uses"])
        self.assertEqual((upload["with"]["name"], upload["with"]["path"]), ("github-pages-full", "site-pages"))
        self.assertEqual(upload["if"], self.step("Upload Pages artifact")["if"])
        names = [step["name"] for step in pages["steps"]]
        for earlier, later in (("Check the site with its Mathlib pages", "Keep the site with its Mathlib pages"),
                               ("Keep the site with its Mathlib pages", "Pack the full site for GitHub Pages"),
                               ("Pack the full site for GitHub Pages", "Check the packed site"),
                               ("Check the packed site", "Upload the packed site")):
            self.assertLess(names.index(earlier), names.index(later))
        for step in pages["steps"]:
            if "pack_pages_site" in step.get("run", "") and "unittest" not in step["run"]:
                self.assertNotIn("if", step)

    def assertDeploysWhateverTheMathlibJobsDo(self):
        # Deployment waits for the wiki job alone and publishes its site. Only after it, and only if the Mathlib pages
        # job succeeded, a second job publishes that job's packed full site in its place.
        jobs = self.workflow["jobs"]
        deploy, promote = jobs["deploy"], jobs["promote"]
        self.assertEqual(deploy["needs"], "wiki")
        self.assertNotIn("mathlib", deploy["if"])
        self.assertNotIn("with", next(step for step in deploy["steps"] if step["name"] == "Deploy"))
        self.assertNotIn("name", self.step("Upload Pages artifact").get("with", {}))
        self.assertEqual(promote["name"], "publish the full site")
        self.assertEqual(promote["needs"], ["deploy", "mathlib-pages"])
        for function in ("always()", "!cancelled()", "failure()"):
            self.assertNotIn(function, promote["if"])
        self.assertEqual(promote["if"], deploy["if"])
        steps = {step["name"]: step for step in promote["steps"]}
        self.assertEqual(steps["Deploy"]["with"], {"artifact_name": "github-pages-full"})
        self.assertNotIn("cancel-in-progress", str(self.workflow["concurrency"]["group"]))
        self.assertEqual(self.workflow["concurrency"]["cancel-in-progress"], "${{ github.ref != 'refs/heads/main' }}")


class GraphSyncWorkflowTests(unittest.TestCase):
    """The scoped declarations check (docs/BLUEPRINT.md, Maintaining articles) runs on every pull request and merge
    group, reads the Lean sources only, and reports without failing its job."""

    @classmethod
    def setUpClass(cls):
        cls.text = GRAPH_SYNC.read_text()
        cls.workflow = yaml.load(cls.text, Loader=yaml.BaseLoader)
        cls.job = cls.workflow["jobs"]["check"]
        cls.steps = {step.get("name"): step for step in cls.job["steps"]}

    def test_every_pull_request_and_merge_group_runs_it(self):
        # No filter skips a pull request, Lean-only ones included, and nothing skips the job: the merge queue could
        # require it one day (scripts/test_merge_queue_checks.py holds required checks to this).
        events = self.workflow["on"]
        self.assertEqual(set(events), {"pull_request", "merge_group", "workflow_dispatch"})
        self.assertEqual(events["pull_request"], "")
        self.assertEqual(events["merge_group"], {"types": ["checks_requested"]})
        for key in ("if", "needs", "strategy", "continue-on-error"):
            self.assertNotIn(key, self.job)
        self.assertIn("github.ref", self.workflow["concurrency"]["group"])
        # Its check's name is its own: another job of that name could stand in for it.
        names = [job.get("name", key) for path in sorted(GRAPH_SYNC.parent.glob("*.y*ml"))
                 for key, job in yaml.load(path.read_text(), Loader=yaml.BaseLoader)["jobs"].items()]
        self.assertEqual(names.count("graph sync"), 1)
        self.assertEqual(self.job["name"], "graph sync")

    def test_the_check_only_reports_and_keeps_its_report(self):
        step = self.steps["Check that the graph is in step with the Lean"]
        self.assertEqual(step["continue-on-error"], "true")
        self.assertIn('python scripts/sync_wiki.py declarations --base "$BASE" --check', step["run"])
        self.assertIn("--report build/graph-sync.json", step["run"])
        self.assertIn('exit "$status"', step["run"])
        keep = self.steps["Keep the report"]
        self.assertEqual((keep["if"], keep["continue-on-error"], keep["with"]["name"]), ("always()", "true", "graph-sync"))
        # No Lean is built or fetched: the check reads the sources as the declarations sync does.
        self.assertNotIn("lake", self.text)
        self.assertNotIn("elan", self.text)

    def test_it_reads_autoform_and_the_markdown_as_the_wiki_build_does(self):
        wiki = yaml.load(WORKFLOW.read_text(), Loader=yaml.BaseLoader)
        pins = {step["name"]: step for step in wiki["jobs"]["wiki"]["steps"]}
        self.assertEqual(self.steps["Read the reviewed Autoform pin"]["run"], pins["Read the reviewed Autoform pin"]["run"])
        self.assertEqual(self.steps["Install uv"]["with"], pins["Install uv"]["with"])
        self.assertEqual(self.workflow["env"]["AUTOFORM_SOURCE"], wiki["env"]["AUTOFORM_SOURCE"])
        check = self.steps["Check that the graph is in step with the Lean"]["run"]
        self.assertIn('--with "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}"', check)
        for pin in re.findall(r"--with ([\w.-]+==[^\s]+)", pins["Build the Markdown site"]["run"]):
            self.assertIn(f"--with {pin}", check)

    def test_it_holds_no_write_token_or_credentials(self):
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertNotIn("permissions", self.job)
        self.assertEqual(self.steps["Check out project"]["with"]["persist-credentials"], "false")
        self.assertNotIn("secrets.", self.text)
        for step in self.job["steps"]:
            if "uses" in step:
                self.assertRegex(step["uses"], r"@[0-9a-f]{40}\Z")

    def run_check(self, status: int, report: str | None = None, extra: str = "", fix_fetch: str = "refs/heads/main"):
        """Run the check's step with a uv that prints a verdict, writes *report* as the check's JSON report, if any,
        and exits with *status*; returns the result, the job summary and the arguments uv got."""
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        (root / "bin").mkdir()
        if report is not None:
            (root / "report.json").write_text(report)
        (root / "bin" / "uv").write_text(f'#!/bin/sh\necho "$@" > uv-arguments\necho "In step: no"\necho "error: a link" >&2\n'
                                        'printf "%s" "${UV_EXTRA:-}"\n'
                                        f'[ -f report.json ] && cp report.json build/graph-sync.json\nexit {status}\n')
        (root / "bin" / "uv").chmod(0o755)
        summary = root / "summary.md"
        result = subprocess.run(
            ["bash", "-c", self.steps["Check that the graph is in step with the Lean"]["run"]], cwd=root, text=True,
            capture_output=True, env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}", "BASE": "b" * 40,
                                      "AUTOFORM_SOURCE": "https://example.invalid/autoform.git", "AUTOFORM_REF": "a" * 40,
                                      "GITHUB_STEP_SUMMARY": str(summary), "UV_EXTRA": extra, "FIX_FETCH": fix_fetch})
        return result, summary.read_text(), (root / "uv-arguments").read_text().split()

    def test_the_check_output_can_neither_issue_a_command_nor_end_the_summary_block(self):
        # A file name holding a workflow command or a code fence, as the check prints it.
        result, summary, _ = self.run_check(0, extra="::error::forged\n```\n# Heading")
        lines = result.stdout.splitlines()
        start = next(number for number, line in enumerate(lines) if line.startswith("::stop-commands::"))
        token = lines[start].removeprefix("::stop-commands::")
        self.assertTrue(token.startswith("graph-sync-") and len(token) > len("graph-sync-") + 16, token)
        end = lines.index(f"::{token}::")
        self.assertTrue(start < lines.index("::error::forged") < end)
        self.assertTrue(all(line.startswith("    ") or not line.strip() or line.startswith(("###", "The check"))
                            for line in summary.splitlines()), summary)
        self.assertIn("    ```\n    # Heading", summary)
        # Lines a carriage return ends, and output with no last line end: every line of the summary stays indented,
        # and the log's resume marker stands on a line of its own.
        result, summary, _ = self.run_check(0, extra="one\r# two\r\n```three")
        self.assertTrue(summary.endswith("    one\n    # two\n    ```three\n"), summary)
        self.assertNotIn("\r", summary)
        self.assertTrue(any(line.startswith("::graph-sync-") for line in result.stdout.split("\n")), result.stdout)

    def test_the_verdict_goes_to_the_log_and_the_summary_with_the_branchs_command(self):
        if shutil.which("jq") is None:
            self.skipTest("jq is not installed")
        result, summary, arguments = self.run_check(1, '{"in_step": false}')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(arguments[arguments.index("python"):], ["python", "scripts/sync_wiki.py", "declarations", "--base",
                                                                "b" * 40, "--check", "--report", "build/graph-sync.json"])
        self.assertIn("In step: no\nerror: a link\n", result.stdout)
        self.assertIn("::warning title=Graph sync::", result.stdout)
        self.assertIn("    In step: no\n    error: a link\n", summary)
        self.assertIn('git fetch https://github.com/facebookresearch/atlas-lean.git refs/heads/main\n'
                      'python3 scripts/sync_wiki.py declarations --base "$(git merge-base FETCH_HEAD HEAD)"\n', summary)
        # A run dispatched with a base names it.
        result, summary, _ = self.run_check(1, '{"in_step": false}', fix_fetch="")
        self.assertIn(f"git fetch https://github.com/facebookresearch/atlas-lean.git {'b' * 40}\n"
                      f"python3 scripts/sync_wiki.py declarations --base {'b' * 40}\n", summary)
        result, summary, _ = self.run_check(0)
        self.assertEqual(result.returncode, 0)
        self.assertNotIn("::warning", result.stdout)
        self.assertNotIn("merge-base", summary)
        # A check that could not run, by its exit code or with no report that says the pull request is not in step,
        # as when Python fails, says so rather than that the pull request is not in step.
        for status, report in ((2, None), (1, None), (1, '{"in_step": true}'), (1, "not json")):
            result, summary, _ = self.run_check(status, report)
            self.assertEqual(result.returncode, status)
            self.assertIn("::warning title=Graph sync::The check could not run", result.stdout)
            self.assertIn(f"The check could not run (exit {status})", summary)
            self.assertNotIn("merge-base", summary)

    def find_base(self, event: str, env=lambda main, merge: {}):
        """Run the step that finds the base in a repository whose HEAD merges a branch into main, as a pull request's
        merge commit does, with the environment *env* gives for the main and merge commits; returns the result, what
        the step wrote to GITHUB_ENV, and those commits."""
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        git = lambda *args: subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@t", *args],
                                           check=True, capture_output=True, text=True).stdout.strip()
        git("init", "-q", "-b", "main")
        git("commit", "-q", "--allow-empty", "-m", "first")
        git("switch", "-q", "-c", "topic")
        git("commit", "-q", "--allow-empty", "-m", "topic")
        git("switch", "-q", "main")
        git("commit", "-q", "--allow-empty", "-m", "second")
        main = git("rev-parse", "HEAD")
        git("merge", "-q", "--no-ff", "-m", "merge", "topic")
        merge = git("rev-parse", "HEAD")
        output = root / "env"
        result = subprocess.run(["bash", "-c", self.steps["Find the base commit"]["run"]], cwd=root, text=True,
                                capture_output=True,
                                env={**os.environ, "EVENT": event, "GITHUB_ENV": str(output), **env(main, merge)})
        return result, output.read_text() if output.exists() else "", main, merge

    def test_a_pull_request_compares_with_its_base_and_a_merge_group_with_the_queues(self):
        env = self.steps["Find the base commit"]["env"]
        self.assertEqual(env["MERGE_GROUP_BASE"], "${{ github.event.merge_group.base_sha }}")
        self.assertEqual(env["DISPATCH_BASE"], "${{ inputs.base }}")
        self.assertEqual(env["PR_BASE_REF"], "${{ github.event.pull_request.base.ref }}")
        self.assertEqual(env["MERGE_GROUP_REF"], "${{ github.event.merge_group.base_ref }}")
        self.assertEqual(self.steps["Check out project"]["with"]["fetch-depth"], "2")
        result, written, main, merge = self.find_base("pull_request", lambda main, merge: {"PR_BASE_REF": "release/1.x"})
        self.assertEqual((result.returncode, written), (0, f"BASE={main}\nFIX_FETCH=refs/heads/release/1.x\n"),
                         result.stderr)
        # A branch name the fix command could not give plainly: it fetches the base commit instead.
        result, written, main, merge = self.find_base("pull_request", lambda main, merge: {"PR_BASE_REF": "a b;c"})
        self.assertEqual((result.returncode, written), (0, f"BASE={main}\nFIX_FETCH={main}\n"), result.stderr)
        # The queue's base, here the merge commit itself, which the checkout already has.
        result, written, main, merge = self.find_base("merge_group", lambda main, merge: {
            "MERGE_GROUP_BASE": merge, "MERGE_GROUP_REF": "refs/heads/main"})
        self.assertEqual((result.returncode, written), (0, f"BASE={merge}\nFIX_FETCH=refs/heads/main\n"),
                         result.stderr)
        # A run dispatched with a base fetches nothing to find one: the command names it.
        result, written, main, merge = self.find_base("workflow_dispatch", lambda main, merge: {"DISPATCH_BASE": main})
        self.assertEqual((result.returncode, written), (0, f"BASE={main}\nFIX_FETCH=\n"), result.stderr)
        # A run with no commit to compare with fails rather than checking against nothing.
        result, written, _, _ = self.find_base("workflow_dispatch", lambda main, merge: {"DISPATCH_BASE": "main"})
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(written, "")


if __name__ == "__main__":
    unittest.main()
