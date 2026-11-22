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

ROOT = Path(__file__).resolve().parent.parent
# The card files: their tests run in the card job (scripts/test_cards.py), not in the wiki job.
CARD_INPUTS = ("scripts/cards.py", "scripts/card-moves.jsonl", "scripts/test_cards.py", "docs/cards.md")
WORKFLOW = ROOT / ".github" / "workflows" / "blueprint-pages.yml"


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
            "scripts/requirements-blueprint.txt", "mkdocs.yml", "theme/**", "hooks/**",
            "docs/BLUEPRINT.md", ".github/workflows/blueprint-pages.yml", ".github/autoform-ref",
            "lean-toolchain", "lake-manifest.json", "lakefile.toml",
        ):
            self.assertIn(path, paths)
        # Every test module the job runs is in the filter, so changing a test runs it.
        tests = self.step("Test the wiki scripts")["run"]
        for module in re.findall(r"scripts\.(test_\w+)", tests):
            self.assertIn(f"scripts/{module}.py", paths)
        # A path that no longer exists would silently stop triggering the check. The sync baseline
        # scripts/wiki-sync.json arrives with the wiki's last page batch, so it may not exist yet. The card
        # inputs are checked by the card tests, in their own job, so that no card file can fail this one.
        for path in paths:
            if path == "scripts/wiki-sync.json" or path in CARD_INPUTS:
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

    def test_the_build_cache_is_restored_from_ci_and_never_saved(self):
        restore = self.step("Restore local build")
        self.assertIn("actions/cache/restore@", restore["uses"])
        self.assertIn("lake-build-", restore["with"]["restore-keys"])
        for job in self.workflow["jobs"].values():
            for step in job["steps"]:
                uses = step.get("uses", "")
                self.assertFalse(uses.startswith(("actions/cache@", "actions/cache/save@")), uses)

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
        # The layer has its own job and check after the wiki job, and deployment waits for the wiki job alone.
        jobs = self.workflow["jobs"]
        mathlib = jobs["mathlib"]
        self.assertEqual(mathlib["needs"], "wiki")
        self.assertDeploysWhateverTheMathlibJobsDo()
        self.assertNotIn("permissions", mathlib)
        self.assertNotIn("continue-on-error", mathlib)
        checkout = next(step for step in mathlib["steps"] if step.get("name") == "Check out project")
        self.assertEqual(checkout["with"]["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["with"]["sparse-checkout"])
        self.assertIn("!/Atlas/", checkout["with"]["sparse-checkout"])
        # In the wiki job only the dump of the v2 declarations, which needs the ATLAS build. It comes after every
        # step the site needs, cannot fail the job, and has a timeout, so a hang cannot hold the job until its own
        # timeout either; its upload cannot fail the job. A missing dump fails the layer's job instead.
        dump = "Dump the v2 declarations with their Mathlib uses"
        wiki_steps = [step["name"] for step in self.steps if "extract_mathlib_graph.py" in step.get("run", "")]
        self.assertEqual(wiki_steps, [dump])
        self.assertEqual(self.step(dump)["continue-on-error"], "true")
        self.assertLessEqual(int(self.step(dump)["timeout-minutes"]), 30)
        self.assertIn("--jobs 1 --shards 1", self.step(dump)["run"])
        names = [step.get("name") for step in self.steps]
        upload = "Keep the v2 declarations with their Mathlib uses"
        self.assertEqual(names[-2:], [dump, upload])
        for site_step in ("Check routes, anchors, and article cards", "Keep dependency diagnostics",
                          "Keep the built site", "Upload Pages artifact"):
            self.assertLess(names.index(site_step), names.index(dump), site_step)
        self.assertEqual(self.step(upload)["continue-on-error"], "true")
        self.assertEqual(self.step(upload)["with"]["name"], "v2-mathlib-dump")
        self.assertNotIn("mathlib-graph", self.step("Keep dependency diagnostics")["with"]["path"])
        steps = {step.get("name"): step for step in mathlib["steps"]}
        self.assertEqual(steps["Fetch the v2 extraction"]["with"]["name"], "blueprint-dependencies")
        fetch = steps["Fetch the v2 declarations with their Mathlib uses"]["with"]
        self.assertEqual((fetch["name"], fetch["path"]), ("v2-mathlib-dump", "mathlib-graph"))
        extract = steps["Extract the Mathlib layer"]["run"]
        self.assertIn("set -euo pipefail", extract)
        self.assertIn("test -s mathlib-graph/v2-mathlib-dump.jsonl.gz", extract)
        self.assertIn("--check-v2 build/lean-dependencies.json", extract)
        self.assertIn("join --strict", extract)
        for command in ("dump", "graph", "bridge", "stats"):
            self.assertTrue(any(f"extract_mathlib_graph.py {command}" in step.get("run", "")
                                for step in mathlib["steps"]), command)
        # Only the upload may fail without failing the layer's check.
        self.assertEqual([name for name, step in steps.items() if "continue-on-error" in step],
                         ["Keep the Mathlib layer"])
        self.assertEqual(steps["Keep the Mathlib layer"]["with"]["name"], "mathlib-graph")
        self.assertEqual(steps["Keep the Mathlib layer"]["if"], "always()")

    def test_the_cards_cannot_hold_back_the_site(self):
        # The card check has its own job after the wiki job; the wiki job and deployment never wait for it.
        jobs = self.workflow["jobs"]
        cards = jobs["cards"]
        self.assertEqual(cards["name"], "check the cards")
        self.assertEqual(cards["needs"], "wiki")
        self.assertEqual(jobs["deploy"]["needs"], "wiki")
        self.assertNotIn("permissions", cards)
        self.assertNotIn("continue-on-error", cards)
        # The card tests do not run in the wiki job. It derives the card data its site shows in one step, after
        # lean-facts and before render, which can neither fail the job nor hold it past its timeout.
        self.assertFalse(any("test_cards" in step.get("run", "") for step in self.steps))
        derive = "Derive the card data the site shows"
        self.assertEqual([step["name"] for step in self.steps if "cards.py" in step.get("run", "")], [derive])
        self.assertEqual(self.step(derive)["continue-on-error"], "true")
        self.assertLessEqual(int(self.step(derive)["timeout-minutes"]), 15)
        wiki_names = [step.get("name") for step in self.steps]
        self.assertLess(wiki_names.index("Add the Lean-owned facts to the articles"), wiki_names.index(derive))
        self.assertLess(wiki_names.index(derive), wiki_names.index("Render the blueprint"))
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


if __name__ == "__main__":
    unittest.main()
