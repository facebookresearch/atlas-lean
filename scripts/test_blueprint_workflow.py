#!/usr/bin/env python3
"""Security/correctness regressions for the upstream blueprint workflow."""

from __future__ import annotations

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
        deploy = self.workflow["jobs"]["deploy"]
        self.assertEqual(deploy["needs"], "wiki")
        self.assertEqual(deploy["permissions"], {
            "pages": "write", "id-token": "write",
        })
        conditions = [deploy["if"], self.step("Upload Pages artifact")["if"]]
        for condition in conditions:
            for clause in ("vars.BLUEPRINT_PAGES == 'true'",
                           "github.ref == 'refs/heads/main'",
                           "github.event_name != 'pull_request'",
                           "github.event_name != 'merge_group'"):
                self.assertIn(clause, condition)
            # Scheduled and manual runs of main publish, so no clause may require a push.
            self.assertNotIn("push", condition)
        self.assertTrue(all("uses" in step for step in deploy["steps"]))

    def test_the_mathlib_layer_cannot_hold_back_the_site(self):
        # The layer has its own job and check after the wiki job, and deployment waits for the wiki job alone.
        jobs = self.workflow["jobs"]
        mathlib = jobs["mathlib"]
        self.assertEqual(mathlib["needs"], "wiki")
        self.assertEqual(jobs["deploy"]["needs"], "wiki")
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
        self.assertEqual(jobs["deploy"]["needs"], "wiki")
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
            self.assertFalse(step.get("uses", "").startswith(("actions/upload-pages-artifact@", "actions/deploy-pages@")))

    def run_size_step(self, deploying, stubs):
        """Run the size step on an empty `site` with the commands in `stubs` (name -> script) ahead
        of the system's; return its result and summary."""
        step = self.step("Check the site against GitHub Pages' size limit")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "bin").mkdir()
            (root / "site").mkdir()
            for name, script in stubs.items():
                command = root / "bin" / name
                command.write_text(script)
                command.chmod(0o755)
            summary = root / "summary.md"
            env = {"PATH": f"{root / 'bin'}:/usr/bin:/bin", "GITHUB_STEP_SUMMARY": str(summary),
                   "DEPLOYING": "true" if deploying else "false"}
            result = subprocess.run(["bash", "-e", "-c", step["run"]], cwd=root, env=env,
                                    text=True, capture_output=True, check=False)
            return result, summary.read_text() if summary.exists() else ""

    def run_size_check(self, size, deploying):
        # `wc` reads the archive and reports `size` bytes.
        result, summary = self.run_size_step(
            deploying, {"wc": f"#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' {size}\n"})
        self.assertIn(f"The built site's Pages archive is {size} bytes ({size // 1000000} MB)", summary)
        return result

    def test_site_size_warns_from_900_mb_and_fails_only_a_publishing_build_over_1_gb(self):
        for size, deploying, code, annotation in (
            (899_999_999, True, 0, None),
            (900_000_000, True, 0, "::warning title=Site near the Pages limit::"),
            (1_000_000_000, True, 0, "::warning title=Site near the Pages limit::"),
            (1_000_000_001, False, 0, "::warning title=Site over the Pages limit::"),
            (1_000_000_001, True, 1, "::error title=Site over the Pages limit::"),
        ):
            with self.subTest(size=size, deploying=deploying):
                result = self.run_size_check(size, deploying)
                self.assertEqual(result.returncode, code, result.stderr)
                if annotation is None:
                    self.assertNotIn("::", result.stdout)
                else:
                    self.assertIn(annotation, result.stdout)
                    self.assertIn(f"archive is {size} bytes", result.stdout)

    def test_site_size_check_fails_when_the_size_cannot_be_measured(self):
        # A failing archive, or a count that is not a number of bytes, fails the step on every
        # build with its own annotation, instead of reporting 0 MB and passing.
        for stubs in ({"tar": "#!/bin/sh\necho 'tar: site: Cannot open' >&2\nexit 2\n"},
                      {"wc": "#!/bin/sh\ncat >/dev/null\necho unknown\n"},
                      {"wc": "#!/bin/sh\ncat >/dev/null\n"}):
            for deploying in (False, True):
                with self.subTest(stubs=stubs, deploying=deploying):
                    result, summary = self.run_size_step(deploying, stubs)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn("::error title=Site size unknown::", result.stdout)
                    self.assertNotIn("Pages archive is", summary)

    def test_site_size_check_measures_the_archive_the_pages_upload_builds(self):
        step = self.step("Check the site against GitHub Pages' size limit")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            site = root / "site"
            (site / "assets").mkdir(parents=True)
            (site / "index.html").write_text("hello")
            (site / "assets" / "page.html").write_text("x" * 3000)
            (root / "outside.txt").write_text("content behind a link")
            (site / "linked.txt").symlink_to(root / "outside.txt")
            (site / ".git").mkdir()
            (site / ".git" / "objects").write_bytes(b"\0" * 4096)
            # A hidden sparse file larger than the limit: the upload leaves it out.
            with open(site / ".hidden", "wb") as hidden:
                hidden.truncate(2_000_000_000)
            # The archive of actions/upload-pages-artifact's Linux "Archive artifact" step.
            archive = subprocess.run(
                ["tar", "--dereference", "--hard-dereference", "--directory", str(site), "-cf", "-",
                 "--exclude=.git", "--exclude=.github", "--exclude=.[^/]*", "."],
                capture_output=True, check=True).stdout
            summary = root / "summary.md"
            env = {"PATH": "/usr/bin:/bin", "GITHUB_STEP_SUMMARY": str(summary), "DEPLOYING": "true"}
            result = subprocess.run(["bash", "-e", "-c", step["run"]], cwd=root, env=env,
                                    text=True, capture_output=True, check=False)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn("::", result.stdout)
            self.assertIn(f"The built site's Pages archive is {len(archive)} bytes", summary.read_text())

    def test_site_size_check_deploys_exactly_when_the_upload_does(self):
        step = self.step("Check the site against GitHub Pages' size limit")
        upload = self.step("Upload Pages artifact")["if"]
        self.assertEqual(step["env"]["DEPLOYING"], "${{ " + upload + " }}")


if __name__ == "__main__":
    unittest.main()
