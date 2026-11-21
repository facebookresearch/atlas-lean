#!/usr/bin/env python3
"""Security/correctness regressions for the upstream blueprint workflow."""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
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

    def test_pull_requests_run_the_check_on_wiki_paths_and_merge_groups_always(self):
        events = self.workflow["on"]
        self.assertEqual(set(events), {
            "schedule", "pull_request", "merge_group", "workflow_dispatch",
        })
        # main is built once a day at 03:17 UTC (GitHub reads cron in UTC), not on every push.
        self.assertEqual(events["schedule"], [{"cron": "17 3 * * *"}])
        paths = events["pull_request"]["paths"]
        for path in (
            "blueprint/**", "scripts/generate_wiki.py", "scripts/sync_wiki.py",
            "scripts/extract_v2_lean_dependencies.py", "scripts/dump_v2_dependencies.lean",
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
        # scripts/wiki-sync.json arrives with the wiki's last page batch, so it may not exist yet.
        for path in paths:
            if path == "scripts/wiki-sync.json":
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

    def test_dump_refuses_missing_compiled_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
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
        conditions = [deploy["if"], promote["if"], self.step("Upload Pages artifact")["if"]]
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
        # GitHub Pages publishes at most 1 GB: the artifact is measured as its upload packs it, before the upload.
        names = [step.get("name") for step in self.steps]
        size = self.step("Check the size of the Pages artifact")
        self.assertEqual(size["run"], "bash scripts/pages_size.sh site 950000000")
        self.assertEqual(size["if"], self.step("Upload Pages artifact")["if"])
        self.assertEqual(names.index("Check the size of the Pages artifact") + 1, names.index("Upload Pages artifact"))

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
        # Its share of the Mathlib pages goes up as a second Pages artifact, under the same conditions as the wiki
        # job's, after the check of its size and links.
        selection = steps["Build the Pages site with the Mathlib pages that fit"]["run"]
        self.assertIn("build_mathlib_pages.py build --budget 900000000", selection)
        checked = steps["Check the Pages site"]["run"]
        self.assertIn("build_mathlib_pages.py check site mathlib-graph site-pages", checked)
        self.assertIn("bash scripts/pages_size.sh site-pages 950000000", checked)
        upload = steps["Upload the Pages site with Mathlib pages"]
        self.assertIn("actions/upload-pages-artifact@", upload["uses"])
        self.assertEqual((upload["with"]["name"], upload["with"]["path"]), ("github-pages-mathlib", "site-pages"))
        self.assertEqual(upload["if"], self.step("Upload Pages artifact")["if"])
        names = [step["name"] for step in pages["steps"]]
        self.assertLess(names.index("Check the Pages site"), names.index("Upload the Pages site with Mathlib pages"))

    def assertDeploysWhateverTheMathlibJobsDo(self):
        # Deployment waits for the wiki job alone and publishes its site. Only after it, and only if the Mathlib pages
        # job succeeded, a second job publishes that job's site in its place.
        jobs = self.workflow["jobs"]
        deploy, promote = jobs["deploy"], jobs["promote"]
        self.assertEqual(deploy["needs"], "wiki")
        self.assertNotIn("mathlib", deploy["if"])
        self.assertNotIn("with", next(step for step in deploy["steps"] if step["name"] == "Deploy"))
        self.assertNotIn("name", self.step("Upload Pages artifact").get("with", {}))
        self.assertEqual(promote["needs"], ["deploy", "mathlib-pages"])
        for function in ("always()", "!cancelled()", "failure()"):
            self.assertNotIn(function, promote["if"])
        self.assertEqual(promote["if"], deploy["if"])
        steps = {step["name"]: step for step in promote["steps"]}
        self.assertEqual(steps["Deploy"]["with"], {"artifact_name": "github-pages-mathlib"})
        self.assertNotIn("cancel-in-progress", str(self.workflow["concurrency"]["group"]))
        self.assertEqual(self.workflow["concurrency"]["cancel-in-progress"], "${{ github.ref != 'refs/heads/main' }}")


if __name__ == "__main__":
    unittest.main()
