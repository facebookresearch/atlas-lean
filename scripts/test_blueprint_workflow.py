#!/usr/bin/env python3
"""Security/correctness regressions for the upstream blueprint workflow."""

from __future__ import annotations

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
            "push", "pull_request", "merge_group", "workflow_dispatch",
        })
        self.assertEqual(events["push"]["branches"], ["main"])
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
                         "lake build MathlibExt CSLibExt PhyslibExt WantedExt")
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
        self.assertTrue(all("uses" in step for step in deploy["steps"]))

    def test_built_site_is_kept_only_for_main_builds(self):
        condition = self.step("Keep the built site")["if"]
        for clause in ("github.ref == 'refs/heads/main'",
                       "github.event_name != 'pull_request'",
                       "github.event_name != 'merge_group'"):
            self.assertIn(clause, condition)
        self.assertNotIn("BLUEPRINT_PAGES", condition)


if __name__ == "__main__":
    unittest.main()
