#!/usr/bin/env python3
"""Security/correctness regressions for the upstream blueprint workflow."""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

from scripts import next_task

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
        # The reader of the list the job writes: changing it runs the tests that hold the two to one format.
        self.assertIn("scripts/next_task.py", paths)
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


if __name__ == "__main__":
    unittest.main()
