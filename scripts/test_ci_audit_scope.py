#!/usr/bin/env python3
"""What CI's `build` job audits, and where a missed module still shows up.

Pull requests and merge groups audit only the modules their build rewrote since
the cached build they restore (scripts/audit_rebuilt_modules.py). That is sound
only while main's cache holds builds that passed the audit of their own commit,
so build-cache.yml must promote only the build of the successful merge-group run
of that exact commit. Pushes to main keep the full audit, and a failed main
build is reported in an issue. A merge group also skips the native tests of the
audit tools when the files they read match the restored build's commit, so that
list must name every repository file those tests read.

These tests guard against accidental edits of those workflows. They do not
model GitHub Actions.

Run with: python3 -m unittest discover -s scripts -p test_ci_audit_scope.py
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

from test_merge_queue_checks import block, jobs, value, workflow

ROOT = Path(__file__).resolve().parent.parent
NATIVE_TESTS = ("scripts/test_declaration_collisions_native.py", "scripts/test_compiled_audit_native.py")
LIBRARIES = ("CSLibExt", "CSLibExtTest", "MathlibExt", "MathlibExtTest", "PhyslibExt",
             "PhyslibExtTest", "Domains", "DomainsTest", "WantedExt")


def steps(job: list[str]) -> dict[str, list[str]]:
    """Each named step of a job, by name, with its lines."""
    found: dict[str, list[str]] = {}
    current: list[str] | None = None
    for line in block(job, "steps", 4) or []:
        if line.startswith("      - "):
            current = [line.replace("      - ", "        ", 1)]
            name = value(current, "name", 8).strip("'\"")
            found[name or f"step {len(found)}"] = current
        elif current is not None:
            current.append(line)
    return found


def native_test_inputs() -> set[str]:
    """Every repository file the native tests name or import, with the project
    modules those Lean files import."""
    inputs = set(NATIVE_TESTS)
    for test in NATIVE_TESTS:
        text = (ROOT / test).read_text(encoding="utf-8")
        for module in re.findall(r"^import (\w+)", text, re.M):
            if (ROOT / "scripts" / f"{module}.py").is_file():
                inputs.add(f"scripts/{module}.py")
        # A file named by its path, by its name in scripts/, or as a module.
        for literal in re.findall(r"'([^'\s]+)'", text):
            candidates = [literal, f"scripts/{literal}"]
            if "/" not in literal:
                candidates.append(literal.replace(".", "/") + ".lean")
            inputs.update(path for path in candidates if (ROOT / path).is_file())
    pending = [path for path in inputs if path.endswith(".lean") and path.split("/")[0] in LIBRARIES]
    while pending:
        source = (ROOT / pending.pop()).read_text(encoding="utf-8")
        for module in re.findall(r"^(?:public )?import (?:all )?([\w.]+)", source, re.M):
            path = module.replace(".", "/") + ".lean"
            if path.split("/")[0] in LIBRARIES and (ROOT / path).is_file() and path not in inputs:
                inputs.add(path)
                pending.append(path)
    return inputs


class BuildAuditScope(unittest.TestCase):
    def setUp(self) -> None:
        self.ci = jobs(workflow("ci.yml"))
        self.build = steps(self.ci["build"])

    def test_only_pull_requests_and_merge_groups_scope_the_audit(self):
        record = self.build["Record the restored build for a scoped audit"]
        condition = value(record, "if", 8)
        self.assertIn("github.event_name == 'pull_request'", condition)
        self.assertIn("github.event_name == 'merge_group'", condition)
        self.assertNotIn("push", condition)
        self.assertNotIn("workflow_dispatch", condition)
        setters = [name for name, lines in self.build.items()
                   if any("ATLAS_AUDIT_RESTORED" in line for line in lines)]
        self.assertEqual(setters, ["Record the restored build for a scoped audit"])

    def test_main_takes_only_the_merge_group_build_of_its_commit(self):
        save = jobs(workflow("build-cache.yml"))["save"]
        download = " ".join(steps(save)["Download the merge group's build"])
        for term in ("actions/workflows/ci.yml/runs?", "event=merge_group",
                     "head_sha=${GITHUB_SHA}", "status=success", "actions/runs/${run}/artifacts"):
            self.assertIn(term, download)

    def test_a_failed_main_build_is_reported(self):
        report = self.ci["report"]
        self.assertEqual(value(report, "needs", 4), "build")
        condition = value(report, "if", 4)
        self.assertIn("failure()", condition)
        self.assertIn("github.event_name == 'push'", condition)
        self.assertEqual([line.strip() for line in block(report, "permissions", 4) if line.strip()],
                         ["issues: write"])

    def test_merge_groups_compare_every_input_of_the_native_tests(self):
        compare = self.build["Compare the audit tools with the restored build"]
        self.assertIn("github.event_name == 'merge_group'", value(compare, "if", 8))
        script = " ".join(line.strip().rstrip("\\") for line in block(compare, "run", 8))
        listed = set(script.split("git diff --quiet FETCH_HEAD HEAD --", 1)[1].split(";", 1)[0].split())
        missing = native_test_inputs() - listed
        self.assertFalse(missing, f"the native tests read files the merge group does not compare: {sorted(missing)}")
        for name in ("Test the declaration collision check", "Test initialized compiled-audit isolation"):
            self.assertEqual(value(self.build[name], "if", 8),
                             "steps.audit-tools.outputs.unchanged != 'true'")


if __name__ == "__main__":
    unittest.main()
