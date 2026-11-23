#!/usr/bin/env python3
"""What CI's `build` job audits and tests, and where a missed module still shows up.

Pull requests and merge groups audit only the modules their build rewrote since
the cached build they restore (scripts/audit_rebuilt_modules.py). That is sound
only while main's cache holds builds that passed the audit of their own commit,
so build-cache.yml must promote only the build of the successful merge-group run
of that exact commit. Builds of main keep the full audit, and a failed one is
reported in an issue. A merge group also skips the native tests of the audit
tools when a build of main passed them with the same files, so the cache key
that records it must hash every repository file those tests read.

These tests guard against accidental edits of those workflows. They do not
model GitHub Actions.

Run with: python3 -m unittest discover -s scripts -p test_ci_audit_scope.py
"""

from __future__ import annotations

import ast
import os
import re
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

from test_merge_queue_checks import block, jobs, value, workflow

ROOT = Path(__file__).resolve().parent.parent
NATIVE_TESTS = ("scripts/test_declaration_collisions_native.py", "scripts/test_compiled_audit_native.py")
LIBRARIES = ("CSLibExt", "CSLibExtTest", "MathlibExt", "MathlibExtTest", "PhyslibExt",
             "PhyslibExtTest", "Domains", "DomainsTest", "WantedExt")
RECORD = "Record the restored build for a scoped audit"
LOOKUP = "Look for a build of main that passed the audit tools' tests"
WRITE = "Write the record of the audit tools' tests"
SAVE = "Save that a build of main passed the audit tools' tests"
NATIVE_STEPS = ("Test the declaration collision check", "Test initialized compiled-audit isolation")
MAIN_BUILD = ("(github.event_name == 'push' || github.event_name == 'workflow_dispatch')"
              " && github.ref == 'refs/heads/main'")


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


def run_block(step: list[str]) -> str:
    return textwrap.dedent("\n".join(block(step, "run", 8)))


def repository_files(literal: str, root: Path) -> set[str]:
    """The files `literal` can name: a path, a name in scripts/, or a module."""
    if not literal or any(character.isspace() for character in literal):
        return set()
    candidates = {literal, f"scripts/{literal}"}
    if "/" not in literal:
        candidates.add(literal.replace(".", "/") + ".lean")
    return {path for path in candidates
            if not path.startswith(("/", "..")) and (root / path).is_file()}


def native_test_inputs(root: Path = ROOT, tests: tuple[str, ...] = NATIVE_TESTS) -> set[str]:
    """Every repository file the native tests name or import, followed through the
    local Python modules and shell scripts they use and the project modules their
    Lean files import."""
    inputs: set[str] = set()
    pending = list(tests)
    while pending:
        path = pending.pop()
        if path in inputs:
            continue
        inputs.add(path)
        text = (root / path).read_text(encoding="utf-8")
        found: set[str] = set()
        if path.endswith(".py"):
            for node in ast.walk(ast.parse(text)):
                if isinstance(node, ast.Constant) and isinstance(node.value, str):
                    found |= repository_files(node.value, root)
                elif isinstance(node, ast.Import):
                    for alias in node.names:
                        found |= repository_files(alias.name.split(".")[0] + ".py", root)
                elif isinstance(node, ast.ImportFrom) and node.module and not node.level:
                    found |= repository_files(node.module.split(".")[0] + ".py", root)
        elif path.endswith(".sh"):
            for name in re.findall(r"scripts/[\w.-]+", text):
                found |= repository_files(name, root)
        elif path.endswith(".lean") and path.split("/")[0] in LIBRARIES:
            for module in re.findall(r"^(?:public )?import (?:all )?([\w.]+)", text, re.M):
                found |= {file for file in repository_files(module, root)
                          if file.split("/")[0] in LIBRARIES}
        pending.extend(sorted(found - inputs))
    return inputs


def hashed_files(step: list[str]) -> list[str]:
    key = value(block(step, "with", 8), "key", 10)
    match = re.fullmatch(r"audit-tools-tested-\$\{\{ runner\.os \}\}-\$\{\{ hashFiles\((.*)\) \}\}", key)
    if match is None:
        raise AssertionError(f"unexpected key: {key}")
    return re.findall(r"'([^']+)'", match.group(1))


class BuildAuditScope(unittest.TestCase):
    def setUp(self) -> None:
        self.ci = jobs(workflow("ci.yml"))
        self.build = steps(self.ci["build"])

    def test_only_pull_requests_and_merge_groups_scope_the_audit(self):
        self.assertEqual(
            value(self.build[RECORD], "if", 8),
            "(github.event_name == 'pull_request' || github.event_name == 'merge_group')"
            " && steps.local-build-cache.outputs.cache-matched-key != ''")
        setters = [name for name, lines in self.build.items()
                   if any("ATLAS_AUDIT_RESTORED" in line for line in lines)]
        self.assertEqual(setters, [RECORD])

    def test_main_takes_only_the_merge_group_build_of_its_commit(self):
        save = jobs(workflow("build-cache.yml"))["save"]
        download = " ".join(steps(save)["Download the merge group's build"])
        for term in ("actions/workflows/ci.yml/runs?", "event=merge_group",
                     "head_sha=${GITHUB_SHA}", "status=success", "actions/runs/${run}/artifacts"):
            self.assertIn(term, download)

    def test_merge_groups_skip_native_tests_only_after_main_passed_them(self):
        names = list(self.build)
        self.assertEqual(value(self.build[LOOKUP], "if", 8), "github.event_name == 'merge_group'")
        for name in NATIVE_STEPS:
            self.assertLess(names.index(LOOKUP), names.index(name))
            self.assertEqual(value(self.build[name], "if", 8),
                             "steps.audit-tools.outputs.cache-hit != 'true'")
        for name in (WRITE, SAVE):
            self.assertEqual(value(self.build[name], "if", 8), MAIN_BUILD)
            self.assertGreater(names.index(name), max(names.index(step) for step in NATIVE_STEPS))
        self.assertEqual(hashed_files(self.build[LOOKUP]), hashed_files(self.build[SAVE]))
        missing = native_test_inputs() - set(hashed_files(self.build[SAVE]))
        self.assertFalse(missing, f"the native tests read files the key does not hash: {sorted(missing)}")

    def test_native_test_inputs_follow_new_reads_and_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("CONTRIBUTING.md", "scripts/helper.py", "scripts/data.json",
                         "scripts/run.sh", "scripts/list.sh", "MathlibExt/A.lean", "MathlibExt/B.lean"):
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                (root / name).write_text("")
            (root / "scripts/helper.py").write_text('DATA = "data.json"\n')
            (root / "scripts/run.sh").write_text("scripts/list.sh\n")
            (root / "MathlibExt/A.lean").write_text("module\npublic import MathlibExt.B\n")
            (root / "scripts/test_x_native.py").write_text(
                'from helper import DATA\nTEXT = (ROOT / "CONTRIBUTING.md").read_text()\n'
                "RUN = ['scripts/run.sh']\nPAIR = ['MathlibExt.A']\n")
            self.assertEqual(native_test_inputs(root, ("scripts/test_x_native.py",)), {
                "scripts/test_x_native.py", "scripts/helper.py", "scripts/data.json", "CONTRIBUTING.md",
                "scripts/run.sh", "scripts/list.sh", "MathlibExt/A.lean", "MathlibExt/B.lean"})

    def test_disk_cleanup_runs_unless_60_gib_are_known_to_be_free(self):
        cases = {"echo 62914560": False, "echo 62914559": True, "echo unknown": True, "return 1": True}
        for name, job in (("ci.yml", "build"), ("bump-cache.yml", "warm")):
            script = run_block(steps(jobs(workflow(name))[job])["Free disk space for Lean caches"])
            for probe, cleans in cases.items():
                with self.subTest(workflow=name, probe=probe):
                    stubs = ('sudo() { echo CLEANED; }\n'
                             f'df() {{ if [[ "$1" == -h ]]; then echo df; else {probe}; fi; }}\n')
                    result = subprocess.run(["bash", "-c", stubs + script], capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual("CLEANED" in result.stdout, cleans)

    def test_a_failed_main_build_is_reported_once(self):
        report = self.ci["report"]
        self.assertEqual(value(report, "needs", 4), "build")
        self.assertEqual(value(report, "if", 4), "failure() && github.event_name == 'push'")
        self.assertEqual([line.strip() for line in block(report, "permissions", 4) if line.strip()],
                         ["issues: write"])
        script = run_block(steps(report)["Open or update the issue"])
        with tempfile.TemporaryDirectory() as directory:
            stub = Path(directory) / "gh"
            stub.write_text('#!/usr/bin/env bash\n'
                            'echo "$*" >> "$GH_LOG"\n'
                            'if [[ "$1" == api ]]; then printf "%b" "$ISSUES"; exit "${API_STATUS:-0}"; fi\n')
            stub.chmod(0o755)
            for issues, status, expected in (("12\\n34\\n", "0", "issue comment 12 --body"),
                                             ("", "0", "issue create --title CI build fails on main"),
                                             ("", "1", None)):
                with self.subTest(issues=issues, status=status):
                    log = Path(directory) / "log"
                    log.write_text("")
                    env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}", "GH_LOG": str(log),
                           "ISSUES": issues, "API_STATUS": status, "GH_REPO": "o/r", "RUN_URL": "u",
                           "GITHUB_SHA": "0" * 40}
                    result = subprocess.run(["bash", "-c", script], env=env, capture_output=True, text=True)
                    calls = log.read_text().splitlines()
                    self.assertTrue(calls[0].startswith("api --paginate repos/o/r/issues?state=open"))
                    if expected is None:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertEqual(len(calls), 1, "an API error must not open an issue")
                    else:
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(len(calls), 2)
                        self.assertTrue(calls[1].startswith(expected), calls[1])


if __name__ == "__main__":
    unittest.main()
