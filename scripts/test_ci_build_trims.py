#!/usr/bin/env python3
"""Two fixed costs of CI's `build` job that it skips when they cannot matter.

- The job deletes unused SDKs only when less than 60 GiB of disk is known to be
  free.
- A merge group skips the native tests of the audit tools when a build of main
  passed them with the same files on the same runner image. A build of main that
  passes them saves a marker in main's cache, keyed on the runner image and on
  the hash of every repository file those tests read, so the key must hash all
  of those files.

These tests guard against accidental edits of those steps. They do not model
GitHub Actions.

Run with: python3 -m unittest discover -s scripts -p test_ci_build_trims.py
"""

from __future__ import annotations

import ast
import re
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

import audit_rebuilt_modules as scoped
from test_merge_queue_checks import block, jobs, value, workflow

ROOT = Path(__file__).resolve().parent.parent
NATIVE_TESTS = ("scripts/test_declaration_collisions_native.py", "scripts/test_compiled_audit_native.py")
LIBRARIES = ("CSLibExt", "CSLibExtTest", "MathlibExt", "MathlibExtTest", "PhyslibExt",
             "PhyslibExtTest", "Domains", "DomainsTest", "WantedExt")
IMAGE = "Read the runner image version"
LOOKUP = "Look for a build of main that passed the audit tools' tests"
WRITE = "Write the record of the audit tools' tests"
SAVE = "Save that a build of main passed the audit tools' tests"
NATIVE_STEPS = ("Test the declaration collision check", "Test initialized compiled-audit isolation")
MAIN_BUILD = ("(github.event_name == 'push' || github.event_name == 'workflow_dispatch')"
              " && github.ref == 'refs/heads/main'")
KEY = re.compile(r"audit-tools-tested-\$\{\{ runner\.os \}\}-\$\{\{ steps\.image\.outputs\.version \}\}"
                 r"-\$\{\{ hashFiles\((.*)\) \}\}")


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


def python_modules(name: str, root: Path) -> set[str]:
    """The local files a Python import of `name` (`a` or `a.b`) can load."""
    parts = name.split(".")
    found: set[str] = set()
    for end in range(1, len(parts) + 1):
        stem = "/".join(parts[:end])
        found |= repository_files(f"{stem}.py", root) | repository_files(f"{stem}/__init__.py", root)
    return found


def joined_path(node: ast.AST) -> str:
    """`a / "b" / "c"`, `a.joinpath("b", "c")` or `os.path.join(a, "b", "c")` as
    "b/c": the constant parts of a path built from pieces, or "" if none."""
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in ("join", "joinpath"):
        pieces = list(node.args)
    else:
        pieces = []
        while isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            pieces.insert(0, node.right)
            node = node.left
    parts = [piece.value.strip("/") for piece in pieces
             if isinstance(piece, ast.Constant) and isinstance(piece.value, str)]
    return "/".join(parts)


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
                elif isinstance(node, (ast.BinOp, ast.Call)):
                    found |= repository_files(joined_path(node), root)
                elif isinstance(node, ast.Import):
                    for alias in node.names:
                        found |= python_modules(alias.name, root)
                elif isinstance(node, ast.ImportFrom) and node.module and not node.level:
                    for alias in node.names:
                        found |= python_modules(f"{node.module}.{alias.name}", root)
        elif path.endswith(".sh"):
            for name in re.findall(r"scripts/[\w./-]+", text):
                found |= repository_files(name, root)
            # Python run from the script, as a heredoc or with -c.
            for module in re.findall(r"^\s*(?:import|from)\s+([\w.]+)", text, re.M):
                found |= python_modules(module, root)
        elif path.endswith(".lean") and path.split("/")[0] in LIBRARIES:
            # The scoped audit's own reading of imports: any `import X`, comments
            # and line breaks included.
            modules = set(scoped.IMPORT.findall(text)) | set(scoped.IMPORT.findall(scoped.uncommented(text)))
            for module in modules:
                found |= {file for file in repository_files(module.replace("«", "").replace("»", ""), root)
                          if file.split("/")[0] in LIBRARIES}
        pending.extend(sorted(found - inputs))
    return inputs


def hashed_files(step: list[str]) -> list[str]:
    key = value(block(step, "with", 8), "key", 10)
    match = KEY.fullmatch(key)
    if match is None:
        raise AssertionError(f"unexpected key: {key}")
    return re.findall(r"'([^']+)'", match.group(1))


class BuildTrims(unittest.TestCase):
    def setUp(self) -> None:
        self.build = steps(jobs(workflow("ci.yml"))["build"])

    def test_merge_groups_skip_native_tests_only_after_main_passed_them(self):
        names = list(self.build)
        self.assertIsNone(block(self.build[IMAGE], "if", 8))
        self.assertLess(names.index(IMAGE), names.index(LOOKUP))
        self.assertEqual(value(self.build[LOOKUP], "if", 8), "github.event_name == 'merge_group'")
        for name in NATIVE_STEPS:
            self.assertLess(names.index(LOOKUP), names.index(name))
            self.assertEqual(value(self.build[name], "if", 8),
                             "steps.audit-tools.outputs.cache-hit != 'true'")
            # A native test that may fail would let a failing build of main save the marker.
            self.assertIsNone(block(self.build[name], "continue-on-error", 8))
        for name in (WRITE, SAVE):
            self.assertEqual(value(self.build[name], "if", 8), MAIN_BUILD)
            self.assertGreater(names.index(name), max(names.index(step) for step in NATIVE_STEPS))
        self.assertEqual(hashed_files(self.build[LOOKUP]), hashed_files(self.build[SAVE]))
        missing = native_test_inputs() - set(hashed_files(self.build[SAVE]))
        self.assertFalse(missing, f"the native tests read files the key does not hash: {sorted(missing)}")

    def test_native_test_inputs_follow_new_reads_and_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("CONTRIBUTING.md", "scripts/helper.py", "scripts/data.json", "scripts/run.sh",
                         "scripts/list.sh", "scripts/embedded.py", "scripts/fixtures/sample.txt",
                         "scripts/bump/__init__.py", "scripts/bump/pinned.py", ".github/workflows/ci.yml",
                         "MathlibExt/A.lean", "MathlibExt/B.lean"):
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                (root / name).write_text("")
            (root / "scripts/helper.py").write_text('DATA = "data.json"\n')
            (root / "scripts/run.sh").write_text("scripts/list.sh\npython3 - <<'PY'\nimport embedded\nPY\n")
            (root / "MathlibExt/A.lean").write_text("module\npublic import\n  MathlibExt.B -- why\n")
            (root / "scripts/test_x_native.py").write_text(
                'from helper import DATA\nfrom bump import pinned\n'
                'TEXT = (ROOT / "CONTRIBUTING.md").read_text()\n'
                'SAMPLE = (ROOT / "scripts" / "fixtures" / "sample.txt").read_text()\n'
                'CI = ROOT.joinpath(".github", "workflows", "ci.yml").read_text()\n'
                "RUN = ['scripts/run.sh']\nPAIR = ['MathlibExt.A']\n")
            self.assertEqual(native_test_inputs(root, ("scripts/test_x_native.py",)), {
                "scripts/test_x_native.py", "scripts/helper.py", "scripts/data.json", "CONTRIBUTING.md",
                "scripts/fixtures/sample.txt", ".github/workflows/ci.yml", "scripts/bump/__init__.py",
                "scripts/bump/pinned.py", "scripts/run.sh", "scripts/list.sh", "scripts/embedded.py",
                "MathlibExt/A.lean", "MathlibExt/B.lean"})

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


if __name__ == "__main__":
    unittest.main()
