#!/usr/bin/env python3
"""Two fixed costs of CI's `build` job that it skips when they cannot matter.

- The job deletes unused SDKs only when less than 60 GiB of disk is known to be
  free.
- A merge group skips the native tests of the audit tools when a build of main
  passed them on the same runner image with the same inputs. The step
  "Fingerprint the audit tools' inputs" hashes those inputs (tracked files,
  contents and modes); a build of main that passes the tests saves the
  fingerprint in main's cache. Every repository file the native tests read must
  therefore be fingerprinted, and the tests must be the ones the workflow runs.

These tests guard against accidental edits of those steps. They do not model
GitHub Actions.

Run with: python3 -m unittest discover -s scripts -p test_ci_build_trims.py
"""

from __future__ import annotations

import ast
import os
import re
import shlex
import shutil
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

import audit_rebuilt_modules as scoped
from test_merge_queue_checks import block, jobs, value, workflow

ROOT = Path(__file__).resolve().parent.parent
LIBRARIES = ("CSLibExt", "CSLibExtTest", "MathlibExt", "MathlibExtTest", "PhyslibExt",
             "PhyslibExtTest", "Domains", "DomainsTest", "WantedExt")
FINGERPRINT = "Fingerprint the audit tools' inputs"
LOOKUP = "Look for a build of main that passed the audit tools' tests"
WRITE = "Write the record of the audit tools' tests"
SAVE = "Save that a build of main passed the audit tools' tests"
NATIVE_STEPS = {
    "Test the declaration collision check": "test_declaration_collisions_native.py",
    "Test initialized compiled-audit isolation": "test_compiled_audit_native.py",
}
NATIVE_TESTS = tuple(f"scripts/{name}" for name in NATIVE_STEPS.values())
HAS_KEY = "steps.audit-tools-inputs.outputs.key != ''"
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


def python_modules(name: str, root: Path, packages: tuple[str, ...] = ("", "scripts/")) -> set[str]:
    """The local files an import of `name` (`a` or `a.b`) can load from `packages`."""
    parts = name.split(".")
    found: set[str] = set()
    for end in range(1, len(parts) + 1):
        stem = "/".join(parts[:end])
        for package in packages:
            found |= {candidate for candidate in (f"{package}{stem}.py", f"{package}{stem}/__init__.py")
                      if (root / candidate).is_file()}
    return found


def joined_path(node: ast.AST) -> str:
    """`Path("a") / "b" / "c"`, `Path("a", "b")`, `a.joinpath("b", "c")` or
    `os.path.join(a, "b", "c")` as "a/b/c": the constant parts of a path built
    from pieces, nested ones included, or "" if none."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value.strip("/")
    pieces: list[ast.AST] = []
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        pieces = [node.left, node.right]
    elif isinstance(node, ast.Call):
        name = node.func.attr if isinstance(node.func, ast.Attribute) else getattr(node.func, "id", "")
        if name in ("join", "joinpath", "Path", "PurePath", "PosixPath", "PurePosixPath"):
            pieces = ([node.func.value] if name == "joinpath" else []) + list(node.args)
    return "/".join(part for part in map(joined_path, pieces) if part)


def python_inputs(text: str, path: str, root: Path) -> set[str]:
    """The repository files a Python source names, joins or imports."""
    found: set[str] = set()
    for node in ast.walk(ast.parse(text)):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            found |= repository_files(node.value, root)
        elif isinstance(node, (ast.BinOp, ast.Call)):
            found |= repository_files(joined_path(node), root)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                found |= python_modules(alias.name, root)
        elif isinstance(node, ast.ImportFrom):
            packages: tuple[str, ...] = ("", "scripts/")
            if node.level:  # relative to the importing file's package
                package = Path(path).parent
                for _ in range(node.level - 1):
                    package = package.parent
                packages = (f"{package.as_posix()}/" if package.as_posix() != "." else "",)
            names = [node.module] if node.module else []
            names += [f"{node.module}.{alias.name}" if node.module else alias.name for alias in node.names]
            for name in names:
                found |= python_modules(name, root, packages)
    return found


def native_test_inputs(root: Path = ROOT, tests: tuple[str, ...] = NATIVE_TESTS) -> set[str]:
    """Every repository file the native tests name or import, followed through the
    local Python modules and shell scripts they use (with the Python those run)
    and the project modules their Lean files import."""
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
            found = python_inputs(text, path, root)
        elif path.endswith(".sh"):
            for name in re.findall(r"scripts/[\w./-]+", text):
                found |= repository_files(name, root)
            # Python run from the script, as a heredoc.
            for _, body in re.findall(r"<<-?\s*['\"]?(\w+)['\"]?[^\n]*\n(.*?)\n\s*\1\s*$", text, re.M | re.S):
                try:
                    found |= python_inputs(body, path, root)
                except SyntaxError:
                    pass
        elif path.endswith(".lean"):
            # The scoped audit's own reading of imports: any `import X`, comments
            # and line breaks included.
            modules = set(scoped.IMPORT.findall(text)) | set(scoped.IMPORT.findall(scoped.uncommented(text)))
            for module in modules:
                found |= {file for file in repository_files(module.replace("«", "").replace("»", ""), root)
                          if file.split("/")[0] in LIBRARIES}
        pending.extend(sorted(found - inputs))
    return inputs


def fingerprint_pathspecs(step: list[str]) -> list[str]:
    script = run_block(step)
    # The array closes on a line of its own; pathspec magic holds parentheses.
    return shlex.split(script.split("specs=(\n", 1)[1].split("\n)\n", 1)[0])


class BuildTrims(unittest.TestCase):
    def setUp(self) -> None:
        self.build = steps(jobs(workflow("ci.yml"))["build"])

    def test_merge_groups_skip_native_tests_only_after_main_passed_them(self):
        names = list(self.build)
        fingerprint = self.build[FINGERPRINT]
        self.assertIsNone(block(fingerprint, "if", 8))
        self.assertLess(names.index(FINGERPRINT), names.index(LOOKUP))
        self.assertEqual(value(self.build[LOOKUP], "if", 8), f"github.event_name == 'merge_group' && {HAS_KEY}")
        for name, test in NATIVE_STEPS.items():
            step = self.build[name]
            self.assertLess(names.index(LOOKUP), names.index(name))
            self.assertEqual(value(step, "if", 8), "steps.audit-tools.outputs.cache-hit != 'true'")
            self.assertEqual(value(step, "run", 8), f"python3 -m unittest discover -s scripts -p {test} -v")
            # A native test that may fail would let a failing build of main save the marker.
            self.assertIsNone(block(step, "continue-on-error", 8))
        for name in (WRITE, SAVE):
            self.assertEqual(value(self.build[name], "if", 8), f"{MAIN_BUILD} && {HAS_KEY}")
            self.assertGreater(names.index(name), max(names.index(step) for step in NATIVE_STEPS))
        for name in (LOOKUP, SAVE):
            self.assertEqual(value(block(self.build[name], "with", 8), "key", 10),
                             "${{ steps.audit-tools-inputs.outputs.key }}")

    def test_the_fingerprint_covers_every_input_of_the_native_tests(self):
        pathspecs = fingerprint_pathspecs(self.build[FINGERPRINT])
        self.assertIn(".github/workflows/ci.yml", pathspecs)
        listed = subprocess.run(["git", "ls-files", "-z", "--", *pathspecs], cwd=ROOT, check=True,
                                capture_output=True, text=True).stdout.split("\0")
        missing = native_test_inputs() - set(listed)
        self.assertFalse(missing, f"the native tests read files the fingerprint omits: {sorted(missing)}")

    def test_the_fingerprint_follows_contents_modes_and_the_image(self):
        script = run_block(self.build[FINGERPRINT])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in (".github/workflows/ci.yml", "lean-toolchain", "scripts/check.sh",
                         "scripts/taxonomy.json", "README.md"):
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                (root / name).write_text(name)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)

            def key(image: str | None = "20261116.1", failing: str = "") -> str:
                subprocess.run(["git", "add", "-A"], cwd=root, check=True)
                output = root / "output"
                output.write_text("")
                env = {**os.environ, "GITHUB_OUTPUT": str(output), "RUNNER_OS": "Linux"}
                env.pop("ImageVersion", None)
                if image is not None:
                    env["ImageVersion"] = image
                if failing:  # a `git` that fails when this condition on its arguments holds
                    stub = Path(directory) / "bin"
                    stub.mkdir(exist_ok=True)
                    (stub / "git").write_text(f'#!/usr/bin/env bash\nif {failing}; then exit 42; fi\n'
                                              f'exec {shutil.which("git")} "$@"\n')
                    (stub / "git").chmod(0o755)
                    env["PATH"] = f"{stub}:{env['PATH']}"
                result = subprocess.run(["bash", "-c", script], cwd=root, env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode != 0, bool(failing), result.stderr)
                return output.read_text()

            first = key()
            self.assertTrue(first.startswith("key=audit-tools-tested-Linux-20261116.1-"), first)
            self.assertEqual(key(None), "", "no image version, no fingerprint")
            for failing in ('[[ "$1 $2" == "ls-files --stage" ]]',  # the index listing fails
                            '[[ "$1 $2" == "ls-files -z" ]]'):  # the checked-out listing fails
                self.assertEqual(key(failing=failing), "", failing)
            self.assertNotEqual(key("20261123.1"), first)
            for path in ("scripts/taxonomy.json", "README.md"):  # not inputs
                (root / path).write_text("changed")
                self.assertEqual(key(), first, path)
            (root / "scripts/check.sh").write_text("changed\n")
            edited = key()
            self.assertNotEqual(edited, first, "an edit to a script must change the fingerprint")
            (root / "scripts/check.sh").chmod(0o755)
            moded = key()
            self.assertNotEqual(moded, edited, "a mode change must change the fingerprint")
            (root / "scripts/new.py").write_text("")
            added = key()
            self.assertNotEqual(added, moded, "a new script must change the fingerprint")
            # The same index, checked out with other line endings.
            subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "x"],
                           cwd=root, check=True)
            (root / ".git/info/attributes").write_text("*.sh text eol=crlf\n")
            (root / "scripts/check.sh").unlink()
            subprocess.run(["git", "checkout", "--", "scripts/check.sh"], cwd=root, check=True)
            self.assertIn(b"\r\n", (root / "scripts/check.sh").read_bytes())
            self.assertNotEqual(key(), added, "other checked-out bytes must change the fingerprint")

    def test_native_test_inputs_follow_new_reads_and_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("CONTRIBUTING.md", "scripts/helper.py", "scripts/data.json", "scripts/run.sh",
                         "scripts/list.sh", "scripts/embedded.py", "scripts/fixtures/sample.txt",
                         "scripts/data/items.json", "scripts/bump/__init__.py", "scripts/bump/pinned.py",
                         "scripts/bump/leaf.py", "scripts/pkg/__init__.py", "scripts/pkg/leaf.py",
                         ".github/workflows/ci.yml", "MathlibExt/A.lean", "MathlibExt/B.lean",
                         "blueprint/priorities.json", "scripts/check.lean", "MathlibExt/Helper.lean"):
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                (root / name).write_text("")
            (root / "scripts/helper.py").write_text('DATA = "data.json"\n')
            (root / "scripts/bump/pinned.py").write_text("from . import leaf\n")
            (root / "scripts/run.sh").write_text(
                "scripts/list.sh\npython3 - <<'PY'\nimport embedded\nfrom pkg import leaf\nPY\n")
            (root / "MathlibExt/A.lean").write_text("module\npublic import\n  MathlibExt.B -- why\n")
            (root / "scripts/check.lean").write_text("import Lean\nimport MathlibExt.Helper\n")
            (root / "scripts/test_x_native.py").write_text(
                'from helper import DATA\nfrom bump import pinned\n'
                'TEXT = (ROOT / "CONTRIBUTING.md").read_text()\n'
                'SAMPLE = (ROOT / "scripts" / "fixtures" / "sample.txt").read_text()\n'
                'ITEMS = Path("scripts", "data", "items.json").read_text()\n'
                'PRIORITIES = (Path("blueprint") / "priorities.json").read_text()\n'
                "DRIVER = 'scripts/check.lean'\n"
                'CI = ROOT.joinpath(".github", "workflows", "ci.yml").read_text()\n'
                "RUN = ['scripts/run.sh']\nPAIR = ['MathlibExt.A']\n")
            self.assertEqual(native_test_inputs(root, ("scripts/test_x_native.py",)), {
                "scripts/test_x_native.py", "scripts/helper.py", "scripts/data.json", "CONTRIBUTING.md",
                "scripts/fixtures/sample.txt", "scripts/data/items.json", ".github/workflows/ci.yml",
                "scripts/bump/__init__.py", "scripts/bump/pinned.py", "scripts/bump/leaf.py",
                "scripts/run.sh", "scripts/list.sh", "scripts/embedded.py", "scripts/pkg/__init__.py",
                "scripts/pkg/leaf.py", "MathlibExt/A.lean", "MathlibExt/B.lean", "blueprint/priorities.json",
                "scripts/check.lean", "MathlibExt/Helper.lean"})

    def test_disk_cleanup_runs_unless_60_gib_are_known_to_be_free(self):
        cases = {"62914560": False, "  62914560": False, "62914559": True, "000009": True,
                 "1 00000000": True, "unknown": True, None: True}
        for name, job in (("ci.yml", "build"), ("bump-cache.yml", "warm")):
            script = run_block(steps(jobs(workflow(name))[job])["Free disk space for Lean caches"])
            for available, cleans in cases.items():
                with self.subTest(workflow=name, available=available):
                    report = "return 1" if available is None else f"printf ' Avail\\n%s\\n' '{available}'"
                    stubs = ('sudo() { echo CLEANED; }\n'
                             f'df() {{ if [[ "$1" == -h ]]; then echo df; else {report}; fi; }}\n')
                    result = subprocess.run(["bash", "-c", stubs + script], capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stderr, "")
                    self.assertEqual("CLEANED" in result.stdout, cleans)


if __name__ == "__main__":
    unittest.main()
