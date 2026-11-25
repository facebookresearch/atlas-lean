#!/usr/bin/env python3
"""Tests for scripts/ci_scope.py and the `changes` job of .github/workflows/ci.yml that runs it.

    python3 -m unittest discover -s scripts -p test_ci_scope.py -v
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import ci_scope  # noqa: E402

SKIPPED = [
    "blueprint/roadmap/Algebra/README.md",
    "blueprint/links/Algebra.jsonl",
    "blueprint/migrations/AlgebraNotes.json",
    "scripts/taxonomy.json",
    "scripts/wiki-sync.json",
    "scripts/card-moves.jsonl",
    "scripts/mathgraph-map.jsonl",
    "README.md",
    "REVIEWING.md",
    "CONTRIBUTING.md",
    "docs/BLUEPRINT.md",
    "docs/teaching/README.md",
    "provenance/README.md",
    ".agents/skills/atlas-merge-queue/SKILL.md",
    ".claude/skills/atlas-merge-queue",
]
BUILT = [
    "MathlibExt/Algebra/Group.lean",
    "WantedExt/Foo.lean",
    "provenance/formal-math-sync.json",
    "docs/teaching/examples/BoundedCodec.lean",
    "scripts/check_axioms.sh",
    "scripts/ci_scope.py",
    "scripts/README.md",
    "scripts/taxonomy.jsonl",
    ".github/workflows/ci.yml",
    ".github/pull_request_template.md",
    ".gitattributes",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "NOTICE",
    "README.MD",
    "blueprint",
    "Blueprint/links/Algebra.jsonl",
    "v1/Atlas.lean",
]


class NeedsBuildTests(unittest.TestCase):
    def test_graph_data_and_documentation_need_no_build(self):
        for path in SKIPPED:
            with self.subTest(path=path):
                self.assertFalse(ci_scope.needs_build([path]))
        self.assertFalse(ci_scope.needs_build(SKIPPED))

    def test_any_other_path_needs_the_build(self):
        for path in BUILT:
            with self.subTest(path=path):
                self.assertTrue(ci_scope.needs_build([path]))
                self.assertTrue(ci_scope.needs_build(SKIPPED + [path]))

    def test_no_path_needs_the_build(self):
        self.assertTrue(ci_scope.needs_build([]))

    def test_paths_are_read_whole_between_nul_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            listing = Path(temp) / "paths"

            def decide(*paths: bytes) -> str:
                listing.write_bytes(b"".join(path + b"\0" for path in paths))
                result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/ci_scope.py"), str(listing)],
                                        capture_output=True, text=True, check=True)
                return result.stdout

            self.assertEqual(decide(b"docs/a\nMathlibExt/B.lean.md", b"blueprint/\xff.md"), "build=false\n")
            self.assertEqual(decide(b"docs/a.md", b"MathlibExt/B.lean"), "build=true\n")
            self.assertEqual(decide(), "build=true\n")
            result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/ci_scope.py")],
                                    capture_output=True, text=True)
            self.assertEqual((result.returncode, result.stdout), (2, ""))


def decide_step() -> str:
    """The shell of the Decide step of the `changes` job in ci.yml."""
    lines = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8").splitlines()
    start = lines.index("  changes:")
    end = next(i for i in range(start + 1, len(lines)) if lines[i].startswith("  ") and lines[i][2] not in " #")
    job = lines[start:end]
    step = job.index("      - name: Decide")
    run = next(i for i in range(step, len(job)) if job[i] == "        run: |")
    body = []
    for line in job[run + 1:]:
        if line.strip() and not line.startswith(" " * 10):
            break
        body.append(line)
    return textwrap.dedent("\n".join(body))


class WorkflowTests(unittest.TestCase):
    def test_the_job_checks_out_the_merge_and_runs_the_script_on_pull_requests_only(self):
        text = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        job = text.split("\n  changes:\n", 1)[1].split("\n\n  # ", 1)[0]
        self.assertIn("      build: ${{ steps.decide.outputs.build }}\n", job)
        self.assertIn("          fetch-depth: 2\n          sparse-checkout: /scripts/ci_scope.py\n", job)
        self.assertEqual(job.count("        if: github.event_name == 'pull_request'\n"), 2)

    def test_the_decide_step_on_a_merge_commit(self):
        script = decide_step()
        self.assertIn('python3 -I scripts/ci_scope.py "$RUNNER_TEMP/changed-paths" >> "$GITHUB_OUTPUT"', script)
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "repo"
            env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
            env.update(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
                       GIT_COMMITTER_EMAIL="t@t", GIT_CONFIG_NOSYSTEM="1", HOME=temp)

            def git(*args: str) -> str:
                return subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True,
                                      check=True, env=env).stdout.strip()

            def write(path: str, text: str) -> None:
                (repo / path).parent.mkdir(parents=True, exist_ok=True)
                (repo / path).write_text(text, encoding="utf-8")

            repo.mkdir()
            git("init", "-q", "-b", "main")
            write("scripts/ci_scope.py", (ROOT / "scripts/ci_scope.py").read_text(encoding="utf-8"))
            write("blueprint/roadmap/A.md", "a\n")
            write("MathlibExt/A.lean", "def a : Nat := 1\n")
            git("add", "-A")
            git("commit", "-qm", "base")

            def decide(changes: dict[str, str]) -> str:
                git("checkout", "-q", "-B", "topic", "main")
                for path, text in changes.items():
                    write(path, text)
                git("add", "-A")
                git("commit", "-qm", "change")
                # GitHub's merge commit for a pull request: the base first, then the head.
                git("checkout", "-q", "--detach", "main")
                git("merge", "-q", "--no-ff", "--no-edit", "topic")
                runner = Path(temp) / "runner"
                runner.mkdir(exist_ok=True)
                output = runner / "output"
                output.write_text("", encoding="utf-8")
                subprocess.run(["bash", "-c", script], cwd=repo, check=True, capture_output=True,
                               env=dict(env, RUNNER_TEMP=str(runner), GITHUB_OUTPUT=str(output)))
                git("checkout", "-q", "main")
                return output.read_text(encoding="utf-8")

            self.assertEqual(decide({"blueprint/roadmap/A.md": "b\n", "HEAD": "x\n", "docs/B.md": "c\n"}),
                             "build=true\n")  # a file named HEAD is a path like any other
            self.assertEqual(decide({"blueprint/roadmap/A.md": "c\n", "docs/C.md": "d\n"}), "build=false\n")
            self.assertEqual(decide({"blueprint/roadmap/A.md": "d\n", "MathlibExt/A.lean": "def a : Nat := 2\n"}),
                             "build=true\n")


if __name__ == "__main__":
    unittest.main()
