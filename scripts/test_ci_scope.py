#!/usr/bin/env python3
"""Tests for scripts/ci_scope.py, the steps of .github/workflows/ci.yml and blueprint-pages.yml that run
it, and the tool tests that scripts/test_scripts.sh skips on its word.

    python3 -m unittest discover -s scripts -p test_ci_scope.py -v

The paths below are examples. These tests read only ci.yml, ci_scope.py and test_scripts.sh,
which preflight already follows as code of the required checks, and blueprint-pages.yml and
test_blueprint_taxonomy.py, only to compare them with ci.yml and ci_scope.py, so that a change to
either that would fail these tests must change one of those too: scripts/queue/preflight.py relies
on that (NAMES_ONLY).
"""

from __future__ import annotations

import os
import re
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


# Lean sources of the libraries and provenance: the build reads them, the tool tests do not.
LEAN = [
    "MathlibExt/Algebra/Group.lean",
    "WantedExt/Foo.lean",
    "DomainsTest/Biology/X.lean",
    "provenance/formal-math-sync.json",
    "provenance/formal-math-sync.d/MathlibExt/Algebra.json",
]
# The suites of scripts/test_scripts.sh that ATLAS_TOOL_TESTS=skip leaves out, and those that always run.
TOOL_TESTS = [
    "scripts/import_optimizer test_*.py",
    "scripts test_quality_eval.py",
    "scripts test_quality_pass.py",
    "scripts test_audit_parallel.py",
    "scripts test_formal_math_sync.py",
    "scripts test_public_references.py",
    "scripts test_public_reference_workflow.py",
    "scripts test_bump_cache_workflow.py",
    "scripts/bump/test_pinned_bump.py",
    "scripts/bump/test_bump_branch.py",
]
ALWAYS = [
    "scripts test_merge_queue_checks.py",
    "scripts test_ci_scope.py",
    "scripts test_ci_build_trims.py",
    "scripts test_next_task.py",
    "scripts/queue test_*.py",
]
TOOL_TESTS_ENV = ("${{ (github.event_name == 'pull_request' && steps.scope.outputs.tool_tests == 'false') "
                  "&& 'skip' || 'run' }}")


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
        self.assertTrue(ci_scope.needs_tool_tests([]))

    def test_the_tool_tests_skip_lean_graph_data_and_documentation(self):
        for path in SKIPPED + LEAN:
            with self.subTest(path=path):
                self.assertFalse(ci_scope.needs_tool_tests([path]))
        self.assertFalse(ci_scope.needs_tool_tests(SKIPPED + LEAN))
        self.assertTrue(ci_scope.needs_build(LEAN[:1]))
        for path in [p for p in BUILT if p not in LEAN]:
            with self.subTest(path=path):
                self.assertTrue(ci_scope.needs_tool_tests(SKIPPED + LEAN + [path]))
        # Lean files outside the libraries: the lessons, v1, the scripts' own Lean.
        for path in ("docs/teaching/examples/BoundedCodec.lean", "v1/Atlas.lean", "scripts/check_axioms.lean",
                     "Atlas/CDISProbability/A.lean", "MathlibExt.lean"):
            with self.subTest(path=path):
                self.assertTrue(ci_scope.needs_tool_tests([path]))

    def test_paths_are_read_whole_between_nul_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            listing = Path(temp) / "paths"

            def decide(*paths: bytes) -> str:
                listing.write_bytes(b"".join(path + b"\0" for path in paths))
                result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/ci_scope.py"), str(listing)],
                                        capture_output=True, text=True, check=True)
                return result.stdout

            self.assertEqual(decide(b"docs/a\nMathlibExt/B.lean.md", b"blueprint/\xff.md"),
                             "build=false\ntool_tests=false\nsite_tests=true\n")
            self.assertEqual(decide(b"docs/a.md", b"MathlibExt/B.lean"),
                             "build=true\ntool_tests=false\nsite_tests=false\n")
            self.assertEqual(decide(b"docs/a.md", b"scripts/x.py"), "build=true\ntool_tests=true\nsite_tests=true\n")
            self.assertEqual(decide(), "build=true\ntool_tests=true\nsite_tests=true\n")
            result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/ci_scope.py")],
                                    capture_output=True, text=True)
            self.assertEqual((result.returncode, result.stdout), (2, ""))


def job_lines(name: str, workflow: str = "ci.yml") -> list[str]:
    """The lines of job `name` in `workflow`."""
    lines = (ROOT / ".github/workflows" / workflow).read_text(encoding="utf-8").splitlines()
    start = lines.index(f"  {name}:")
    end = next((i for i in range(start + 1, len(lines)) if re.match(r"  \S", lines[i])), len(lines))
    job = lines[start:end]  # up to the next job, or the comment above it
    while job and not job[-1].strip():
        job.pop()
    return job


def decide_step(name: str = "changes", step_name: str = "Decide", workflow: str = "ci.yml") -> str:
    """The shell of the step that runs scripts/ci_scope.py in job `name` of `workflow`."""
    job = job_lines(name, workflow)
    step = job.index(f"      - name: {step_name}")
    run = next(i for i in range(step, len(job)) if job[i] == "        run: |")
    body = []
    for line in job[run + 1:]:
        if line.strip() and not line.startswith(" " * 10):
            break
        body.append(line)
    while body and not body[-1].strip():
        body.pop()
    return textwrap.dedent("\n".join(body))


class NeedsSiteTestsTests(unittest.TestCase):
    def test_lean_provenance_and_documentation_skip_the_site_tests(self):
        for path in LEAN + ["README.md", "docs/BLUEPRINT.md", ".agents/skills/atlas-graph-pr/SKILL.md"]:
            with self.subTest(path=path):
                self.assertFalse(ci_scope.needs_site_tests([path]))
        self.assertTrue(ci_scope.needs_site_tests([]))

    def test_what_the_site_tests_read_runs_them(self):
        for path in sorted(ci_scope.SITE_TEST_READS) + [p for p in SKIPPED if ci_scope.graph(p)] + [
                p for p in BUILT if p not in LEAN]:
            with self.subTest(path=path):
                self.assertTrue(ci_scope.needs_site_tests(LEAN + [path]))

    def test_the_lean_modules_read_are_those_the_taxonomy_test_indexes(self):
        text = (ROOT / "scripts/test_blueprint_taxonomy.py").read_text(encoding="utf-8")
        test = text.split("def test_extracted_declarations_are_published_in_their_source_field", 1)[1]
        cases = test.split("cases = {", 1)[1].split("}", 1)[0]
        modules = {module + ".lean" for module in re.findall(r'"([A-Za-z]+/[\w/]+)": "', cases)}
        self.assertEqual(len(modules), 4)
        self.assertEqual(modules, {p for p in ci_scope.SITE_TEST_READS if p.endswith(".lean")})
        self.assertTrue(all(ci_scope.library_source(p) for p in modules))


class WorkflowTests(unittest.TestCase):
    def test_the_job_checks_out_the_merge_and_runs_the_script_on_pull_requests_only(self):
        text = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        job = text.split("\n  changes:\n", 1)[1].split("\n\n  # ", 1)[0]
        self.assertIn("      build: ${{ steps.decide.outputs.build }}\n", job)
        self.assertIn("          fetch-depth: 2\n          sparse-checkout: /scripts/ci_scope.py\n", job)
        self.assertEqual(job.count("        if: github.event_name == 'pull_request'\n"), 2)

    def test_build_needs_changes_which_only_pull_requests_run(self):
        text = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
        build = text.split("\n  build:\n", 1)[1].split("\n    steps:\n", 1)[0] + "\n"
        changes = text.split("\n  changes:\n", 1)[1].split("\n    steps:\n", 1)[0] + "\n"
        self.assertIn("    needs: changes\n    if: ${{ !cancelled() && (github.event_name != 'pull_request' || "
                      "needs.changes.outputs.build != 'false') }}\n", build)
        self.assertIn("    if: github.event_name == 'pull_request'\n", changes)

    def test_repository_integrity_skips_the_tool_tests_on_pull_requests_only(self):
        job = "\n".join(job_lines("preflight")) + "\n"
        self.assertIn("          fetch-depth: ${{ github.event_name == 'pull_request' && 2 || 1 }}\n", job)
        self.assertIn("      - name: Decide whether to run the tool tests\n        id: scope\n"
                      "        if: github.event_name == 'pull_request'\n        continue-on-error: true\n", job)
        self.assertIn("      - name: Run deterministic repository checks\n        env:\n"
                      f"          ATLAS_TOOL_TESTS: {TOOL_TESTS_ENV}\n        run: scripts/check.sh preflight\n", job)
        self.assertEqual(job.count("ATLAS_TOOL_TESTS"), 1)
        self.assertEqual(decide_step("preflight", "Decide whether to run the tool tests"), decide_step())

    def test_blueprint_pages_skips_the_site_tests_on_pull_requests_only(self):
        scope = "\n".join(job_lines("scope", "blueprint-pages.yml")) + "\n"
        changes = "\n".join(job_lines("changes")) + "\n"
        # The same checkout and decision as CI's `changes` job, with its own output.
        self.assertEqual(scope.split("    steps:\n", 1)[1], changes.split("    steps:\n", 1)[1])
        self.assertIn("    outputs:\n      site_tests: ${{ steps.decide.outputs.site_tests }}\n    steps:\n", scope)
        self.assertNotIn("\n    if:", scope)
        tests = "\n".join(job_lines("tests", "blueprint-pages.yml")) + "\n"
        self.assertIn("    needs: [changes, scope]\n    if: ${{ !cancelled() && needs.changes.outputs.build == 'false' && "
                      "needs.scope.outputs.site_tests != 'false' }}\n", tests)

    def test_the_tool_tests_are_exactly_these_suites(self):
        text = (ROOT / "scripts/test_scripts.sh").read_text(encoding="utf-8")
        gated = text.split('\nif [[ "$tool_tests" == run ]]; then\n', 1)[1].split("\nelse\n", 1)[0]
        rest = text.replace(gated, "")

        suite = re.compile(r'\s*(?:PYTHONPATH=\S+\s+)?python3 (?:-m unittest discover\s+-s "\$REPO_ROOT/([\w/]+)" '
                           r'-p \'?([\w*.]+)\'?( -v)?|"\$REPO_ROOT/([\w/.]+)")')

        def suites(block: str) -> list[str]:
            joined = block.replace("\\\n", " ")
            return [f"{m[1]} {m[2]}" if m[1] else m[4] for m in re.finditer(r"(?m)^" + suite.pattern, joined)]
        self.assertEqual(suites(gated), TOOL_TESTS)
        # These must run outside the block; a suite in neither list runs too, until it is shown to read only
        # scripts, workflows and the pins and is moved into the block.
        self.assertEqual([name for name in ALWAYS if name not in suites(rest)], [])
        # And nothing outside the block depends on the variable: no `else` branch or second gate holds a suite.
        self.assertEqual((text.count("tool_tests"), text.count("ATLAS_TOOL_TESTS")), (4, 4))
        self.assertTrue(text.endswith('\nelse\n  echo "skipped [scripts]: the tool tests (ATLAS_TOOL_TESTS=skip)."\nfi\n\n'
                                      'echo "ok [scripts]: repository policy regression tests passed."\n'))
        # The skipped block holds those suites and nothing else: another command there would be skipped unseen.
        lines = [line for line in gated.replace("\\\n", " ").splitlines() if line.strip()]
        self.assertEqual([line for line in lines if not suite.fullmatch(line)], [])
        self.assertIn('tool_tests="${ATLAS_TOOL_TESTS-run}"\ncase "$tool_tests" in\n  run|skip) ;;\n', text)
        for value in ("", "yes", "Skip"):
            with self.subTest(value=value):
                result = subprocess.run(["bash", str(ROOT / "scripts/test_scripts.sh")], capture_output=True, text=True,
                                        env=dict(os.environ, ATLAS_TOOL_TESTS=value))
                self.assertEqual(result.returncode, 2)
                self.assertIn("ATLAS_TOOL_TESTS must be run or skip", result.stderr)

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
                             "build=true\ntool_tests=true\nsite_tests=true\n")  # a file named HEAD is a path like any other
            self.assertEqual(decide({"blueprint/roadmap/A.md": "c\n", "docs/C.md": "d\n"}),
                             "build=false\ntool_tests=false\nsite_tests=true\n")
            self.assertEqual(decide({"blueprint/roadmap/A.md": "d\n", "MathlibExt/A.lean": "def a : Nat := 2\n"}),
                             "build=true\ntool_tests=false\nsite_tests=true\n")
            self.assertEqual(decide({"MathlibExt/A.lean": "def a : Nat := 3\n", "docs/D.md": "e\n"}),
                             "build=true\ntool_tests=false\nsite_tests=false\n")


if __name__ == "__main__":
    unittest.main()
