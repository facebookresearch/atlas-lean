#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""No-inference tests; set QUALITY_INDICATORS_DIR to enable official-suite integration."""
from __future__ import annotations

import argparse
import importlib._bootstrap_external
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import quality_eval as evaluation


class StatisticsTests(unittest.TestCase):
    def test_wilson_matches_article(self) -> None:
        lower, upper = evaluation.wilson(31, 1000)
        self.assertEqual(round(lower * 100, 1), 2.2)
        self.assertEqual(round(upper * 100, 1), 4.4)

    def test_wilson_zero_and_all(self) -> None:
        self.assertAlmostEqual(evaluation.wilson(0, 100)[0], 0.0)
        self.assertAlmostEqual(evaluation.wilson(100, 100)[1], 1.0)
        self.assertGreater(evaluation.wilson(0, 100)[1], 0.0)

    def test_invalid_denominators(self) -> None:
        for flagged, judged in ((0, 0), (-1, 3), (4, 3)):
            with self.assertRaises(ValueError):
                evaluation.wilson(flagged, judged)

    def test_missing_is_not_a_negative(self) -> None:
        cell = evaluation.summarize([{"id": "a"}, {"id": "b"}], {
            "a": {"id": "a", "verdict": "none_found"}}, "unnecessary-hypotheses")
        self.assertFalse(cell["complete"])
        self.assertEqual(cell["missing"], ["b"])
        self.assertIsNone(cell["rate"])
        self.assertIsNone(cell["wilson95"])

    def test_partial_keeps_comparable_rate_and_reports_bounds(self) -> None:
        cell = evaluation.summarize([{"id": "a"}], {
            "a": {"id": "a", "verdict": "none_found", "coverage": "partial"}},
            "repeated-proof-machinery")
        self.assertTrue(cell["complete"])
        self.assertFalse(cell["full_coverage"])
        self.assertEqual(cell["partial"], ["a"])
        self.assertEqual(cell["rate"], 0.0)
        self.assertEqual(cell["partial_negative_bounds"], [0.0, 1.0])

    def test_empty_population_is_not_green(self) -> None:
        self.assertFalse(evaluation.summarize([], {}, "unnecessary-hypotheses")["complete"])

    def test_not_applicable_remains_in_file_denominator(self) -> None:
        cell = evaluation.summarize([{"id": "a"}, {"id": "b"}], {
            "a": {"id": "a", "verdict": "findings_found", "coverage": "complete"},
            "b": {"id": "b", "verdict": "not_applicable", "coverage": "complete"}},
            "repeated-proof-machinery")
        self.assertEqual(cell["rate"], 0.5)
        self.assertEqual(cell["not_applicable"], 1)

    def test_scope_excludes_legacy_wanted_tests_and_certificates(self) -> None:
        self.assertTrue(evaluation.eligible_path("MathlibExt/Analysis/X.lean", "atlas"))
        self.assertTrue(evaluation.eligible_path("CSLibExt/Logic/X.lean", "atlas"))
        self.assertTrue(evaluation.eligible_path("PhyslibExt/StatisticalMechanics/X.lean", "atlas"))
        for path in ("Atlas/X.lean", "v1/X.lean", "WantedExt/X.lean", "MathlibExtTest/X.lean",
                     "CSLibExtTest/X.lean", "PhyslibExtTest/X.lean", "MathlibExt/Certificates/X.lean",
                     "PhyslibExt/Certificates/X.lean", "MathlibExt/README.md", "PhyslibExt/README.md"):
            self.assertFalse(evaluation.eligible_path(path, "atlas"), path)
        self.assertFalse(evaluation.eligible_path("Mathlib/Tactic/Basic.lean", "mathlib"))
        self.assertTrue(evaluation.eligible_path("Mathlib/Analysis/Basic.lean", "mathlib"))


class TraceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.cwd = self.root / "sources"
        self.cwd.mkdir()
        self.trace = self.root / "trace.jsonl"
        self.initial = {"type": "system", "subtype": "init", "model": "test",
                        "cwd": str(self.cwd), "claude_code_version": "1.0.0",
                        "tools": ["Read", "Grep", "Glob", "StructuredOutput"]}

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_trace(self, tool: str = "Read", arguments: dict[str, object] | None = None) -> None:
        event = {"type": "assistant", "message": {"content": [{"type": "tool_use", "name": tool,
                  "input": arguments or {"file_path": str(self.cwd / "A.lean")}}]}}
        self.trace.write_text(json.dumps(self.initial) + "\n" + json.dumps(event) + "\n")

    def check_trace(self) -> None:
        evaluation.validate_session_trace(self.trace, self.cwd, [self.cwd], "test", "1.0.0 (Claude Code)")

    def test_source_read_allowed(self) -> None:
        self.write_trace()
        self.check_trace()

    def test_parent_directory_search_rejected(self) -> None:
        self.write_trace("Grep", {"path": str(self.root), "pattern": "theorem"})
        with self.assertRaisesRegex(ValueError, "outside"):
            self.check_trace()

    def test_default_grep_directory_allowed(self) -> None:
        self.write_trace("Grep", {"path": None, "pattern": "theorem"})
        self.check_trace()

    def test_glob_pattern_traversal_rejected(self) -> None:
        self.write_trace("Glob", {"path": str(self.cwd), "pattern": "../../results/*.json"})
        with self.assertRaisesRegex(ValueError, "traverses"):
            self.check_trace()

    def test_absolute_glob_outside_root_rejected(self) -> None:
        self.write_trace("Glob", {"pattern": "/tmp/**/report.md"})
        with self.assertRaisesRegex(ValueError, "outside"):
            self.check_trace()

    def test_absolute_brace_alternative_rejected(self) -> None:
        self.write_trace("Glob", {"path": str(self.cwd), "pattern": "{/tmp,MathlibExt}/**"})
        with self.assertRaisesRegex(ValueError, "absolute"):
            self.check_trace()
        self.write_trace("Grep", {"path": str(self.cwd), "pattern": "x", "glob": "{A,../results}/*.json"})
        with self.assertRaisesRegex(ValueError, "traverses"):
            self.check_trace()
        for pattern in (".{.,}/atlas/**/*.lean", "[.][.]/atlas/**/*.lean"):
            self.write_trace("Glob", {"path": str(self.cwd), "pattern": pattern})
            with self.assertRaisesRegex(ValueError, "traverses"):
                self.check_trace()
        self.write_trace("Grep", {"path": str(self.cwd), "pattern": "x", "glob": "{Mathlib,Batteries}/**/*.lean"})
        self.check_trace()

    def test_shell_tool_rejected(self) -> None:
        self.write_trace("Bash", {"command": "true"})
        with self.assertRaisesRegex(ValueError, "unauthorized tool"):
            self.check_trace()

    def test_cli_version_drift_rejected(self) -> None:
        self.initial["claude_code_version"] = "2.0.0"
        self.write_trace()
        with self.assertRaisesRegex(ValueError, "CLI version"):
            self.check_trace()

    def test_model_drift_rejected(self) -> None:
        self.initial["model"] = "another-model"
        self.write_trace()
        with self.assertRaisesRegex(ValueError, "initialization"):
            self.check_trace()


class ArchiveTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.command("init", "-q")
        self.command("config", "user.email", "test@example.invalid")
        self.command("config", "user.name", "Quality evaluation test")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def command(self, *arguments: str) -> str:
        return subprocess.check_output(["git", "-C", str(self.repo), *arguments], text=True).strip()

    def commit(self) -> None:
        self.command("add", ".")
        self.command("commit", "-qm", "fixture")

    def test_committed_sources_only(self) -> None:
        (self.repo / "A.lean").write_text("theorem a : True := by trivial\n")
        (self.repo / "secret.txt").write_text("not a judge input\n")
        self.commit()
        (self.repo / "Untracked.lean").write_text("theorem untracked : True := by trivial\n")
        destination = self.root / "snapshot"
        result = evaluation.snapshot(self.repo, destination)
        self.assertEqual(set(result["files"]), {"A.lean"})
        self.assertFalse((destination / ".git").exists())
        self.assertFalse((destination / "secret.txt").exists())
        self.assertFalse((destination / "Untracked.lean").exists())

    def test_tracked_modification_rejected(self) -> None:
        (self.repo / "A.lean").write_text("theorem a : True := by trivial\n")
        self.commit()
        (self.repo / "A.lean").write_text("theorem a : False := by sorry\n")
        with self.assertRaisesRegex(ValueError, "tracked changes"):
            evaluation.snapshot(self.repo, self.root / "snapshot")

    def test_symlink_source_rejected(self) -> None:
        (self.repo / "A.lean").write_text("theorem a : True := by trivial\n")
        (self.repo / "Link.lean").symlink_to("A.lean")
        self.commit()
        with self.assertRaisesRegex(ValueError, "nonregular"):
            evaluation.snapshot(self.repo, self.root / "snapshot")


def git_fixture(path: Path, sources: dict[str, str]) -> str:
    path.mkdir(parents=True, exist_ok=True)
    for name, data in sources.items():
        target = path / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(data)
    for arguments in (("init", "-q"), ("config", "user.email", "test@example.invalid"),
                      ("config", "user.name", "Quality evaluation test"), ("add", "."),
                      ("commit", "-qm", "fixture")):
        subprocess.run(["git", "-C", str(path), *arguments], check=True, capture_output=True)
    return evaluation.git(path, "rev-parse", "HEAD")


class PinnedUpstreamLoadingTests(unittest.TestCase):
    """Only the pinned commit's Git objects may execute, never local bytecode or untracked modules."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.upstream = self.root / "upstream"
        self.marker = self.root / "executed"
        sources = {f"scripts/{name}.py": f"ORIGIN = 'pinned'\n" for name in evaluation.UPSTREAM_MODULES}
        sources["scripts/judge.py"] = ("import source_tools\nORIGIN = source_tools.ORIGIN\n"
                                       "def validate_verdict(verdict, protocol):\n    return None\n")
        sources["scripts/file_audits.py"] = "import judge\nORIGIN = judge.ORIGIN\n"
        commit = git_fixture(self.upstream, sources)
        names = set(evaluation.UPSTREAM_MODULES)
        self.saved_modules = {name: module for name, module in sys.modules.items() if name in names}
        for name in names:
            sys.modules.pop(name, None)
        self.saved_meta_path, self.saved_path = list(sys.meta_path), list(sys.path)
        self.saved_cache = dict(evaluation._UPSTREAM_CACHE)
        evaluation._UPSTREAM_CACHE.clear()
        self.pin = mock.patch.object(evaluation, "UPSTREAM_COMMIT", commit)
        self.pin.start()

    def tearDown(self) -> None:
        self.pin.stop()
        for name in evaluation.UPSTREAM_MODULES:
            sys.modules.pop(name, None)
        sys.modules.update(self.saved_modules)
        sys.meta_path[:], sys.path[:] = self.saved_meta_path, self.saved_path
        evaluation._UPSTREAM_CACHE.clear()
        evaluation._UPSTREAM_CACHE.update(self.saved_cache)
        self.temporary.cleanup()

    def malicious(self, name: str) -> str:
        return (f"open({str(self.marker)!r}, 'w').write('executed')\nORIGIN = 'attacker'\n"
                "def validate_verdict(verdict, protocol):\n    return None\n")

    def test_timestamp_valid_untracked_bytecode_never_executes(self) -> None:
        source = self.upstream / "scripts" / "judge.py"
        stat = source.stat()
        code = compile(self.malicious("judge"), str(source), "exec")
        cached = Path(importlib.util.cache_from_source(str(source)))
        cached.parent.mkdir()
        cached.write_bytes(importlib._bootstrap_external._code_to_timestamp_pyc(code, stat.st_mtime, stat.st_size))
        upstream = evaluation.load_upstream(self.upstream)
        self.assertFalse(self.marker.exists())
        self.assertEqual((upstream.judge.ORIGIN, upstream.files.ORIGIN), ("pinned", "pinned"))
        self.assertEqual(Path(upstream.judge.__file__), source.resolve())

    def test_untracked_shadowing_package_never_executes(self) -> None:
        package = self.upstream / "scripts" / "sample" / "__init__.py"
        package.parent.mkdir()
        package.write_text(self.malicious("sample"))
        try:
            upstream = evaluation.load_upstream(self.upstream)
        finally:  # A later rejection is too late once the package has run.
            self.assertFalse(self.marker.exists())
        self.assertEqual(upstream.sample.ORIGIN, "pinned")
        self.assertNotIn(str(self.upstream / "scripts"), sys.path)

    def test_hidden_working_tree_edit_never_executes(self) -> None:
        source = self.upstream / "scripts" / "leanscan.py"
        evaluation.git(self.upstream, "update-index", "--skip-worktree", "scripts/leanscan.py")
        source.write_text(self.malicious("leanscan"))
        upstream = evaluation.load_upstream(self.upstream)
        self.assertFalse(self.marker.exists())
        self.assertEqual(upstream.scan.ORIGIN, "pinned")

    def test_preloaded_unrelated_module_is_rejected(self) -> None:
        sys.modules["judge"] = SimpleNamespace(__spec__=None)
        with self.assertRaisesRegex(ValueError, "shadows"):
            evaluation.load_upstream(self.upstream)


def fake_scanner() -> SimpleNamespace:
    def scan(text: str, kinds: object = None, extra_other: object = None) -> tuple[list[object], list[object]]:
        names = re.findall(r"(?m)^theorem (\S+)", text)
        return [SimpleNamespace(full_name=name, deprecated=False) for name in names], []
    return SimpleNamespace(scan=scan, DECL_KW=("theorem",))


class DeclarationIndexTests(unittest.TestCase):
    """Only an index preparation exported from the pinned build may vouch for generated names."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.run_dir = Path(self.temporary.name) / "run"
        module = self.run_dir / "views/atlas/mathlib/Mathlib/Fixture.lean"
        module.parent.mkdir(parents=True)
        module.write_text("theorem mathlib_a : True := trivial\n")
        (self.run_dir / "protocols/duplicates-mathlib-inclusive").mkdir(parents=True)
        self.upstream = SimpleNamespace(theorem_validator=lambda verdict, protocol: None, scan=fake_scanner())
        self.row = {"lib": "atlas", "name": "atlas_a"}

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def install(self, pairs: list[list[str]], info: dict[str, object] | None) -> None:
        data = json.dumps(pairs).encode()
        (self.run_dir / "compiled-declarations.json").write_bytes(data)
        if info is not None:
            info = {"sha256": evaluation.digest(data), "entries": len(pairs), **info}
        evaluation.write_json(self.run_dir / "manifest.json", {"compiled_declaration_index": info})

    def cite(self, name: str) -> evaluation.Row:
        verdict = {"verdict": "duplicate", "mathlib_declaration": name, "file": "Mathlib/Fixture.lean",
                   "derivation": f"by exact {name}", "proof_uses_it": False, "explanation": "Fixture."}
        return evaluation.validate_theorem(verdict, "duplicates-mathlib-inclusive", self.upstream,
                                           self.run_dir / "protocols/duplicates-mathlib-inclusive", self.row)

    def test_supplied_index_cannot_fabricate_membership(self) -> None:
        fabricated = [["fabricated_duplicate", "Mathlib.Fixture"]]
        for info in (None, {"mathlib_commit": "pinned", "lean_toolchain": "leanprover/lean4:v4.35.0"}):
            self.install(fabricated, info)
            self.assertEqual(evaluation.declaration_index(self.run_dir), {})
            with self.assertRaisesRegex(ValueError, "not a declaration"):
                self.cite("fabricated_duplicate")

    def test_prepared_index_validates_generated_name_and_detects_tampering(self) -> None:
        self.install([["generated_name", "Mathlib.Fixture"]], {"generated_by": evaluation.INDEX_GENERATOR})
        self.assertEqual(self.cite("generated_name"), {})
        self.assertEqual(self.cite("mathlib_a"), {})
        (self.run_dir / "compiled-declarations.json").write_text('[["other", "Mathlib.Fixture"]]')
        with self.assertRaisesRegex(ValueError, "index changed"):
            self.cite("generated_name")

    def fake_lake(self, version: str = "4.35.0", stale: bool = False) -> object:
        calls: list[list[str]] = []
        def run(arguments: list[str], repo: Path, env: dict[str, str] | None = None) -> str:
            calls.append(arguments)
            if arguments[:2] == ["build", "--no-build"] and stale:
                raise ValueError("lake build --no-build Mathlib failed: target is not up-to-date")
            if arguments == ["env", "lean", "--version"]:
                return f"Lean (version {version}, x86_64-unknown-linux-gnu, Release)\n"
            if arguments[:2] == ["env", "lean"]:
                assert env is not None
                Path(env["QUALITY_SYMBOLS_OUTPUT"]).write_text('[["generated_name", "Mathlib.Fixture"]]')
            return ""
        run.calls = calls  # type: ignore[attr-defined]
        return run

    def test_preparation_exports_index_from_the_verified_build(self) -> None:
        repo = Path(self.temporary.name) / "atlas"
        repo.mkdir()
        (repo / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        output = self.run_dir / "compiled-declarations.json"
        fake = self.fake_lake()
        with mock.patch.object(evaluation, "run_lake", fake):
            info = evaluation.export_declaration_index(repo, output)
        self.assertEqual(fake.calls[0], ["build", "--no-build", "Mathlib"])  # type: ignore[attr-defined]
        self.assertEqual((info["generated_by"], info["entries"]), (evaluation.INDEX_GENERATOR, 1))
        self.assertEqual(info["sha256"], evaluation.digest(output.read_bytes()))
        output.unlink()
        for fake, message in ((self.fake_lake(stale=True), "missing or stale"),
                              (self.fake_lake(version="4.34.0"), "does not match")):
            with mock.patch.object(evaluation, "run_lake", fake), self.assertRaisesRegex(ValueError, message):
                evaluation.export_declaration_index(repo, output)
            self.assertFalse(output.exists())

    def test_cli_no_longer_accepts_a_supplied_index(self) -> None:
        script = Path(evaluation.__file__)
        completed = subprocess.run([sys.executable, str(script), "prepare", "--upstream", "x", "--run-dir",
                                    str(self.run_dir / "new"), "--declaration-index", "symbols.json"],
                                   capture_output=True, text=True)
        self.assertEqual(completed.returncode, 2)
        self.assertIn("--declaration-index", completed.stderr)


class ScopeRetryTests(unittest.TestCase):
    """Outer attempts discarded for denied source access stay in diagnostics, evidence and cost."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.run_dir = Path(self.temporary.name) / "run"
        self.view = self.run_dir / "views/atlas"
        self.cwd = self.view / "atlas"
        self.cwd.mkdir(parents=True)
        self.row = {"id": "atlas-theorem-0000", "lib": "atlas", "input_sha256": "input", "source_sha256": "source"}
        self.indicator = "duplicates-mathlib-inclusive"
        self.destination = evaluation.result_path(self.run_dir, self.indicator, "label", self.row)
        self.destination.parent.mkdir(parents=True)
        self.args = SimpleNamespace(retries=1, model="test", cli_version="1.0.0 (Claude Code)", protocol_sha256="p")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def upstream(self, denied_calls: set[int]) -> SimpleNamespace:
        calls: list[int] = []
        def judge_one(row: evaluation.Row, run: Path, protocol: Path, results: Path, args: object) -> evaluation.Row:
            call = len(calls)
            calls.append(call)
            denied = call in denied_calls
            destination = results / f"{row['id']}.json"
            raw = {"type": "result", "structured_output": {"verdict": "duplicate" if denied else "none_found"},
                   "permission_denials": [{"tool_name": "Read"}] if denied else [], "call": call,
                   "total_cost_usd": 0.25, "modelUsage": {"test": {"inputTokens": 10, "contextWindow": 200000}}}
            initial = {"type": "system", "subtype": "init", "model": "test", "cwd": str(self.cwd),
                       "claude_code_version": "1.0.0", "tools": ["Read", "Grep", "Glob", "StructuredOutput"],
                       "additional_directories": [str(self.view)]}
            trace = json.dumps(initial) + "\n" + json.dumps(raw) + "\n"
            destination.with_name(f"{row['id']}.attempt-1.transcript.jsonl").write_text(trace)
            destination.with_suffix(".transcript.jsonl").write_text(trace)
            evaluation.write_json(destination.with_suffix(".raw.json"), raw)
            result = {"id": row["id"], "lib": row["lib"], "verdict": raw["structured_output"]["verdict"],
                      "attempts": 1, "cost_usd": 0.25, "usage": {"input_tokens": 10}}
            evaluation.write_json(destination, result)
            return result
        directories = lambda row: (self.cwd, {"combined": self.view})
        return SimpleNamespace(judge=SimpleNamespace(judge_one=judge_one, judge_dirs=directories))

    def review(self, upstream: SimpleNamespace) -> evaluation.Row:
        saved = lambda run, indicator, label, row, upstream: evaluation.read_json(self.destination)
        with mock.patch.object(evaluation, "validate_saved", saved):
            return evaluation.review_in_context(self.run_dir, "label", (self.indicator, self.row), upstream, self.args)

    def test_rejected_outer_attempt_is_counted_archived_and_costed(self) -> None:
        result = self.review(self.upstream({0}))
        diagnostics = result["attempt_diagnostics"]
        self.assertEqual((diagnostics["scope_rejections"], diagnostics["outer_scope_retries"],
                          diagnostics["total_attempts"]), (1, 1, 2))
        self.assertFalse(diagnostics["accepted_on_first_attempt"])
        self.assertEqual(diagnostics["first_raw_verdict"], "duplicate")
        stem = self.row["id"]
        for name in (f"{stem}.scope-rejected-0.transcript.jsonl", f"{stem}.scope-rejected-0.attempt-1.transcript.jsonl"):
            self.assertEqual(json.loads((self.destination.parent / name).read_text().splitlines()[1])["call"], 0)
        accepted = self.destination.with_suffix(".transcript.jsonl").read_text().splitlines()[1]
        self.assertEqual(json.loads(accepted)["call"], 1)
        self.assertEqual(evaluation.result_cost(result), 0.5)
        self.assertEqual(result["all_attempts_model_usage"]["test"], {"inputTokens": 20, "contextWindow": 200000})
        cell = evaluation.summarize([self.row], {stem: result}, self.indicator)
        self.assertEqual((cell["attempts"]["scope_rejections"], cell["attempts"]["accepted_on_first_attempt"]), (1, 0))

    def test_exhausted_retries_keep_every_attempt(self) -> None:
        with self.assertRaisesRegex(ValueError, "access was denied"):
            self.review(self.upstream({0, 1}))
        stem = self.row["id"]
        calls = [json.loads((self.destination.parent / f"{stem}.scope-rejected-{index}.transcript.jsonl")
                            .read_text().splitlines()[1])["call"] for index in (0, 1)]
        self.assertEqual(calls, [0, 1])
        failure = json.loads((self.destination.parent / f"{stem}.scope-rejected-failures.jsonl").read_text())
        self.assertEqual([item["cost_usd"] for item in failure["scope_rejected_attempts"]], [0.25, 0.25])
        self.assertFalse(self.destination.exists())
        result = self.review(self.upstream({0}))  # A resumed run keeps and counts earlier evidence.
        self.assertEqual([item["outer_attempt"] for item in result["scope_rejected_attempts"]], [0, 1, 2])
        self.assertEqual(result["attempt_diagnostics"]["scope_rejections"], 3)
        self.assertEqual(evaluation.result_cost(result), 1.0)


@unittest.skipUnless(os.environ.get("QUALITY_INDICATORS_DIR"), "set QUALITY_INDICATORS_DIR for pinned-suite integration")
class OfficialSuiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.upstream_path = Path(os.environ["QUALITY_INDICATORS_DIR"])
        cls.upstream = evaluation.load_upstream(cls.upstream_path)

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_seeded_theorem_draw_is_extendible(self) -> None:
        population = [{"name": str(index)} for index in range(100)]
        first = evaluation.select(population, 10, 0, "atlas", "theorem", self.upstream)
        extended = evaluation.select(population, 30, 0, "atlas", "theorem", self.upstream)
        self.assertEqual(first, extended[:10])
        self.assertEqual(len({row["name"] for row in extended}), 30)

    def test_file_order_matches_official_hash(self) -> None:
        rows = [{"dir": "atlas", "path": path} for path in ("MathlibExt/A.lean", "CSLibExt/B.lean")]
        expected = sorted(rows, key=lambda row: evaluation.digest(
            f"file-quality-v1:0:atlas:atlas:{row['path']}".encode()))
        self.assertEqual(evaluation.select(rows, 2, 0, "atlas", "file", self.upstream), expected)

    def test_excess_sample_count_rejected(self) -> None:
        with self.assertRaises(ValueError):
            evaluation.select([{}], 2, 0, "atlas", "theorem", self.upstream)

    def test_scanner_context_exclusions_and_wanted_boundary(self) -> None:
        source = self.root / "MathlibExt" / "Fixture.lean"
        source.parent.mkdir()
        source.write_text("namespace Fixture\nvariable (unused : True)\ninclude unused\n"
                          "/-- Documentation. -/\ntheorem visible : True := by trivial\n"
                          "theorem_wanted deferred : True\n"
                          "private theorem hidden : True := by trivial\n"
                          "@[deprecated visible]\ntheorem obsolete : True := by trivial\nend Fixture\n")
        theorems, files, census = evaluation.scan_population(
            self.root, "atlas", ["MathlibExt/Fixture.lean"], self.upstream)
        self.assertEqual([row["name"] for row in theorems], ["Fixture.visible"])
        self.assertEqual(len(files), 1)
        self.assertEqual(census["skipped_private"], 1)
        self.assertEqual(census["skipped_deprecated"], 1)
        declarations, docs = self.upstream.scan.scan(source.read_text(), extra_other={"theorem_wanted", "def_wanted"})
        visible = next(declaration for declaration in declarations if declaration.full_name == "Fixture.visible")
        snippet = self.upstream.scan.render_context(source.read_text(), docs, visible)
        self.assertIn("namespace Fixture", snippet)
        self.assertIn("variable (unused : True)", snippet)
        self.assertIn("include unused", snippet)
        self.assertNotIn("Documentation", snippet)
        self.assertNotIn("theorem_wanted", snippet)
        self.assertNotIn("theorem hidden", snippet)

    def make_repo(self, path: Path, sources: dict[str, str]) -> str:
        path.mkdir(parents=True)
        for name, data in sources.items():
            target = path / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(data)
        for arguments in (("init", "-q"), ("config", "user.email", "test@example.invalid"),
                          ("config", "user.name", "Quality evaluation test"), ("add", "."),
                          ("commit", "-qm", "fixture")):
            subprocess.run(["git", "-C", str(path), *arguments], check=True, capture_output=True)
        return evaluation.git(path, "rev-parse", "HEAD")

    @staticmethod
    def atlas_fixture_sources(physics: bool) -> dict[str, str]:
        return {
            "MathlibExt/Fixture.lean": ("-- no declarations\n" if physics else
                "theorem atlas_a : True := by trivial\ntheorem atlas_b : True := by trivial\n"),
            "CSLibExt/Empty.lean": "-- no declarations\n",
            "PhyslibExt/Fixture.lean": ("module\npublic lemma physics_a : True := by trivial\n"
                "public lemma physics_b : True := by trivial\n"
                "private lemma physics_hidden : True := by trivial\n"
                "@[deprecated physics_a (since := \"2026-01-01\")]\n"
                "public lemma physics_old : True := by trivial\n" if physics else "-- no declarations\n"),
            "PhyslibExtTest/Excluded.lean": "lemma physics_test : True := by trivial\n",
        }

    def prepare_fixture(self, index: list[list[str]] | None = None, *, physics: bool = False) -> Path:
        repo = self.root / "atlas"
        repo.mkdir()
        dependency = repo / ".lake" / "packages" / "mathlib"
        revision = self.make_repo(dependency, {"Mathlib/Fixture.lean":
            "theorem mathlib_a : True := by trivial\ntheorem mathlib_b : True := by trivial\n"
            "@[deprecated mathlib_a (since := \"2026-01-01\")]\ntheorem mathlib_old : True := by trivial\n"})
        packages = [{"name": "mathlib", "rev": revision,
                     "url": "https://github.com/leanprover-community/mathlib4"}]
        if physics:
            revision = self.make_repo(repo / ".lake/packages/Physlib", {
                f"{root}/Fixture.lean": f"lemma {root}.upstream_fixture : True := by trivial\n"
                for root in ("Physlib", "PhyslibAlpha", "QuantumInfo")})
            packages.append({"name": "Physlib", "rev": revision,
                             "url": "https://github.com/leanprover-community/physlib"})
        self.make_repo(repo / "production", {"placeholder.lean": "-- unused\n"})
        for name, data in {
            **self.atlas_fixture_sources(physics),
            "lake-manifest.json": json.dumps({"packagesDir": ".lake/packages", "packages": packages}),
            "lakefile.toml": 'name = "atlas"\n', "lean-toolchain": "leanprover/lean4:v4.35.0\n",
            ".gitignore": ".lake/\nproduction/\n"}.items():
            target = repo / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(data)
        for arguments in (("init", "-q"), ("config", "user.email", "test@example.invalid"),
                          ("config", "user.name", "Quality evaluation test"), ("add", "."),
                          ("commit", "-qm", "fixture")):
            subprocess.run(["git", "-C", str(repo), *arguments], check=True, capture_output=True)
        run = self.root / "evaluation"
        def lake(arguments: list[str], repo: Path, env: dict[str, str] | None = None) -> str:
            if arguments == ["env", "lean", "--version"]:
                return "Lean (version 4.35.0, x86_64-unknown-linux-gnu, Release)\n"
            if env is not None:
                Path(env["QUALITY_SYMBOLS_OUTPUT"]).write_text(json.dumps(index))
            return ""
        with mock.patch.object(evaluation, "run_lake", lake):
            evaluation.prepare(argparse.Namespace(repo=repo, run_dir=run, upstream=self.upstream_path,
                                                 lean_core_repo=None, theorems=2, files=1, seed=0,
                                                 compile_declaration_index=index is not None))
        return run

    def write_negative_results(self, run: Path, label: str) -> None:
        tasks = evaluation.selected_tasks(run, None, None)
        evaluation.write_json(run / "judges" / f"{label}.json", {"model": "test", "effort": "high",
            "cli_version": "1.0.0 (Claude Code)", "runner_sha256": evaluation.RUNNER_SHA256,
            "manifest_sha256": evaluation.digest((run / "manifest.json").read_bytes()),
            "tasks": [{"indicator": indicator, "id": row["id"]} for indicator, row in tasks]})
        (run / "runner" / f"{label}.py").write_bytes(evaluation.RUNNER_BYTES)
        protocol_hash = evaluation.digest((run / "judges" / f"{label}.json").read_bytes())
        for indicator, row in tasks:
            destination = evaluation.result_path(run, indicator, label, row)
            trace = destination.with_suffix(".transcript.jsonl")
            trace.parent.mkdir(parents=True, exist_ok=True)
            view = run / "views" / row["lib"]
            trace.write_text(json.dumps({"type": "system", "subtype": "init", "model": "test",
                "cwd": str(view / row["lib"]), "claude_code_version": "1.0.0",
                "additional_directories": ["/managed/preset", str(view),
                                           *(str(path) for path in view.iterdir() if path.name != row["lib"])],
                "tools": ["Read", "Grep", "Glob", "StructuredOutput"]}) + "\n")
            result = {"id": row["id"], "lib": row["lib"], "input_sha256": row["input_sha256"], "verdict": "none_found",
                      "source_sha256": row["source_sha256"], "source_run_dir": str(run),
                      "model": "test", "effort": "high", "judge_protocol_sha256": protocol_hash,
                      "trace_sha256": evaluation.digest(trace.read_bytes())}
            if indicator == "unnecessary-hypotheses":
                result["hypotheses"] = []
            elif indicator == "duplicates-mathlib-inclusive":
                result.update(mathlib_declaration="", file="", derivation="", proof_uses_it=False, explanation="Fixture negative.")
            else:
                result.update(coverage="complete", review_notes="Fixture reviewed entirely.", findings=[])
            evaluation.write_json(evaluation.result_path(run, indicator, label, row), result)

    def test_real_preparation_and_populated_report(self) -> None:
        run = self.prepare_fixture()
        manifest = evaluation.verify_run(run)
        self.assertEqual(manifest["populations"]["atlas"]["theorems"], 2)
        self.assertEqual(len(evaluation.selected_tasks(run, None, None)), 10)
        self.write_negative_results(run, "fixture")
        evaluation.report(argparse.Namespace(run_dir=run, label="fixture", require_complete=True))
        summary = evaluation.read_json(run / "reports" / "fixture" / "summary.json")
        self.assertTrue(summary["complete"])
        self.assertEqual(len(summary["cells"]), 6)
        self.assertEqual(summary["cells"]["unnecessary-hypotheses/MathlibExt/public"]["judged"], 2)
        lines = (run / "reports/fixture/report.md").read_text().splitlines()
        header = next(index for index, line in enumerate(lines) if line.startswith("| Indicator"))
        self.assertEqual(lines[header].count("|"), lines[header + 1].count("|"))
        self.assertEqual(lines[header].count("|"), lines[header + 2].count("|"))

    def test_physics_preparation_and_populated_report(self) -> None:
        run = self.prepare_fixture(physics=True)
        manifest = evaluation.verify_run(run)
        self.assertEqual(manifest["scope"]["atlas"], ["MathlibExt", "CSLibExt", "PhyslibExt"])
        census = manifest["populations"]["atlas"]
        self.assertEqual(census["roots"]["PhyslibExt"]["public_theorems"], 2)
        self.assertEqual(census["roots"]["PhyslibExt"]["files"], 1)
        self.assertEqual(census["skipped_private"], 1)
        self.assertEqual(census["skipped_deprecated"], 1)
        self.assertFalse((run / "corpus/atlas/PhyslibExtTest").exists())
        targets = [row for row in evaluation.read_json(run / "theorems.json")["rows"] if row["lib"] == "atlas"]
        self.assertEqual({row["name"] for row in targets}, {"physics_a", "physics_b"})
        self.assertTrue(all(row["root"] == "PhyslibExt" for row in targets))
        self.write_negative_results(run, "physics-fixture")
        evaluation.report(argparse.Namespace(run_dir=run, label="physics-fixture", require_complete=True))
        summary = evaluation.read_json(run / "reports/physics-fixture/summary.json")
        self.assertTrue(summary["complete"])
        for indicator in evaluation.INDICATORS:
            visibility = "whole-file" if indicator == "repeated-proof-machinery" else "public"
            cell = summary["cells"][f"{indicator}/PhyslibExt/{visibility}"]
            self.assertEqual(cell["judged"], 1 if visibility == "whole-file" else 2)
        self.assertEqual(summary["comparisons"], {})
        text = (run / "reports/physics-fixture/report.md").read_text()
        self.assertIn("Scope: maintained MathlibExt, CSLibExt, PhyslibExt;", text)
        self.assertIn("Physlib (including PhyslibAlpha and QuantumInfo) redundancy is not measured", text)
        self.assertIn("CSLibExt and PhyslibExt have no domain-matched control", text)

    def test_physics_duplicate_references_preserve_official_scope(self) -> None:
        run = self.prepare_fixture(physics=True)
        evaluation.verify_run(run)
        row = next(row for row in evaluation.read_json(run / "theorems.json")["rows"] if row["lib"] == "atlas")
        protocol = run / "protocols/duplicates-mathlib-inclusive"
        verdict = {"verdict": "duplicate", "mathlib_declaration": "mathlib_a",
                   "file": "Mathlib/Fixture.lean", "derivation": "by exact mathlib_a",
                   "proof_uses_it": False, "explanation": "Source-binding fixture only."}
        self.assertEqual(evaluation.validate_theorem(verdict, protocol.name, self.upstream, protocol, row), {})
        for root in ("Physlib", "PhyslibAlpha", "QuantumInfo"):
            relative = f"{root}/Fixture.lean"
            absolute = run / "views/atlas/Physlib" / relative
            self.assertTrue(absolute.is_file())
            for path in (relative, str(absolute)):
                with self.subTest(root=root, path=path):
                    with self.assertRaisesRegex(ValueError, "permitted pinned upstreams"):
                        evaluation.validate_theorem({**verdict, "mathlib_declaration": f"{root}.upstream_fixture",
                            "file": path, "derivation": f"by exact {root}.upstream_fixture"},
                            protocol.name, self.upstream, protocol, row)

    def test_changed_sample_rejected(self) -> None:
        run = self.prepare_fixture()
        row = evaluation.read_json(run / "theorems.json")["rows"][0]
        (run / row["file"]).write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "Sample input changed"):
            evaluation.verify_run(run)

    def test_changed_source_rejected(self) -> None:
        run = self.prepare_fixture()
        (run / "corpus/atlas/MathlibExt/Fixture.lean").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "Frozen source changed"):
            evaluation.verify_run(run)

    def test_changed_protocol_rejected(self) -> None:
        run = self.prepare_fixture()
        (run / "protocols/unnecessary-hypotheses/prompt.md").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "Frozen protocol changed"):
            evaluation.verify_run(run)

    def test_missing_judgment_blocks_complete_report(self) -> None:
        run = self.prepare_fixture()
        self.write_negative_results(run, "fixture")
        indicator, row = evaluation.selected_tasks(run, None, None)[0]
        evaluation.result_path(run, indicator, "fixture", row).unlink()
        with self.assertRaisesRegex(RuntimeError, "incomplete"):
            evaluation.report(argparse.Namespace(run_dir=run, label="fixture", require_complete=True))
        summary = evaluation.read_json(run / "reports/fixture/summary.json")
        self.assertFalse(summary["complete"])
        self.assertIsNone(summary["cells"][f"{indicator}/{row['root']}/{row.get('visibility', 'whole-file')}"]["rate"])

    def test_result_input_identity_rejected(self) -> None:
        run = self.prepare_fixture()
        self.write_negative_results(run, "fixture")
        indicator, row = evaluation.selected_tasks(run, None, None)[0]
        path = evaluation.result_path(run, indicator, "fixture", row)
        result = evaluation.read_json(path)
        result["input_sha256"] = "wrong"
        evaluation.write_json(path, result)
        with self.assertRaisesRegex(ValueError, "identity or input hash"):
            evaluation.report(argparse.Namespace(run_dir=run, label="fixture", require_complete=True))

    def test_file_excerpt_must_exist(self) -> None:
        run = self.prepare_fixture()
        manifest = evaluation.verify_run(run)
        evaluation.configure_judge(run, manifest, self.upstream)
        row = evaluation.read_json(run / "files.json")["rows"][0]
        self.upstream.files.context.text = (run / row["file"]).read_text()
        cwd, extras = self.upstream.judge.judge_dirs(row)
        self.upstream.files.context.sources = self.upstream.sources.Sources([cwd, *extras.values()])
        verdict = {"verdict": "findings_found", "coverage": "complete", "review_notes": "Checked.",
            "findings": [{"declaration": "atlas_a", "excerpt": "NOT PRESENT", "problem": "Repeated reasoning",
                "proposed_change": "Extract shared lemma", "benefit": "Reuse", "start_line": 1, "end_line": 1,
                "evidence": [{"path": str(cwd / row["path"]), "declaration": "atlas_a", "excerpt": "theorem atlas_a"}]}]}
        with self.assertRaisesRegex(ValueError, "excerpt"):
            self.upstream.files.validate(verdict, run / "protocols/repeated-proof-machinery")
        del self.upstream.files.context.text
        del self.upstream.files.context.sources

    def test_symbol_index_can_validate_a_generated_name(self) -> None:
        run = self.prepare_fixture([["generated_fixture", "Mathlib.Fixture"]])
        evaluation.verify_run(run)
        row = next(row for row in evaluation.read_json(run / "theorems.json")["rows"] if row["lib"] == "atlas")
        verdict = {"verdict": "duplicate", "mathlib_declaration": "generated_fixture",
                   "file": "Mathlib/Fixture.lean", "derivation": "by exact generated_fixture",
                   "proof_uses_it": False, "explanation": "Generated declaration fixture."}
        evaluation.validate_theorem(verdict, "duplicates-mathlib-inclusive", self.upstream,
                                    run / "protocols/duplicates-mathlib-inclusive", row)

    def test_hand_written_index_is_ignored(self) -> None:
        run = self.prepare_fixture()
        row = next(row for row in evaluation.read_json(run / "theorems.json")["rows"] if row["lib"] == "atlas")
        evaluation.write_json(run / "compiled-declarations.json", [["generated_fixture", "Mathlib.Fixture"]])
        verdict = {"verdict": "duplicate", "mathlib_declaration": "generated_fixture",
                   "file": "Mathlib/Fixture.lean", "derivation": "by exact generated_fixture",
                   "proof_uses_it": False, "explanation": "Fabricated index fixture."}
        with self.assertRaisesRegex(ValueError, "not a declaration"):
            evaluation.validate_theorem(verdict, "duplicates-mathlib-inclusive", self.upstream,
                                        run / "protocols/duplicates-mathlib-inclusive", row)

    def test_fabricated_duplicate_is_rejected(self) -> None:
        run = self.prepare_fixture()
        row = evaluation.read_json(run / "theorems.json")["rows"][0]
        verdict = {"verdict": "duplicate", "mathlib_declaration": "Nat.totally_fabricated",
                   "file": "Mathlib/Does/Not/Exist.lean", "derivation": "by exact Nat.totally_fabricated",
                   "proof_uses_it": False, "explanation": "Invalid citation fixture."}
        with self.assertRaisesRegex(ValueError, "citation"):
            evaluation.validate_theorem(verdict, "duplicates-mathlib-inclusive", self.upstream,
                                        run / "protocols/duplicates-mathlib-inclusive", row)

    def test_fabricated_hypothesis_is_rejected(self) -> None:
        run = self.prepare_fixture()
        row = evaluation.read_json(run / "theorems.json")["rows"][0]
        verdict = {"verdict": "unnecessary_hypothesis_found", "hypotheses": [{
            "binder": "(hFabricated : 2 + 2 = 5)", "source": "theorem", "justification": "Invalid fixture."}]}
        with self.assertRaisesRegex(ValueError, "binder"):
            evaluation.validate_theorem(verdict, "unnecessary-hypotheses", self.upstream,
                                        run / "protocols/unnecessary-hypotheses", row)

    def test_module_private_declarations_are_not_public(self) -> None:
        path = self.root / "MathlibExt/Module.lean"
        path.parent.mkdir()
        path.write_text("module\nnamespace ModuleFixture\ntheorem hidden : True := by trivial\n"
                        "public theorem visible : True := by trivial\npublic section\n"
                        "theorem section_visible : True := by trivial\nend\nend ModuleFixture\n")
        private = []
        public, _, census = evaluation.scan_population(self.root, "atlas", ["MathlibExt/Module.lean"],
                                                       self.upstream, private_out=private)
        self.assertEqual({row["name"] for row in public}, {"ModuleFixture.visible", "ModuleFixture.section_visible"})
        self.assertEqual([row["name"] for row in private], ["ModuleFixture.hidden"])
        self.assertEqual(census["skipped_module_private"], 1)

    def test_report_survives_relocation(self) -> None:
        run = self.prepare_fixture()
        self.write_negative_results(run, "fixture")
        moved = self.root / "relocated"
        run.rename(moved)
        evaluation.report(argparse.Namespace(run_dir=moved, label="fixture", require_complete=True))
        self.assertTrue(evaluation.read_json(moved / "reports/fixture/summary.json")["complete"])

    def test_stale_runner_is_rejected(self) -> None:
        run = self.prepare_fixture()
        self.write_negative_results(run, "fixture")
        path = run / "judges/fixture.json"
        manifest = evaluation.read_json(path)
        manifest["runner_sha256"] = "f" * 64
        evaluation.write_json(path, manifest)
        with self.assertRaisesRegex(ValueError, "different adapter"):
            evaluation.report(argparse.Namespace(run_dir=run, label="fixture", require_complete=True))

    def test_mathlib_judge_cannot_read_atlas_or_prior_results(self) -> None:
        run = self.prepare_fixture()
        evaluation.configure_judge(run, evaluation.verify_run(run), self.upstream)
        rows = evaluation.read_json(run / "theorems.json")["rows"]
        row = next(row for row in rows if row["lib"] == "mathlib")
        cwd, extras = self.upstream.judge.judge_dirs(row)
        roots = [cwd, *extras.values()]
        self.assertEqual(extras[evaluation.COMBINED_LABEL], run / "views/mathlib")
        self.assertTrue(all(root.is_relative_to(run / "views/mathlib") for root in roots))
        self.assertFalse((run / "views/mathlib/atlas").exists())
        self.assertEqual(sorted(path.name for path in (run / "views/mathlib").iterdir()), ["mathlib"])

    def test_combined_root_holds_exactly_each_arms_sources(self) -> None:
        run = self.prepare_fixture()
        manifest = evaluation.verify_run(run)
        evaluation.configure_judge(run, manifest, self.upstream)
        rows = evaluation.read_json(run / "theorems.json")["rows"]
        atlas = next(row for row in rows if row["lib"] == "atlas")
        cwd, extras = self.upstream.judge.judge_dirs(atlas)
        combined = extras[evaluation.COMBINED_LABEL]
        self.assertEqual(cwd, combined / "atlas")
        self.assertEqual(sorted(path.name for path in combined.iterdir()), sorted(manifest["sources"]))
        self.assertEqual((combined / "atlas/MathlibExt/Fixture.lean").read_bytes(),
                         (run / "corpus/atlas/MathlibExt/Fixture.lean").read_bytes())
        trace = self.root / "trace.jsonl"
        granted = [str(path) for path in extras.values()]
        def check(path: Path) -> None:
            trace.write_text(json.dumps({"type": "system", "subtype": "init", "model": "test",
                "cwd": str(cwd), "claude_code_version": "1.0.0", "tools": ["Grep"],
                "additional_directories": granted}) + "\n" +
                json.dumps({"type": "assistant", "message": {"content": [{"type": "tool_use",
                    "name": "Grep", "input": {"path": str(path), "pattern": "atlas_a"}}]}}) + "\n")
            evaluation.validate_session_trace(trace, cwd, [cwd, *extras.values()], "test", "1.0.0")
        check(combined)
        for outside in (run / "views", run / "corpus", run):
            with self.assertRaisesRegex(ValueError, "outside"):
                check(outside)
        granted.append("/managed/preset")
        check(combined)
        for extra in (str(run / "judges"), str(run.parent)):
            granted.append(extra)
            with self.assertRaisesRegex(ValueError, "granted directories"):
                check(combined)
            granted.remove(extra)
        granted.remove(str(combined / "mathlib"))
        with self.assertRaisesRegex(ValueError, "granted directories"):
            check(combined)

    def test_extra_or_replaced_view_file_rejected(self) -> None:
        run = self.prepare_fixture()
        extra = run / "views/mathlib/atlas/MathlibExt/Fixture.lean"
        extra.parent.mkdir(parents=True)
        extra.write_text("theorem atlas_a : True := by trivial\n")
        with self.assertRaisesRegex(ValueError, "missing or extra"):
            evaluation.verify_run(run)
        extra.unlink()
        with self.assertRaisesRegex(ValueError, "missing or extra"):
            evaluation.verify_run(run)  # the now-empty directories remain
        extra.parent.rmdir()
        extra.parent.parent.rmdir()
        evaluation.verify_run(run)
        replaced = run / "views/atlas/mathlib/Mathlib/Fixture.lean"
        replaced.unlink()
        replaced.write_text("theorem changed : True := by trivial\n")
        with self.assertRaisesRegex(ValueError, "view changed"):
            evaluation.verify_run(run)

    def test_citation_normalization_is_recorded(self) -> None:
        run = self.prepare_fixture([["mathlib_a", "Mathlib.Fixture"], ["mathlib_old", "Mathlib.Fixture"]])
        row = next(row for row in evaluation.read_json(run / "theorems.json")["rows"] if row["lib"] == "atlas")
        protocol = run / "protocols/duplicates-mathlib-inclusive"
        verdict = {"verdict": "duplicate", "mathlib_declaration": "`mathlib_a` (theorem)",
                   "file": "Mathlib/Fixture.lean", "derivation": "mathlib_a",
                   "proof_uses_it": False, "explanation": "Annotated name fixture."}
        def check(**changes: str) -> evaluation.Row:
            return evaluation.validate_theorem({**verdict, **changes}, "duplicates-mathlib-inclusive",
                                               self.upstream, protocol, row)
        self.assertEqual(check(), {"citation_normalized": True})
        self.assertEqual(check(mathlib_declaration="mathlib_a"), {})
        self.assertEqual(check(mathlib_declaration="mathlib_a", file="Mathlib/Elsewhere.lean"),
                         {"citation_module_corrected": "Mathlib.Fixture"})
        with self.assertRaisesRegex(ValueError, "deprecated"):
            check(mathlib_declaration="mathlib_old", file="Mathlib/Elsewhere.lean")
        with self.assertRaisesRegex(ValueError, "deprecated"):
            check(mathlib_declaration="mathlib_old", file="Mathlib/Fixture.lean")
        with self.assertRaisesRegex(ValueError, "citation"):
            check(mathlib_declaration="mathlib_unindexed")
        for outside in ("/root/.elan/toolchains/lean/src/lean/Init/Core.lean",
                        str(run / "views/atlas/atlas/MathlibExt/Fixture.lean")):
            with self.assertRaisesRegex(ValueError, "outside the permitted"):
                check(mathlib_declaration="mathlib_a", file=outside)
        self.assertEqual(check(mathlib_declaration="mathlib_a",
                               file=str(run / "views/atlas/mathlib/Mathlib/Fixture.lean")), {})

    def test_positive_duplicate_report_survives_relocation(self) -> None:
        run = self.prepare_fixture()
        self.write_negative_results(run, "fixture")
        indicator, row = next(task for task in evaluation.selected_tasks(run, None, None)
                              if task[0] == "duplicates-mathlib-inclusive" and task[1]["lib"] == "atlas")
        path = evaluation.result_path(run, indicator, "fixture", row)
        result = evaluation.read_json(path)
        result.update(verdict="duplicate", mathlib_declaration="mathlib_a", derivation="mathlib_a",
                      file=str(run / "views/atlas/mathlib/Mathlib/Fixture.lean"), explanation="Fixture.")
        evaluation.write_json(path, result)
        moved = self.root / "relocated"
        run.rename(moved)
        evaluation.report(argparse.Namespace(run_dir=moved, label="fixture", require_complete=True))
        cell = evaluation.read_json(moved / "reports/fixture/summary.json")["cells"][
            f"{indicator}/{row['root']}/public"]
        self.assertEqual((cell["flagged"], cell["reproofs"], cell["citation_module_corrected"]), (1, 1, 0))

    def test_copy_fallback_when_hard_links_fail(self) -> None:
        original = Path.hardlink_to
        def refuse(self: Path, target: Path) -> None:
            raise OSError("cross-device link")
        Path.hardlink_to = refuse
        try:
            run = self.prepare_fixture()
        finally:
            Path.hardlink_to = original
        evaluation.verify_run(run)
        self.assertEqual((run / "views/atlas/atlas/MathlibExt/Fixture.lean").stat().st_nlink, 1)

    def test_lean_core_module_resolves_with_or_without_src(self) -> None:
        core = self.root / "lean-core"
        (core / "src/Init").mkdir(parents=True)
        (core / "src/Init/Core.lean").write_text("theorem core_fixture : True := trivial\n")
        self.assertEqual(evaluation.module_file("Init.Core", [core]), core / "src/Init/Core.lean")
        self.assertIsNone(evaluation.module_file("MathlibExt.Core", [core]))


if __name__ == "__main__":
    unittest.main()
