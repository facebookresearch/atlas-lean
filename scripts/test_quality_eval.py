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
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

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
        for path in ("Atlas/X.lean", "v1/X.lean", "WantedExt/X.lean", "MathlibExtTest/X.lean",
                     "CSLibExtTest/X.lean", "MathlibExt/Certificates/X.lean", "MathlibExt/README.md"):
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

    def prepare_fixture(self) -> Path:
        repo = self.root / "atlas"
        repo.mkdir()
        dependency = repo / ".lake" / "packages" / "mathlib"
        revision = self.make_repo(dependency, {"Mathlib/Fixture.lean":
            "theorem mathlib_a : True := by trivial\ntheorem mathlib_b : True := by trivial\n"
            "@[deprecated mathlib_a (since := \"2026-01-01\")]\ntheorem mathlib_old : True := by trivial\n"})
        self.make_repo(repo / "production", {"placeholder.lean": "-- unused\n"})
        for name, data in {
            "MathlibExt/Fixture.lean": "theorem atlas_a : True := by trivial\ntheorem atlas_b : True := by trivial\n",
            "CSLibExt/Empty.lean": "-- no declarations\n",
            "lake-manifest.json": json.dumps({"packagesDir": ".lake/packages", "packages": [
                {"name": "mathlib", "rev": revision, "url": "https://github.com/leanprover-community/mathlib4"}]}),
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
        evaluation.prepare(argparse.Namespace(repo=repo, run_dir=run, upstream=self.upstream_path,
                                             lean_core_repo=None, theorems=2, files=1, seed=0))
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
        run = self.prepare_fixture()
        row = next(row for row in evaluation.read_json(run / "theorems.json")["rows"] if row["lib"] == "atlas")
        evaluation.write_json(run / "compiled-declarations.json", [["generated_fixture", "Mathlib.Fixture"]])
        verdict = {"verdict": "duplicate", "mathlib_declaration": "generated_fixture",
                   "file": "Mathlib/Fixture.lean", "derivation": "by exact generated_fixture",
                   "proof_uses_it": False, "explanation": "Generated declaration fixture."}
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
        run = self.prepare_fixture()
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
        evaluation.write_json(run / "compiled-declarations.json", [
            ["mathlib_a", "Mathlib.Fixture"], ["mathlib_old", "Mathlib.Fixture"]])
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
