#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Shake cache tests; external Lean/Lake calls are mocked."""

from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_evidence as evidence
from test_import_optimizer_recovery import main_inputs


class CompiledAnalysisInputTests(unittest.TestCase):
    def fixture(self, root: Path, names: tuple[str, ...] = ("A",)):
        arguments = main_inputs(root, names)
        dependencies = root / "dependencies"
        dependencies.mkdir()
        for name in ("Shared.olean", "library.so", "plugin.so"):
            (dependencies / name).write_bytes(b"Mock dependency bytes, never executed\n")
        library = root / "sysroot/lib/lean"
        library.mkdir(parents=True)
        (library / "Init.ir").write_bytes(b"Mock standard-library bytes\n")
        binary = root / "sysroot/bin"
        binary.mkdir()
        for name in ("lean", "lake"):
            (binary / name).write_bytes((root / "bin" / name).read_bytes())
        artifacts = root / ".lake/build/lib/lean"
        artifacts.mkdir(parents=True)
        for name in names:
            for suffix in optimizer.ARTIFACT_SUFFIXES:
                (artifacts / (name + suffix)).write_bytes(b"Mock compiled target bytes\n")
            setup = root / ".lake/build/ir" / (name + ".setup.json")
            metadata = optimizer.read_json(setup)
            metadata["importArts"]["Shared"] = [[str(dependencies / "Shared.olean")], []]
            metadata["dynlibs"] = [str(dependencies / "library.so")]
            metadata["plugins"] = [{"path": str(dependencies / "plugin.so")}]
            optimizer.write_json(setup, metadata)
        return arguments

    def tools(self, root: Path) -> optimizer.Tools:
        config = root / ".lake/lakefile-lean-j2.toml"
        return optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                               root, {"LEAN_SYSROOT": str(root / "sysroot")}, 5,
                               time_binary=root / "bin/time",
                               lake_config=config if config.exists() else None)

    def mutate(self, root: Path, kind: str) -> None:
        paths = {
            "target": root / ".lake/build/lib/lean/A.olean",
            "private": root / ".lake/build/lib/lean/A.olean.private",
            "references": root / ".lake/build/lib/lean/A.ilean",
            "dependency": root / "dependencies/Shared.olean",
            "dynlib": root / "dependencies/library.so",
            "plugin": root / "dependencies/plugin.so",
            "stdlib": root / "sysroot/lib/lean/Init.ir",
        }
        if kind == "setup":
            setup = root / ".lake/build/ir/A.setup.json"
            metadata = optimizer.read_json(setup)
            metadata["options"] = {"maxRecDepth": 2048}
            optimizer.write_json(setup, metadata)
        else:
            paths[kind].write_bytes(paths[kind].read_bytes().replace(b"Mock", b"Edit", 1))

    def test_cache_refreshes_after_compiled_target_setup_or_dependency_changes(self) -> None:
        for kind in ("target", "private", "references", "setup", "dependency", "dynlib", "plugin", "stdlib"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                self.fixture(root)
                rows = [json.loads((root / "manifest.jsonl").read_text())]
                headers = {"A.lean": json.loads((root / "headers.jsonl").read_text())}
                calls: list[Path] = []
                actual_artifacts = optimizer.artifact_receipt
                with evidence.AnalysisResumeTests().external_cli(root, {"A"}, calls), \
                        patch.object(optimizer, "artifact_receipt", wraps=actual_artifacts):
                    tools = self.tools(root)
                    optimizer.analyze_batch(tools, rows, headers, root / "output/batches/0")
                    optimizer.analyze_batch(tools, rows, headers, root / "output/batches/0")
                    self.assertEqual(len(calls), 1, "Unchanged compiled inputs must reuse analysis")
                    old_output = calls[0].read_bytes()
                    self.mutate(root, kind)
                    optimizer.analyze_batch(self.tools(root), rows, headers, root / "output/batches/0")
                self.assertEqual(len(calls), 2, "Rebuilt inputs must run a fresh Shake analysis")
                self.assertNotEqual(calls[0], calls[1])
                self.assertEqual(calls[0].read_bytes(), old_output)

    def test_completed_no_change_rejects_rebuilt_compiled_inputs(self) -> None:
        for kind in ("target", "private", "references", "setup", "dependency", "dynlib", "plugin", "stdlib"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = self.fixture(root)
                calls: list[Path] = []
                actual_artifacts = optimizer.artifact_receipt
                with patch.dict(os.environ, {"LEAN_SYSROOT": str(root / "sysroot")}), \
                        evidence.AnalysisResumeTests().external_cli(root, {"A"}, calls), \
                        patch.object(optimizer, "artifact_receipt", wraps=actual_artifacts):
                    self.assertEqual(evidence.AnalysisResumeTests().invoke(arguments), 0)
                    journal = (root / "output/results.jsonl").read_bytes()
                    self.assertEqual(json.loads(journal)["status"], "no_change")
                    self.mutate(root, kind)
                    with self.assertRaises(ValueError):
                        evidence.AnalysisResumeTests().invoke([*arguments, "--resume"])
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
                self.assertEqual(len(calls), 1)

    def test_subset_cache_refresh_preserves_old_full_pass_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.fixture(root, ("A", "B"))
            rows = [json.loads(line) for line in (root / "manifest.jsonl").read_text().splitlines()]
            headers = {row["relative_path"]: row for row in
                       (json.loads(line) for line in (root / "headers.jsonl").read_text().splitlines())}
            calls = []
            actual_artifacts = optimizer.artifact_receipt
            with evidence.AnalysisResumeTests().external_cli(root, {"A", "B"}, calls), \
                    patch.object(optimizer, "artifact_receipt", wraps=actual_artifacts):
                batch = root / "output/batches/0"
                full = optimizer.analyze_batch(self.tools(root), rows, headers, batch)
                old = calls[0].read_bytes()
                old_evidence = full["A.lean"].evidence
                self.assertEqual(len(calls), 1)
                subset = optimizer.analyze_batch(self.tools(root), rows[:1], headers, batch)
                self.assertEqual(subset["A.lean"].evidence, old_evidence)
                self.assertEqual(len(calls), 1)
                (root / ".lake/build/lib/lean/B.olean").write_bytes(b"Rebuilt shared input\n")
                refreshed = optimizer.analyze_batch(self.tools(root), rows[:1], headers, batch)
            self.assertEqual(len(calls), 2)
            self.assertEqual(calls[0].read_bytes(), old)
            self.assertNotEqual(refreshed["A.lean"].evidence, old_evidence)
            self.assertEqual(set(refreshed["A.lean"].evidence["inputs"]["sources"]), {"A.lean"})

    def test_shake_cannot_journal_a_result_if_its_compiled_inputs_change(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = self.fixture(root)
            calls: list[Path] = []
            actual_artifacts = optimizer.artifact_receipt
            with patch.dict(os.environ, {"LEAN_SYSROOT": str(root / "sysroot")}), \
                    evidence.AnalysisResumeTests().external_cli(root, {"A"}, calls), \
                    patch.object(optimizer, "artifact_receipt", wraps=actual_artifacts):
                external = optimizer.Tools.run

                def changed(argv, label, environment=None):
                    command = external(argv, label, environment)
                    if "shake" in argv:
                        self.mutate(root, "target")
                    return command

                with patch.object(optimizer.Tools, "run", side_effect=changed):
                    self.assertEqual(evidence.AnalysisResumeTests().invoke(arguments), 1)
            self.assertEqual(json.loads((root / "output/results.jsonl").read_text())["status"], "blocked")
            self.assertFalse((root / "output/batches/0/analysis.json").exists())

    def test_rebuilt_shared_target_invalidates_every_saved_row(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = self.fixture(root, ("A", "B"))
            actual_artifacts = optimizer.artifact_receipt
            with patch.dict(os.environ, {"LEAN_SYSROOT": str(root / "sysroot")}), \
                    evidence.AnalysisResumeTests().external_cli(root, {"A", "B"}, []), \
                    patch.object(optimizer, "artifact_receipt", wraps=actual_artifacts):
                self.assertEqual(evidence.AnalysisResumeTests().invoke(arguments), 0)
            rows = [json.loads(line) for line in (root / "output/results.jsonl").read_text().splitlines()]
            self.assertEqual({row["status"] for row in rows}, {"no_change"})
            (root / ".lake/build/lib/lean/B.olean").write_bytes(b"Rebuilt unrelated target\n")
            for row in rows:
                with self.assertRaises(ValueError):
                    optimizer.verify_saved_no_change(row, self.tools(root))

    def test_rebuilt_target_outside_the_original_pass_keeps_saved_row_valid(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = self.fixture(root, ("A", "B"))
            actual_artifacts = optimizer.artifact_receipt
            with patch.dict(os.environ, {"LEAN_SYSROOT": str(root / "sysroot")}), \
                    evidence.AnalysisResumeTests().external_cli(root, {"A"}, []), \
                    patch.object(optimizer, "artifact_receipt", wraps=actual_artifacts):
                self.assertEqual(evidence.AnalysisResumeTests().invoke([*arguments, "A.lean"]), 0)
            row = json.loads((root / "output/results.jsonl").read_text())
            (root / ".lake/build/lib/lean/B.olean").write_bytes(b"Rebuilt outside-pass target\n")
            optimizer.verify_saved_no_change(row, self.tools(root))

    def test_edited_shared_source_or_setup_invalidates_saved_no_change_row(self) -> None:
        for kind in ("source", "setup"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = self.fixture(root, ("A", "B"))
                actual_artifacts = optimizer.artifact_receipt
                with patch.dict(os.environ, {"LEAN_SYSROOT": str(root / "sysroot")}), \
                        evidence.AnalysisResumeTests().external_cli(root, {"A", "B"}, []), \
                        patch.object(optimizer, "artifact_receipt", wraps=actual_artifacts):
                    self.assertEqual(evidence.AnalysisResumeTests().invoke(arguments), 0)
                row = json.loads((root / "output/results.jsonl").read_text().splitlines()[0])
                optimizer.verify_saved_no_change(row, self.tools(root))
                if kind == "source":
                    source = root / "B.lean"
                    source.write_bytes(source.read_bytes() + b"-- changed participating source\n")
                else:
                    setup = root / ".lake/build/ir/B.setup.json"
                    metadata = optimizer.read_json(setup)
                    metadata["options"] = {"maxRecDepth": 4096}
                    optimizer.write_json(setup, metadata)
                with self.assertRaises(ValueError):
                    optimizer.verify_saved_no_change(row, self.tools(root))

    def test_canonical_analysis_artifacts_cache_hashes_and_rehash_same_size_edits(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.fixture(root, ("A", "B", "C", "D"))
            rows = [json.loads(line) for line in (root / "manifest.jsonl").read_text().splitlines()]
            tools = self.tools(root)
            artifacts = root / ".lake/build/lib/lean"
            counts = {path: 0 for path in artifacts.iterdir()}
            actual = optimizer.sha256

            def counted(path: Path) -> str:
                if path in counts:
                    counts[path] += 1
                return actual(path)

            with patch.object(optimizer, "sha256", side_effect=counted):
                inputs = optimizer.analysis_inputs(tools, rows)
                self.assertEqual(len(counts), 28)
                self.assertEqual(set(counts.values()), {1})
                for row in rows:
                    optimizer.verify_shake_inputs(tools, inputs)
                self.assertEqual(set(counts.values()), {1})
                changed = artifacts / "B.olean"
                metadata = changed.stat()
                original = changed.read_bytes()
                changed.write_bytes(original.replace(b"Mock", b"Edit", 1))
                os.utime(changed, ns=(metadata.st_atime_ns, metadata.st_mtime_ns))
                self.assertEqual(changed.stat().st_size, metadata.st_size)
                with self.assertRaisesRegex(ValueError, "proposal inputs changed"):
                    optimizer.verify_shake_inputs(tools, inputs)
                self.assertEqual(counts[changed], 2)
                self.assertEqual(sum(counts.values()), 29)
                refreshed = optimizer.analysis_inputs(tools, rows)
                optimizer.verify_shake_inputs(tools, refreshed)
                self.assertEqual(sum(counts.values()), 29)
                optimizer.artifact_receipt(artifacts, Path("A.lean"), require_c=True)
                self.assertEqual(sum(counts.values()), 36)


if __name__ == "__main__":
    unittest.main()
