#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Shared validation counts and boundaries; external Lean and Lake are mocked."""

from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import optimize_imports as optimizer
from test_import_optimizer_cache import runtime_stubs
from test_import_optimizer_recovery import ORIGINAL, main_inputs


REAL_RUN_COMMAND = optimizer.run_command


class SharedValidationPhaseTests(unittest.TestCase):
    @staticmethod
    def tools(root: Path) -> optimizer.Tools:
        return optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                               Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 5,
                               root / "bin/time", root / ".lake/lakefile-lean-j2.toml")

    def test_populated_main_and_resume_validate_a_shared_bundle_in_linear_rows(self) -> None:
        for count in (2, 4, 8):
            with self.subTest(files=count), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                names = tuple(chr(ord("A") + index) for index in range(count))
                arguments = main_inputs(root, names) + ["--batch-size", str(count)]
                calls: Counter[str] = Counter()
                phase = ["main"]
                actual = optimizer.analysis_inputs

                def measured(tools: optimizer.Tools, rows: list[dict[str, object]],
                             *recorded: object) -> dict[str, object]:
                    calls[phase[0]] += len(rows)
                    return actual(tools, rows, *recorded)

                with runtime_stubs(root), patch.object(optimizer, "analysis_inputs", side_effect=measured), \
                        patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                    journal = root / "output/results.jsonl"
                    saved = journal.read_bytes()
                    rows = [json.loads(line) for line in saved.splitlines()]
                    self.assertEqual(len(rows), count)
                    self.assertEqual([row["status"] for row in rows], ["no_change"] * count)
                    self.assertTrue(all(row.get("proposal_receipt") for row in rows))
                    phase[0] = "resume"
                    with patch.object(sys, "argv", [*arguments, "--resume"]):
                        self.assertEqual(optimizer.main(), 0)
                    self.assertEqual(journal.read_bytes(), saved)
                    self.assertEqual(optimizer.read_json(root / "output/summary.json")["result_count"], count)
                print(json.dumps({"files": count, "full_row_checks": dict(calls)}))
                self.assertLessEqual(calls["main"], 5 * count)
                self.assertLessEqual(calls["resume"], 2 * count)

    def test_resume_rechecks_a_shared_dependency_edited_after_the_first_row(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B")) + ["--batch-size", "2"]
            dependency = root / "explicit-sibling-dependency"
            dependency.write_text("Original dependency input\n")
            setup = root / ".lake/build/ir/B.setup.json"
            metadata = optimizer.read_json(setup)
            metadata["importArts"]["Sibling"] = [[str(dependency)], []]
            optimizer.write_json(setup, metadata)
            with runtime_stubs(root), patch.object(sys, "argv", arguments):
                self.assertEqual(optimizer.main(), 0)
                saved = (root / "output/results.jsonl").read_bytes()
                actual = optimizer.verify_saved_no_change
                verified: list[str] = []

                def edit_after_first(result: dict[str, object], tools: optimizer.Tools) -> None:
                    actual(result, tools)
                    verified.append(str(result["path"]))
                    if result["path"] == "A.lean":
                        dependency.write_text("Changed dependency input\n")

                with patch.object(optimizer, "verify_saved_no_change", side_effect=edit_after_first), \
                        patch.object(sys, "argv", [*arguments, "--resume"]):
                    with self.assertRaises(ValueError):
                        optimizer.main()
                self.assertIn("A.lean", verified)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), saved)

    def test_native_boundary_revalidates_before_a_real_marker_child(self) -> None:
        for mutation in (False, True):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = main_inputs(root, ("A", "B"))
                actual_run = optimizer.Tools.run
                with runtime_stubs(root), patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                    result = json.loads((root / "output/results.jsonl").read_text().splitlines()[0])
                    tools = self.tools(root)
                    marker = root / "real-python-child-marker"
                    argv = [sys.executable, "-B", "-c",
                            "from pathlib import Path; Path(" + repr(str(marker)) + ").write_text('child ran')"]
                    with patch.object(optimizer.Tools, "run", actual_run), \
                            patch.object(optimizer, "run_command", REAL_RUN_COMMAND):
                        if mutation:
                            with self.assertRaises(ValueError):
                                with optimizer.analysis_validation_phase(tools):
                                    optimizer.verify_saved_no_change(result, tools)
                                    (root / "B.lean").write_bytes(ORIGINAL + b"-- edited before child\n")
                                    tools.run(argv, root / "output/real-child")
                            self.assertFalse(marker.exists())
                        else:
                            with optimizer.analysis_validation_phase(tools):
                                optimizer.verify_saved_no_change(result, tools)
                                command = tools.run(argv, root / "output/real-child")
                                optimizer.require_success(command)
                                self.assertEqual(marker.read_text(), "child ran")
                                optimizer.verify_saved_no_change(result, tools)
                        self.assertEqual(tools.validated_analysis_inputs, {})

    def test_fresh_batch_does_not_journal_after_a_late_shared_dependency_edit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B"))
            dependency = root / "late-shared-dependency"
            dependency.write_text("Original dependency input\n")
            setup = root / ".lake/build/ir/B.setup.json"
            metadata = optimizer.read_json(setup)
            metadata["importArts"]["Sibling"] = [[str(dependency)], []]
            optimizer.write_json(setup, metadata)
            actual = optimizer.verify_saved_no_change
            checked: list[str] = []

            def edit_after_last(result: dict[str, object], tools: optimizer.Tools) -> None:
                actual(result, tools)
                checked.append(str(result["path"]))
                if result["path"] == "B.lean":
                    dependency.write_text("Changed dependency input\n")

            with runtime_stubs(root), patch.object(sys, "argv", arguments), \
                    patch.object(optimizer, "verify_saved_no_change", side_effect=edit_after_last):
                with self.assertRaises(ValueError):
                    optimizer.main()
            self.assertEqual(checked, ["A.lean", "B.lean"])
            self.assertEqual((root / "output/results.jsonl").read_bytes(), b"")

    def test_a_mutated_shared_bundle_cannot_reuse_its_prior_validation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B"))
            with runtime_stubs(root), patch.object(sys, "argv", arguments):
                self.assertEqual(optimizer.main(), 0)
                result = json.loads((root / "output/results.jsonl").read_text().splitlines()[0])
                receipt = optimizer.read_json(Path(result["proposal_receipt"]["path"]))
                inputs = receipt["analysis"]["inputs"]
                tools = self.tools(root)
                with optimizer.analysis_validation_phase(tools):
                    self.assertEqual(len(optimizer.verify_shake_inputs(tools, inputs)), 2)
                    inputs["compiled_inputs"]["B.lean"]["setup"] = inputs["compiled_inputs"]["A.lean"]["setup"]
                    with self.assertRaisesRegex(ValueError, "Inventory module differs from its source path"):
                        optimizer.verify_shake_inputs(tools, inputs)
                self.assertEqual(tools.validated_analysis_inputs, {})

    def test_direct_validation_does_not_keep_a_phase_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B"))
            with runtime_stubs(root), patch.object(sys, "argv", arguments):
                self.assertEqual(optimizer.main(), 0)
                result = json.loads((root / "output/results.jsonl").read_text().splitlines()[0])
                tools = self.tools(root)
                optimizer.verify_saved_no_change(result, tools)
                (root / "B.lean").write_bytes(ORIGINAL + b"-- edited after standalone validation\n")
                with self.assertRaises(ValueError):
                    optimizer.verify_saved_no_change(result, tools)


if __name__ == "__main__":
    unittest.main()
