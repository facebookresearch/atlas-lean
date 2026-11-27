#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Initial Shake failures through the real CLI with mocked native commands."""

from __future__ import annotations

import contextlib
import json
import unittest
from collections.abc import Callable, Iterator
from pathlib import Path
from typing import cast
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_snapshot_groups as groups


class InitialAnalysisFallbackTests(unittest.TestCase):
    @contextlib.contextmanager
    def capture(self, *, snapshot_fault: str = "", failing_owner: str = "",
                joint_failure: bool = True, changed_inputs: bool = False
                ) -> Iterator[tuple[Path, list[dict[str, object]], Callable[[bool], int]]]:
        with groups.GroupedSnapshotTests().capture(snapshot_fault) as (root, calls, invoke):
            external = optimizer.run_command

            def analyze(argv: list[str], cwd: Path, label: Path,
                        environment: dict[str, str], timeout: int) -> dict[str, object]:
                command = external(argv, cwd, label, environment, timeout)
                if "shake" not in argv:
                    return command
                modules = [argv[index + 1] for index, word in enumerate(argv) if word == "--only"]
                self.assertTrue(modules)
                failed = (joint_failure and len(modules) > 1) or modules == [failing_owner]
                stdout, stderr = Path(str(command["stdout"])), Path(str(command["stderr"]))
                stdout.write_text("" if failed else "".join(
                    f"{module}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                    for module in modules))
                stderr.write_text("error: import B failed, environment already contains 'Fixture.shared' from A\n"
                                  if failed else "")
                command["exit_code"] = 1 if failed else 0
                optimizer.write_json(Path(str(label) + ".json"), command)
                if changed_inputs and len(modules) > 1:
                    (cwd / ".lake/build/lib/lean/A.olean").write_bytes(b"Changed original compiled input\n")
                return command

            with patch.object(optimizer, "run_command", side_effect=analyze):
                yield root, calls, cast(Callable[[bool], int], invoke)

    @staticmethod
    def rows(root: Path) -> dict[str, dict[str, object]]:
        identity = optimizer.read_json(root / "output/run.json")
        return optimizer.read_journal(root / "output/results.jsonl", identity["sources"])

    @staticmethod
    def selected(call: dict[str, object]) -> list[str]:
        argv = cast(list[str], call["argv"])
        return [argv[index + 1] for index, word in enumerate(argv) if word == "--only"]

    def assert_individual_proposal(self, result: dict[str, object]) -> None:
        self.assertEqual(result["status"], "verified")
        self.assertEqual(result["removed_imports"], ["import Mathlib"])
        self.assertEqual(result["added_imports"], ["import Init"])
        receipt = cast(dict[str, object], result["proposal_receipt"])
        proposal = optimizer.read_json(Path(str(receipt["path"])))
        analysis = proposal["analysis"]
        self.assertEqual(analysis["kind"], "shake")
        self.assertEqual(set(analysis["inputs"]["sources"]), {result["path"]})
        self.assertEqual(set(analysis["inputs"]["compiled_inputs"]), {result["path"]})

    def assert_failed_analysis_bound(self, result: dict[str, object], call: dict[str, object]) -> None:
        failure = result["shared_analysis_failure"]
        self.assertEqual(failure["error"], "Shake reported an error")
        evidence = failure["evidence"]
        self.assertEqual(evidence["kind"], "shake")
        self.assertEqual(set(evidence["inputs"]["sources"]), {"A.lean", "B.lean"})
        for suffix in ("json", "stdout", "stderr"):
            path = Path(str(call["label"]) + "." + suffix)
            self.assertEqual(evidence[suffix], optimizer.file_pin(path))

    def test_joint_analysis_then_snapshot_failure_retries_each_owner_and_resumes(self) -> None:
        with self.capture(snapshot_fault="joint") as (root, calls, invoke):
            self.assertEqual(invoke(False), 0)
            shake = [call for call in calls if "shake" in call["argv"]]
            self.assertEqual([self.selected(call) for call in shake], [["A", "B"], ["A"], ["B"]])
            self.assertEqual(len([call for call in calls if "build" in call["argv"]]), 1)
            self.assertEqual(len([call for call in calls if call["argv"][0] == str(root / "bin/time")]), 4)
            snapshots = [call for call in calls if "--run" in call["argv"]]
            self.assertEqual([call["argv"][call["argv"].index("--run") + 3:] for call in snapshots],
                             [["A", "B"], ["A"], ["A"], ["B"], ["B"]])
            results = self.rows(root)
            self.assertEqual(list(results), ["A.lean", "B.lean"])
            for result in results.values():
                self.assert_individual_proposal(result)
                self.assert_failed_analysis_bound(result, shake[0])
                self.assertIn("shared_snapshot_failure", result)
                for arm in ("baseline", "candidate"):
                    self.assertNotIn("snapshot_group", result[arm])
                    self.assertEqual(len(result[arm]["artifacts"]), 7)
            failed = Path(str(shake[0]["label"]))
            self.assertEqual(optimizer.read_json(failed.with_suffix(".json"))["exit_code"], 1)
            self.assertIn("Fixture.shared", failed.with_suffix(".stderr").read_text())
            retained = {failed.with_suffix(suffix): failed.with_suffix(suffix).read_bytes()
                        for suffix in (".json", ".stdout", ".stderr")}
            journal, before_calls = (root / "output/results.jsonl").read_bytes(), list(calls)
            self.assertEqual(invoke(True), 0)
            self.assertEqual(calls, before_calls)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
            self.assertEqual({path: path.read_bytes() for path in retained}, retained)

    def test_persistent_individual_analysis_failure_blocks_only_that_owner(self) -> None:
        with self.capture(failing_owner="B") as (root, calls, invoke):
            self.assertEqual(invoke(False), 1)
            shake = [call for call in calls if "shake" in call["argv"]]
            self.assertEqual([self.selected(call) for call in shake], [["A", "B"], ["A"], ["B"]])
            results = self.rows(root)
            self.assert_individual_proposal(results["A.lean"])
            for result in results.values():
                self.assert_failed_analysis_bound(result, shake[0])
            self.assertEqual(results["B.lean"]["status"], "blocked")
            self.assertIn("Shake reported an error", results["B.lean"]["error"])
            self.assertNotIn("baseline", results["B.lean"])
            self.assertEqual(len([call for call in calls if call["argv"][0] == str(root / "bin/time")]), 2)
            self.assertEqual(len([call for call in calls if "--run" in call["argv"]]), 2)
            for call in (shake[0], shake[2]):
                self.assertEqual(optimizer.read_json(Path(str(call["label"]) + ".json"))["exit_code"], 1)
            journal, before_calls = (root / "output/results.jsonl").read_bytes(), list(calls)
            self.assertEqual(invoke(True), 1)
            self.assertEqual(calls, before_calls)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_changed_joint_analysis_inputs_do_not_trigger_individual_retries(self) -> None:
        with self.capture(changed_inputs=True) as (root, calls, invoke):
            self.assertEqual(invoke(False), 1)
            self.assertEqual([self.selected(call) for call in calls if "shake" in call["argv"]], [["A", "B"]])
            results = self.rows(root)
            self.assertEqual([row["status"] for row in results.values()], ["blocked", "blocked"])
            for result in results.values():
                self.assertEqual(result["error"], "Compiled inputs changed during Shake analysis")
                self.assertNotIn("shared_analysis_failure", result)
            self.assertFalse(any("--run" in call["argv"] for call in calls))
            self.assertFalse(any(call["argv"][0] == str(root / "bin/time") for call in calls))

    def test_resume_rejects_changed_failed_or_individual_analysis_without_new_native_work(self) -> None:
        for modules in (["A", "B"], ["A"]):
            with self.subTest(modules=modules), self.capture() as (root, calls, invoke):
                self.assertEqual(invoke(False), 0)
                results = self.rows(root)
                self.assert_individual_proposal(results["A.lean"])
                call = next(call for call in calls if "shake" in call["argv"] and self.selected(call) == modules)
                path = Path(str(call["label"]) + ".json")
                command = optimizer.read_json(path)
                command["argv"][-1] = "A" if len(modules) > 1 else "B"
                optimizer.write_json(path, command)
                journal, before_calls = (root / "output/results.jsonl").read_bytes(), list(calls)
                with self.assertRaises(ValueError):
                    invoke(True)
                self.assertEqual(calls, before_calls)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_successful_joint_analysis_keeps_shared_snapshot_path(self) -> None:
        with self.capture(joint_failure=False) as (root, calls, invoke):
            self.assertEqual(invoke(False), 0)
            self.assertEqual([self.selected(call) for call in calls if "shake" in call["argv"]], [["A", "B"]])
            results = self.rows(root)
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            for result in results.values():
                self.assertNotIn("shared_analysis_failure", result)
                self.assertNotIn("shared_snapshot_failure", result)
                for arm in ("baseline", "candidate"):
                    self.assertIn("snapshot_group", result[arm])
            self.assertEqual(len([call for call in calls if "--run" in call["argv"]]), 2)
            before_calls = list(calls)
            self.assertEqual(invoke(True), 0)
            self.assertEqual(calls, before_calls)

    def test_resume_rejects_erased_failed_analysis_binding(self) -> None:
        with self.capture() as (root, calls, invoke):
            self.assertEqual(invoke(False), 0)
            results = self.rows(root)
            self.assert_individual_proposal(results["A.lean"])
            results["A.lean"].pop("shared_analysis_failure")
            journal = root / "output/results.jsonl"
            journal.write_text("".join(json.dumps(row) + "\n" for row in results.values()))
            self.assertEqual(self.rows(root), results)
            before_calls, altered_journal = list(calls), journal.read_bytes()
            with self.assertRaises(ValueError):
                invoke(True)
            self.assertEqual(calls, before_calls)
            self.assertEqual(journal.read_bytes(), altered_journal)


if __name__ == "__main__":
    unittest.main()
