#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Phase-scoped shared evidence with real files and mocked Lean commands."""

from __future__ import annotations

import contextlib
import json
import sys
import unittest
from collections import Counter
from collections.abc import Iterator
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_snapshot_groups as groups


REAL_RUN_COMMAND = optimizer.run_command


class SnapshotGroupValidationCacheTests(unittest.TestCase):
    @contextlib.contextmanager
    def capture(self) -> Iterator[tuple[Path, dict[str, dict[str, object]], optimizer.Tools]]:
        with groups.GroupedSnapshotTests().capture() as (root, _, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                            optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            for result in results.values():
                self.assertNotIn("shared_snapshot_failure", result)
                for arm in ("baseline", "candidate"):
                    self.assertIn("snapshot_group", result[arm])
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 5,
                                    root / "bin/time", root / ".lake/lakefile-lean-j2.toml")
            yield root, results, tools

    @staticmethod
    def changed_path(results: dict[str, dict[str, object]], fault: str) -> Path:
        arm = results["A.lean"]["baseline"]
        neighbor = results["B.lean"]["baseline"]
        if fault == "receipt":
            return Path(arm["snapshot_group"]["path"])
        if fault == "setup":
            return Path(arm["snapshot_setup"]["path"])
        if fault == "source":
            return Path(neighbor["source_path"])
        if fault == "private":
            return Path(neighbor["artifact_root"]) / "B.olean.private"
        if fault == "dependency":
            return Path(arm["snapshot_dependencies"][1]["stdout"]["path"])
        return Path(arm["snapshot_command_evidence"]["stdout"]["path"])

    def test_shared_group_members_setup_and_output_are_checked_once_per_phase(self) -> None:
        for repetitions in (1, 3):
            with self.subTest(repetitions=repetitions), self.capture() as (_, results, tools):
                reads: Counter[str] = Counter()
                actual = optimizer.read_analysis

                def measured(current: optimizer.Tools, evidence: object) -> tuple[dict[str, object], str]:
                    reads[evidence["kind"]] += 1
                    return actual(current, evidence)

                with patch.object(optimizer, "verify_snapshot_group_member",
                                  wraps=optimizer.verify_snapshot_group_member) as members, \
                        patch.object(optimizer, "snapshot_setup_value",
                                     wraps=optimizer.snapshot_setup_value) as setups, \
                        patch.object(optimizer, "read_analysis", side_effect=measured):
                    with optimizer.analysis_validation_phase(tools):
                        for _ in range(repetitions):
                            for result in results.values():
                                optimizer.verify_saved_candidate(result, tools.output, tools)
                        observed = {"members": members.call_count, "setups": setups.call_count,
                                    "snapshot_reads": reads["snapshot"], "row_visits": 2 * repetitions}
                        print(json.dumps(observed), file=sys.__stdout__)
                        self.assertEqual(observed["members"], 4)
                        self.assertEqual(observed["setups"], 2)
                        self.assertEqual(observed["snapshot_reads"], 2)
                    self.assertEqual(members.call_count, 8)
                    self.assertEqual(setups.call_count, 4)
                    self.assertEqual(reads["snapshot"], 4)

    def test_phase_close_rejects_a_late_receipt_setup_or_member_edit(self) -> None:
        for fault in ("receipt", "setup", "source", "private", "dependency", "snapshot"):
            with self.subTest(fault=fault), self.capture() as (_, results, tools):
                with self.assertRaises(ValueError):
                    with optimizer.analysis_validation_phase(tools):
                        optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)
                        target = self.changed_path(results, fault)
                        target.write_bytes(b"x" * target.stat().st_size)

    def test_new_phase_rejects_changed_receipt_setup_and_neighbor_bytes(self) -> None:
        for fault in ("receipt", "setup", "source", "private", "dependency", "snapshot"):
            with self.subTest(fault=fault), self.capture() as (_, results, tools):
                with optimizer.analysis_validation_phase(tools):
                    optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)
                target = self.changed_path(results, fault)
                target.write_bytes(b"x" * target.stat().st_size)
                with self.assertRaises(ValueError):
                    with optimizer.analysis_validation_phase(tools):
                        optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)

    def test_repinned_shared_evidence_cannot_erase_an_earlier_phase_obligation(self) -> None:
        for field in ("snapshot_group", "snapshot_setup"):
            with self.subTest(field=field), self.capture() as (_, results, tools):
                with self.assertRaisesRegex(ValueError, "Saved evidence file changed"):
                    with optimizer.analysis_validation_phase(tools):
                        optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)
                        changed = deepcopy(results["B.lean"])
                        arm = changed["baseline"]
                        target = Path(arm[field]["path"])
                        target.write_bytes(target.read_bytes() + b" ")
                        arm[field] = optimizer.file_pin(target)
                        optimizer.verify_saved_candidate(changed, tools.output, tools)

    def test_cached_group_still_checks_the_current_row_arm_association(self) -> None:
        for fault in ("compilation", "inputs", "dependencies", "contexts"):
            with self.subTest(fault=fault), self.capture() as (root, results, tools):
                with optimizer.analysis_validation_phase(tools):
                    optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)
                    changed = deepcopy(results["B.lean"])
                    arm = changed["baseline"]
                    if fault == "compilation":
                        arm["unaccepted_compilation_field"] = "not in the pinned group"
                    elif fault == "inputs":
                        arm["snapshot_input_manifest"] = results["A.lean"]["baseline"]["snapshot_input_manifest"]
                    elif fault == "dependencies":
                        arm["snapshot_dependencies"].reverse()
                    else:
                        setup = optimizer.read_json(Path(arm["snapshot_setup"]["path"]))
                        self.assertNotEqual(setup["snapshot_compilations"]["A.lean"]["artifact_root"],
                                            arm["artifact_root"])
                        setup["snapshot_compilations"]["A.lean"]["artifact_root"] = arm["artifact_root"]
                        path = root / "output/changed-group-setup.json"
                        optimizer.write_json(path, setup)
                        arm["snapshot_setup"] = optimizer.file_pin(path)
                    message = "compilation inputs changed" if fault == "contexts" else "."
                    with self.assertRaisesRegex(ValueError, message):
                        optimizer.verify_saved_candidate(changed, tools.output, tools)

    def test_real_child_does_not_run_after_a_cached_neighbor_artifact_edit(self) -> None:
        with self.capture() as (root, results, tools):
            marker = root / "real-child-marker"
            argv = [sys.executable, "-B", "-c",
                    "from pathlib import Path; Path(" + repr(str(marker)) + ").write_text('ran')"]
            with patch.object(optimizer, "run_command", REAL_RUN_COMMAND):
                with self.assertRaises(ValueError):
                    with optimizer.analysis_validation_phase(tools):
                        optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)
                        target = self.changed_path(results, "private")
                        target.write_bytes(b"x" * target.stat().st_size)
                        tools.run(argv, tools.output / "real-child")
            self.assertFalse(marker.exists())

    def test_real_child_clears_shared_validation_before_the_next_candidate(self) -> None:
        with self.capture() as (root, results, tools):
            marker = root / "real-child-marker"
            argv = [sys.executable, "-B", "-c",
                    "from pathlib import Path; Path(" + repr(str(marker)) + ").write_text('ran')"]
            with patch.object(optimizer, "verify_snapshot_group_member",
                              wraps=optimizer.verify_snapshot_group_member) as members, \
                    patch.object(optimizer, "run_command", REAL_RUN_COMMAND):
                with optimizer.analysis_validation_phase(tools):
                    optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)
                    self.assertEqual(members.call_count, 4)
                    optimizer.require_success(tools.run(argv, tools.output / "real-child"))
                    self.assertEqual(marker.read_text(), "ran")
                    self.assertEqual(members.call_count, 8)
                    optimizer.verify_saved_candidate(results["B.lean"], tools.output, tools)
                    self.assertEqual(members.call_count, 12)
                self.assertEqual(members.call_count, 16)

    def test_direct_validation_does_not_reuse_a_group_after_neighbor_mutation(self) -> None:
        with self.capture() as (_, results, tools):
            optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)
            target = self.changed_path(results, "private")
            target.write_bytes(b"x" * target.stat().st_size)
            with self.assertRaises(ValueError):
                optimizer.verify_saved_candidate(results["A.lean"], tools.output, tools)


if __name__ == "__main__":
    unittest.main()
