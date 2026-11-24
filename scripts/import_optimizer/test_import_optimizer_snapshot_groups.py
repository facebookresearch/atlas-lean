#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Grouped snapshots with physical compiler outputs and mocked native commands."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from collections.abc import Iterator
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery


class GroupedSnapshotTests(unittest.TestCase):
    @unittest.skipUnless(sys.platform == "linux", "Linux sibling guards require inotify")
    def test_group_accepts_unrelated_ancestor_siblings_during_each_child(self) -> None:
        for phase in ("--deps", "--run"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                ancestor = Path(directory).resolve() / "temporary"
                ancestor.mkdir()
                with patch.object(tempfile, "tempdir", str(ancestor)), self.capture() as (root, calls, invoke):
                    original = optimizer.run_command.side_effect
                    events: list[Path] = []

                    def external(argv: list[str], *args: object, **kwargs: object) -> dict[str, object]:
                        command = original(argv, *args, **kwargs)
                        if phase in argv:
                            sibling = ancestor / ("unrelated-" + str(len(events)))
                            sibling.mkdir()
                            events.append(sibling)
                        return command

                    with patch.object(optimizer, "run_command", side_effect=external):
                        self.assertEqual(invoke(), 0)
                    results = [json.loads(line) for line in (root / "output/results.jsonl").read_text().splitlines()]
                    self.assertEqual([result["status"] for result in results], ["verified", "verified"])
                    self.assertEqual([result["declaration_count"] for result in results], [1, 1])
                    self.assertTrue(all(result[arm].get("snapshot_group")
                                        for result in results for arm in ("baseline", "candidate")))
                    self.assertEqual(len(events), 4 if phase == "--deps" else 2)

    @contextlib.contextmanager
    def capture(self, fault: str = "", loaded_entry: object = None
                ) -> Iterator[tuple[Path, list[dict[str, object]], object]]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = recovery.main_inputs(root, ("B", "A"))
            canonical = root / ".lake/build/lib/lean"
            for module in ("B", "A"):
                outputs.physical_parts(canonical, Path(module + ".lean"))
            if fault == "conflict":
                setup = root / ".lake/build/ir/A.setup.json"
                metadata = optimizer.read_json(setup)
                alternate = root / "alternate-Mathlib.olean"
                alternate.write_bytes(b"Different original dependency artifact\n")
                metadata["importArts"]["Mathlib"] = [[str(alternate)], []]
                optimizer.write_json(setup, metadata)
            calls: list[dict[str, object]] = []

            def external(argv: list[str], cwd: Path, label: Path,
                         environment: dict[str, str], timeout: int) -> dict[str, object]:
                label.parent.mkdir(parents=True, exist_ok=True)
                stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                if "env" not in argv:
                    calls.append({"argv": list(argv), "environment": {"LEAN_PATH": environment.get("LEAN_PATH", "")},
                                  "label": str(label)})
                text = ""
                exit_code = 0
                error_text = ""
                if "env" in argv:
                    text = json.dumps({"LAKE": str(root / "bin/lake"),
                                       "LEAN_PATH": str(canonical), "LEAN_SYSROOT": str(root)})
                elif "build" in argv:
                    self.assertEqual({word for word in argv if word.startswith("+")}, {"+B", "+A"})
                elif "shake" in argv:
                    text = "".join(f"{module}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                                   for module in ("B", "A"))
                elif argv[0] == str(root / "bin/time"):
                    source = Path(argv[argv.index("-R") + 2])
                    artifact_root = Path(argv[argv.index("-i") + 1]).parent
                    outputs.physical_parts(artifact_root, Path(source.name))
                    Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
                elif "--deps" in argv:
                    modules = [line.removeprefix("import all ") for line in Path(argv[-1]).read_text().splitlines()]
                    text = "".join(str(Path(environment["LEAN_PATH"]) / (module + ".olean")) + "\n"
                                   for module in modules)
                elif "--run" in argv:
                    modules = argv[argv.index("--run") + 3:]
                    setup = optimizer.read_json(Path(argv[argv.index("--run") + 2]))
                    self.assertEqual(list(setup["snapshot_compilations"]), [module + ".lean" for module in modules])
                    self.assertEqual(environment["LEAN_PATH"], "")
                    records = []
                    for module in modules:
                        path = Path(setup["importArts"][module][0][0])
                        declaration = recovery.SavedSnapshotRecoveryTests.declaration()
                        declaration.update(name=module + ("_proof" if module == "A" else "_private"),
                                           kind="theorem" if module == "A" else "def",
                                           is_private_name=module == "B", is_exported=module == "A",
                                           axioms=["propext"] if module == "A" else [])
                        if fault == "axiom" and module == "A" and "candidate" in str(path):
                            declaration["axioms"] = ["propext", "Fixture.unaccepted"]
                        if fault == "private" and module == "B" and "candidate" in str(path):
                            declaration["value"] = "Nat.succ Nat.zero"
                        record = recovery.SavedSnapshotRecoveryTests.snapshot(module, path)
                        record.update(declarations=[declaration], batch_modules=modules,
                                      batch_module_count=len(modules), loaded_modules_scope="whole_batch",
                                      loaded_modules=["Init", *modules], loaded_module_count=len(modules) + 1)
                        records.append(record)
                    if (fault in ("loaded-entry", "persistent-loaded-entry") and
                            (len(modules) > 1 or
                             (fault == "persistent-loaded-entry" and modules == ["B"]))):
                        for record in records:
                            record["loaded_modules"].insert(0, deepcopy(loaded_entry))
                            record["loaded_module_count"] += 1
                    if fault == "reordered":
                        records.reverse()
                    elif fault == "incomplete":
                        records.pop()
                    nonobjects = {"nonobject-null": None, "nonobject-list": [],
                                  "nonobject-int": 0, "nonobject-string": "scalar",
                                  "nonobject-persistent": None}
                    if fault in nonobjects and (len(modules) > 1 or
                            (fault == "nonobject-persistent" and modules == ["B"])):
                        records[0] = nonobjects[fault]
                    text = "".join(json.dumps(record) + "\n" for record in records)
                    joint_failure = (fault in ("joint", "joint-candidate", "joint-and-single") and
                                     len(modules) > 1 and
                                     (fault != "joint-candidate" or "candidate" in str(path)))
                    if joint_failure or (fault == "joint-and-single" and modules == ["B"]):
                        text = ""
                        exit_code = 1
                        error_text = "incompatible duplicate global declaration Fixture.shared\n"
                else:
                    raise AssertionError(f"Unexpected native command: {argv}")
                stdout.write_text(text)
                stderr.write_text(error_text)
                command = {"argv": list(argv), "cwd": str(cwd), "exit_code": exit_code,
                           "timed_out": False, "remaining_group_killed": False,
                           "stdout": str(stdout), "stderr": str(stderr), "external_native_mock": True}
                optimizer.write_json(Path(str(label) + ".json"), command)
                return command

            def invoke(resume: bool = False) -> int:
                with patch.object(sys, "argv", [*arguments, *(["--resume"] if resume else [])]):
                    return optimizer.main()

            with patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=external), \
                    contextlib.redirect_stdout(io.StringIO()):
                yield root, calls, invoke

    def test_compatible_rows_share_two_snapshots_and_resume_without_native_work(self) -> None:
        with self.capture() as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            snapshots = [row for row in calls if "--run" in row["argv"]]
            self.assertEqual([row["argv"][-2:] for row in snapshots], [["A", "B"], ["A", "B"]])
            self.assertEqual(len([row for row in calls if row["argv"][0] == str(root / "bin/time")]), 4)
            deps = [row for row in calls if "--deps" in row["argv"]]
            self.assertEqual(len(deps), 4)
            self.assertEqual(len({row["environment"]["LEAN_PATH"] for row in deps}), 4)
            results = optimizer.read_journal(root / "output/results.jsonl", optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            for name, result in results.items():
                for arm in ("baseline", "candidate"):
                    record = result[arm]
                    group = optimizer.read_json(Path(record["snapshot_group"]["path"]))
                    self.assertEqual([row["path"] for row in group["members"]], ["A.lean", "B.lean"])
                    self.assertEqual(len(record["artifacts"]), 7)
                    self.assertEqual(group["members"][0]["compilation"]["setup_root"], str(root.resolve()))
            before_calls, journal = list(calls), (root / "output/results.jsonl").read_bytes()
            self.assertEqual(invoke(True), 0)
            self.assertEqual(calls, before_calls)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_conflicting_original_maps_keep_serial_snapshot_inputs(self) -> None:
        with self.capture("conflict") as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            snapshots = [row for row in calls if "--run" in row["argv"]]
            self.assertEqual([row["argv"][-1:] for row in snapshots], [["A"], ["A"], ["B"], ["B"]])
            for result in optimizer.read_journal(root / "output/results.jsonl", optimizer.read_json(root / "output/run.json")["sources"]).values():
                self.assertNotIn("snapshot_group", result["baseline"])

    def test_optimize_batch_retries_joint_import_failure_individually(self) -> None:
        with self.capture("joint") as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            snapshots = [row for row in calls if "--run" in row["argv"]]
            self.assertEqual([row["argv"][row["argv"].index("--run") + 3:] for row in snapshots],
                             [["A", "B"], ["A"], ["A"], ["B"], ["B"]])
            self.assertEqual(len([row for row in calls if row["argv"][0] == str(root / "bin/time")]), 4)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                             optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            for result in results.values():
                failure = result["shared_snapshot_failure"]
                failed = Path(failure["directory"]) / "baseline/snapshot-evidence/snapshot.json"
                self.assertEqual(optimizer.read_json(failed)["exit_code"], 1)
                self.assertIn("Fixture.shared", failed.with_suffix(".stderr").read_text())
                for arm in ("baseline", "candidate"):
                    self.assertNotIn("snapshot_group", result[arm])
                    self.assertEqual(len(result[arm]["artifacts"]), 7)
            before = list(calls)
            self.assertEqual(invoke(True), 0)
            self.assertEqual(calls, before)

    def test_resume_rejects_tampered_shared_snapshot_failure_evidence(self) -> None:
        with self.capture("joint") as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                             optimizer.read_json(root / "output/run.json")["sources"])
            failure = results["A.lean"]["shared_snapshot_failure"]
            self.assertIn("snapshot-failure.json", failure["receipts"])
            self.assertEqual(failure["modules"], ["A", "B"])
            shared = Path(failure["directory"])
            stdout = shared / "baseline/snapshot-evidence/snapshot.stdout"
            original = stdout.read_bytes()
            stdout.write_bytes(b"forged failure evidence\n")
            before = list(calls)
            with self.assertRaisesRegex(ValueError, "evidence file changed"):
                invoke(True)
            self.assertEqual(calls, before)
            stdout.write_bytes(original)
            (shared / "baseline/snapshot-evidence/snapshot.stdout").unlink()
            with self.assertRaises((ValueError, OSError)):
                invoke(True)
            self.assertEqual(calls, before)
            stdout.write_bytes(original)
            # Dropping the journal's command-evidence inventory must also
            # fail: the pinned failure manifest anchors the full inventory.
            journal = root / "output/results.jsonl"
            saved = journal.read_bytes()
            rows = [json.loads(line) for line in saved.decode().splitlines()]
            for row in rows:
                row["shared_snapshot_failure"]["arms"] = {}
            journal.write_text("".join(json.dumps(row) + "\n" for row in rows))
            with self.assertRaisesRegex(ValueError, "inventory changed"):
                invoke(True)
            self.assertEqual(calls, before)
            journal.write_bytes(saved)
            # Forging both error strings and repinning only the manifest
            # must fail: the error is re-derived from command evidence.
            manifest = shared / "snapshot-failure.json"
            record = optimizer.read_json(manifest)
            record["error"] = "forged failure reason"
            optimizer.write_json(manifest, record)
            rows = [json.loads(line) for line in journal.read_bytes().decode().splitlines()]
            for row in rows:
                failure_record = row["shared_snapshot_failure"]
                failure_record["error"] = "forged failure reason"
                failure_record["receipts"]["snapshot-failure.json"] = optimizer.file_pin(manifest)
            journal.write_text("".join(json.dumps(row) + "\n" for row in rows))
            with self.assertRaisesRegex(ValueError, "differs from its command evidence"):
                invoke(True)
            self.assertEqual(calls, before)

    def test_optimize_batch_drops_shared_receipts_after_candidate_import_failure(self) -> None:
        with self.capture("joint-candidate") as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            snapshots = [row for row in calls if "--run" in row["argv"]]
            self.assertEqual([row["argv"][row["argv"].index("--run") + 3:] for row in snapshots],
                             [["A", "B"], ["A", "B"], ["A"], ["A"], ["B"], ["B"]])
            results = optimizer.read_journal(root / "output/results.jsonl",
                                             optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            for result in results.values():
                shared = Path(result["shared_snapshot_failure"]["directory"])
                self.assertEqual(optimizer.read_json(shared / "baseline/snapshot-evidence/snapshot.json")["exit_code"], 0)
                self.assertEqual(optimizer.read_json(shared / "candidate/snapshot-evidence/snapshot.json")["exit_code"], 1)
                for arm in ("baseline", "candidate"):
                    self.assertNotIn("snapshot_group", result[arm])
                    setup = optimizer.read_json(Path(result[arm]["snapshot_setup"]["path"]))
                    self.assertEqual(list(setup["snapshot_compilations"]), [result["path"]])

    def test_optimize_batch_isolates_singleton_failure_after_joint_import_failure(self) -> None:
        with self.capture("joint-and-single") as (root, calls, invoke):
            self.assertEqual(invoke(), 1)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                             optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual(results["A.lean"]["status"], "verified")
            self.assertEqual(results["B.lean"]["status"], "blocked")
            self.assertIn("shared_snapshot_failure", results["A.lean"])
            self.assertIn("shared_snapshot_failure", results["B.lean"])

    def test_optimize_batch_retries_reordered_group_outputs_as_singletons(self) -> None:
        with self.capture("reordered") as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                             optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            self.assertTrue(all("order" in row["shared_snapshot_failure"]["error"]
                                for row in results.values()))
            for result in results.values():
                for arm in ("baseline", "candidate"):
                    self.assertNotIn("snapshot_group", result[arm])

    def test_optimize_batch_blocks_persistently_incomplete_snapshots(self) -> None:
        with self.capture("incomplete") as (root, calls, invoke):
            self.assertEqual(invoke(), 1)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                             optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["blocked", "blocked"])
            self.assertTrue(all("Batch snapshot" in row["error"] for row in results.values()))

    def test_optimize_batch_retries_nonobject_group_outputs_as_singletons(self) -> None:
        for fault, value in (("nonobject-null", None), ("nonobject-list", []),
                             ("nonobject-int", 0), ("nonobject-string", "scalar")):
            with self.subTest(fault=fault), self.capture(fault) as (root, calls, invoke):
                try:
                    code = invoke()
                except AttributeError as error:
                    self.fail(f"Malformed record escaped singleton fallback: {error}")
                self.assertEqual(code, 0)
                snapshots = [row for row in calls if "--run" in row["argv"]]
                self.assertEqual([row["argv"][row["argv"].index("--run") + 3:] for row in snapshots],
                                 [["A", "B"], ["A"], ["A"], ["B"], ["B"]])
                self.assertEqual(len([row for row in calls if row["argv"][0] == str(root / "bin/time")]), 4)
                results = optimizer.read_journal(root / "output/results.jsonl",
                                                 optimizer.read_json(root / "output/run.json")["sources"])
                self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
                for result in results.values():
                    failure = result["shared_snapshot_failure"]
                    self.assertIn("nonobject", failure["error"])
                    failed = Path(failure["directory"]) / "baseline/snapshot-evidence/snapshot.json"
                    self.assertEqual(optimizer.read_json(failed)["exit_code"], 0)
                    records = [json.loads(line) for line in failed.with_suffix(".stdout").read_text().splitlines()]
                    self.assertEqual(len(records), 2)
                    self.assertIs(type(records[0]), type(value))
                    self.assertEqual(records[0], value)
                    self.assertEqual(records[1]["module"], "B")
                    for arm in ("baseline", "candidate"):
                        self.assertNotIn("snapshot_group", result[arm])
                before, journal = list(calls), (root / "output/results.jsonl").read_bytes()
                self.assertEqual(invoke(True), 0)
                self.assertEqual(calls, before)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_optimize_batch_isolates_a_persistently_nonobject_singleton(self) -> None:
        with self.capture("nonobject-persistent") as (root, calls, invoke):
            try:
                code = invoke()
            except AttributeError as error:
                self.fail(f"Malformed record escaped singleton isolation: {error}")
            self.assertEqual(code, 1)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                             optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual(results["A.lean"]["status"], "verified")
            self.assertEqual(results["B.lean"]["status"], "blocked")
            self.assertIn("nonobject", results["B.lean"]["error"])
            self.assertTrue(all("shared_snapshot_failure" in row for row in results.values()))
            snapshots = [row for row in calls if "--run" in row["argv"]]
            self.assertEqual([row["argv"][row["argv"].index("--run") + 3:] for row in snapshots],
                             [["A", "B"], ["A"], ["A"], ["B"]])
            failed = Path(snapshots[-1]["label"])
            self.assertEqual(optimizer.read_json(failed.with_suffix(".json"))["exit_code"], 0)
            self.assertIsNone(json.loads(failed.with_suffix(".stdout").read_text()))
            before, journal = list(calls), (root / "output/results.jsonl").read_bytes()
            self.assertEqual(invoke(True), 1)
            self.assertEqual(calls, before)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_optimize_batch_retries_nonstring_loaded_modules_as_singletons(self) -> None:
        for entry in (None, False, 0, 0.5, [], {}):
            with self.subTest(entry=entry), self.capture("loaded-entry", entry) as (root, calls, invoke):
                try:
                    code = invoke()
                except TypeError as error:
                    self.fail(f"Malformed loaded-module entry escaped singleton fallback: {error}")
                self.assertEqual(code, 0)
                snapshots = [row for row in calls if "--run" in row["argv"]]
                self.assertEqual([row["argv"][row["argv"].index("--run") + 3:] for row in snapshots],
                                 [["A", "B"], ["A"], ["A"], ["B"], ["B"]])
                self.assertEqual(len([row for row in calls if row["argv"][0] == str(root / "bin/time")]), 4)
                results = optimizer.read_journal(root / "output/results.jsonl",
                                                 optimizer.read_json(root / "output/run.json")["sources"])
                self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
                for result in results.values():
                    failure = result["shared_snapshot_failure"]
                    self.assertIn("loaded-module receipt", failure["error"])
                    failed = Path(failure["directory"]) / "baseline/snapshot-evidence/snapshot.json"
                    self.assertEqual(optimizer.read_json(failed)["exit_code"], 0)
                    records = [json.loads(line) for line in failed.with_suffix(".stdout").read_text().splitlines()]
                    self.assertEqual(len(records), 2)
                    self.assertTrue(all(record["loaded_module_count"] == len(record["loaded_modules"])
                                        for record in records))
                    self.assertTrue(all(type(record["loaded_modules"][0]) is type(entry) and
                                        record["loaded_modules"][0] == entry for record in records))
                    for arm in ("baseline", "candidate"):
                        self.assertNotIn("snapshot_group", result[arm])
                        self.assertEqual(len(result[arm]["artifacts"]), 7)
                before, journal = list(calls), (root / "output/results.jsonl").read_bytes()
                self.assertEqual(invoke(True), 0)
                self.assertEqual(calls, before)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_optimize_batch_isolates_a_nonstring_loaded_module_singleton(self) -> None:
        for entry in (None, False, 0, 0.5, [], {}):
            with self.subTest(entry=entry), self.capture("persistent-loaded-entry", entry) as (root, calls, invoke):
                try:
                    code = invoke()
                except TypeError as error:
                    self.fail(f"Malformed loaded-module entry escaped singleton isolation: {error}")
                self.assertEqual(code, 1)
                results = optimizer.read_journal(root / "output/results.jsonl",
                                                 optimizer.read_json(root / "output/run.json")["sources"])
                self.assertEqual(results["A.lean"]["status"], "verified")
                self.assertEqual(results["B.lean"]["status"], "blocked")
                self.assertIn("loaded-module receipt", results["B.lean"]["error"])
                self.assertTrue(all("shared_snapshot_failure" in row for row in results.values()))
                snapshots = [row for row in calls if "--run" in row["argv"]]
                self.assertEqual([row["argv"][row["argv"].index("--run") + 3:] for row in snapshots],
                                 [["A", "B"], ["A"], ["A"], ["B"]])
                failed = Path(snapshots[-1]["label"])
                self.assertEqual(optimizer.read_json(failed.with_suffix(".json"))["exit_code"], 0)
                record = json.loads(failed.with_suffix(".stdout").read_text())
                self.assertEqual(record["loaded_module_count"], len(record["loaded_modules"]))
                self.assertIs(type(record["loaded_modules"][0]), type(entry))
                self.assertEqual(record["loaded_modules"][0], entry)
                before, journal = list(calls), (root / "output/results.jsonl").read_bytes()
                self.assertEqual(invoke(True), 1)
                self.assertEqual(calls, before)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_unaccepted_neighbor_axioms_do_not_certify_that_row(self) -> None:
        with self.capture("axiom") as (root, calls, invoke):
            self.assertEqual(invoke(), 1)
            results = optimizer.read_journal(root / "output/results.jsonl", optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual(results["B.lean"]["status"], "verified")
            self.assertEqual(results["A.lean"]["status"], "blocked")
            self.assertIn("changed owned declarations", results["A.lean"]["error"])

    def test_resume_verifies_every_group_member_artifact(self) -> None:
        with self.capture() as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl", optimizer.read_json(root / "output/run.json")["sources"])
            part = Path(results["A.lean"]["baseline"]["artifact_root"]) / "A.olean.private"
            original = part.read_bytes()
            part.write_bytes(b"x" * len(original))
            before = list(calls)
            with self.assertRaisesRegex(ValueError, "artifacts.*changed"):
                invoke(True)
            self.assertEqual(calls, before)

    @staticmethod
    def repin_loaded_module_receipts(results: list[dict[str, object]], fault: str,
                                    loaded_entry: object = None) -> None:
        for arm_name, filename, digest in (("baseline", "owned-before.json", "owned_before_sha256"),
                                           ("candidate", "owned-after.json", "owned_after_sha256")):
            rewritten: dict[Path, list[dict[str, object]]] = {}
            for result in results:
                arm = result[arm_name]
                command = arm.get("snapshot_command_evidence")
                stdout = (Path(command["stdout"]["path"]) if command is not None else
                          Path(arm["artifact_root"]).parent / "snapshot-evidence/snapshot.stdout")
                if stdout not in rewritten:
                    records = [json.loads(line) for line in stdout.read_text().splitlines()]
                    for index, record in enumerate(records):
                        if fault == "list":
                            record["loaded_modules"] = None
                        elif fault == "count":
                            record["loaded_module_count"] += 1
                        elif fault == "empty":
                            record.update(loaded_modules=[], loaded_module_count=0)
                        elif fault == "loaded-entry":
                            record["loaded_modules"].append(deepcopy(loaded_entry))
                            record["loaded_module_count"] += 1
                        elif fault == "missing-neighbor":
                            record.update(loaded_modules=["Init", records[0]["module"]], loaded_module_count=2)
                        elif index:
                            record["loaded_modules"].append("Fixture.extraLoadedModule")
                            record["loaded_module_count"] += 1
                    stdout.write_text("".join(json.dumps(record) + "\n" for record in records))
                    rewritten[stdout] = records
                if command is not None:
                    command["stdout"] = optimizer.file_pin(stdout)
                snapshot = next(record for record in rewritten[stdout] if record["module"] == result["module"])
                owned = Path(result["attempt_directory"]) / filename
                optimizer.write_json(owned, snapshot)
                result[digest] = optimizer.sha256(owned)

    def test_resume_rejects_repinned_group_loaded_module_receipts(self) -> None:
        for fault in ("list", "count", "empty", "missing-neighbor", "different"):
            with self.subTest(fault=fault), self.capture() as (root, calls, invoke):
                self.assertEqual(invoke(), 0)
                journal = root / "output/results.jsonl"
                results = [json.loads(line) for line in journal.read_text().splitlines()]
                self.assertTrue(all(result["status"] == "verified" for result in results))
                self.repin_loaded_module_receipts(results, fault)
                journal.write_text("".join(json.dumps(result) + "\n" for result in results))
                before, saved = list(calls), journal.read_bytes()
                with self.assertRaisesRegex(ValueError, "loaded-module receipt"):
                    invoke(True)
                self.assertEqual(calls, before)
                self.assertEqual(journal.read_bytes(), saved)

    def test_resume_rejects_repinned_singleton_batch_loaded_module_receipts(self) -> None:
        for fault in ("list", "count", "empty"):
            with self.subTest(fault=fault), self.capture("joint") as (root, calls, invoke):
                self.assertEqual(invoke(), 0)
                journal = root / "output/results.jsonl"
                results = [json.loads(line) for line in journal.read_text().splitlines()]
                self.assertTrue(all(result["status"] == "verified" for result in results))
                for result in results:
                    for arm_name in ("baseline", "candidate"):
                        arm = result[arm_name]
                        self.assertNotIn("snapshot_group", arm)
                        self.assertEqual(optimizer.read_json(Path(arm["snapshot_setup"]["path"]))["snapshot_kind"],
                                         "batch")
                self.repin_loaded_module_receipts(results, fault)
                journal.write_text("".join(json.dumps(result) + "\n" for result in results))
                before, saved = list(calls), journal.read_bytes()
                with self.assertRaisesRegex(ValueError, "loaded-module receipt"):
                    invoke(True)
                self.assertEqual(calls, before)
                self.assertEqual(journal.read_bytes(), saved)

    def test_resume_rejects_repinned_nonstring_group_loaded_modules(self) -> None:
        for entry in (None, False, 0, 0.5, [], {}):
            with self.subTest(entry=entry), self.capture() as (root, calls, invoke):
                self.assertEqual(invoke(), 0)
                journal = root / "output/results.jsonl"
                results = [json.loads(line) for line in journal.read_text().splitlines()]
                self.assertTrue(all(result["status"] == "verified" for result in results))
                for result in results:
                    for arm_name in ("baseline", "candidate"):
                        arm = result[arm_name]
                        self.assertIn("snapshot_group", arm)
                        self.assertEqual(len(optimizer.read_json(Path(arm["snapshot_group"]["path"]))["members"]), 2)
                self.repin_loaded_module_receipts(results, "loaded-entry", entry)
                journal.write_text("".join(json.dumps(result) + "\n" for result in results))
                before, saved = list(calls), journal.read_bytes()
                try:
                    with self.assertRaisesRegex(ValueError, "loaded-module receipt"):
                        invoke(True)
                except TypeError as error:
                    self.fail(f"Malformed group loaded-module entry escaped saved validation: {error}")
                self.assertEqual(calls, before)
                self.assertEqual(journal.read_bytes(), saved)

    def test_resume_rejects_repinned_nonstring_singleton_loaded_modules(self) -> None:
        for entry in (None, False, 0, 0.5, [], {}):
            with self.subTest(entry=entry), self.capture("joint") as (root, calls, invoke):
                self.assertEqual(invoke(), 0)
                journal = root / "output/results.jsonl"
                results = [json.loads(line) for line in journal.read_text().splitlines()]
                self.assertTrue(all(result["status"] == "verified" for result in results))
                for result in results:
                    for arm_name in ("baseline", "candidate"):
                        arm = result[arm_name]
                        self.assertNotIn("snapshot_group", arm)
                        self.assertEqual(optimizer.read_json(Path(arm["snapshot_setup"]["path"]))["snapshot_kind"],
                                         "batch")
                self.repin_loaded_module_receipts(results, "loaded-entry", entry)
                journal.write_text("".join(json.dumps(result) + "\n" for result in results))
                before, saved = list(calls), journal.read_bytes()
                try:
                    with self.assertRaisesRegex(ValueError, "loaded-module receipt"):
                        invoke(True)
                except TypeError as error:
                    self.fail(f"Malformed singleton loaded-module entry escaped saved validation: {error}")
                self.assertEqual(calls, before)
                self.assertEqual(journal.read_bytes(), saved)

    def test_repinned_group_proofs_cannot_replace_original_inputs_or_order(self) -> None:
        for fault in ("missing", "order", "source", "command", "inputs"):
            with self.subTest(fault=fault), self.capture() as (root, calls, invoke):
                self.assertEqual(invoke(), 0)
                journal = root / "output/results.jsonl"
                results = [json.loads(line) for line in journal.read_text().splitlines()]
                arm = results[0]["baseline"]
                group = optimizer.read_json(Path(arm["snapshot_group"]["path"]))
                if fault == "missing":
                    del arm["snapshot_group"]
                else:
                    if fault == "order":
                        group["members"].reverse()
                    elif fault == "source":
                        group["members"][1]["source"] = optimizer.file_pin(root / "A.lean")
                    elif fault == "command":
                        group["members"][1]["compilation"]["command"]["argv"].append("--changed")
                    else:
                        inputs = root / "output/empty-neighbor-inputs.json"
                        optimizer.write_json(inputs, {"files": []})
                        group["members"][1]["compilation"]["input_manifest"] = optimizer.file_pin(inputs)
                    path = root / "output/repinned-group.json"
                    optimizer.write_json(path, group)
                    arm["snapshot_group"] = optimizer.file_pin(path)
                journal.write_text("".join(json.dumps(result) + "\n" for result in results))
                before = list(calls)
                with self.assertRaises(ValueError):
                    invoke(True)
                self.assertEqual(calls, before)

    def test_grouped_private_value_change_does_not_certify_that_owner(self) -> None:
        with self.capture("private") as (root, calls, invoke):
            self.assertEqual(invoke(), 1)
            results = optimizer.read_journal(root / "output/results.jsonl", optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual(results["A.lean"]["status"], "verified")
            self.assertEqual(results["B.lean"]["status"], "blocked")
            self.assertIn("changed owned declarations", results["B.lean"]["error"])

    def test_public_batch_path_reuses_original_per_row_compilations(self) -> None:
        with self.capture() as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl", optimizer.read_json(root / "output/run.json")["sources"])
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 840,
                                    root / "bin/time")
            rows = [{"path": module + ".lean", "module": module,
                     "source_sha256": recovery.digest(recovery.ORIGINAL)} for module in ("B", "A")]
            compilations = {row["path"]: deepcopy(results[row["path"]]["baseline"]) for row in rows}
            roots = {name: Path(compilation["artifact_root"]) for name, compilation in compilations.items()}
            before = len(calls)
            snapshots = optimizer.snapshot_batch(tools, rows, roots, root / "output/reused", compilations)
            self.assertEqual(list(snapshots), ["B", "A"])
            self.assertEqual(len([row for row in calls[before:] if "--deps" in row["argv"]]), 2)
            self.assertEqual(len([row for row in calls[before:] if "--run" in row["argv"]]), 1)
            self.assertFalse(any(row["argv"][0] == str(root / "bin/time") for row in calls[before:]))
            for module, snapshot in snapshots.items():
                self.assertEqual(snapshot["resolved_olean"], str(roots[module + ".lean"] / (module + ".olean")))
                self.assertEqual(len(snapshot["declarations"][0]), 10)

    def test_aliased_project_root_reuses_compilations_in_public_batch(self) -> None:
        with self.capture() as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                            optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            for result in results.values():
                self.assertNotIn("shared_snapshot_failure", result)
                self.assertIn("snapshot_group", result["baseline"])
                self.assertIn("snapshot_group", result["candidate"])
            alias = root / "project-alias"
            alias.symlink_to(root, target_is_directory=True)
            self.assertTrue(alias.is_symlink())
            self.assertTrue(alias.samefile(root))
            self.assertNotEqual(str(alias), str(root.resolve()))
            tools = optimizer.Tools(alias, root / "output", root / "bin/lake", root / "bin/lean",
                                    Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 840,
                                    root / "bin/time")
            rows = [{"path": module + ".lean", "module": module,
                     "source_sha256": results[module + ".lean"]["source_sha256"]} for module in ("B", "A")]
            compilations = {row["path"]: deepcopy(results[row["path"]]["baseline"]) for row in rows}
            roots = {name: Path(compilation["artifact_root"]) for name, compilation in compilations.items()}
            before = len(calls)
            try:
                snapshots = optimizer.snapshot_batch(tools, rows, roots, root / "output/aliased", compilations)
            except ValueError as error:
                self.fail(f"Equivalent project root rejected original compilations: {error}")
            self.assertEqual(list(snapshots), ["B", "A"])
            self.assertEqual(len([row for row in calls[before:] if "--deps" in row["argv"]]), 2)
            self.assertEqual(len([row for row in calls[before:] if "--run" in row["argv"]]), 1)
            self.assertFalse(any(row["argv"][0] == str(root / "bin/time") for row in calls[before:]))
            for module, snapshot in snapshots.items():
                self.assertEqual(snapshot["resolved_olean"], str(roots[module + ".lean"] / (module + ".olean")))
                self.assertEqual(len(snapshot["declarations"][0]), 10)
                group = optimizer.read_json(Path(compilations[module + ".lean"]["snapshot_group"]["path"]))
                self.assertEqual(group["root"], str(root.resolve()))
            self.assertTrue(snapshots["B"]["declarations"][0]["is_private_name"])
            self.assertEqual(snapshots["A"]["declarations"][0]["axioms"], ["propext"])

    def test_aliased_project_root_validates_saved_groups_and_compilations(self) -> None:
        with self.capture() as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                            optimizer.read_json(root / "output/run.json")["sources"])
            self.assertEqual([row["status"] for row in results.values()], ["verified", "verified"])
            for result in results.values():
                self.assertNotIn("shared_snapshot_failure", result)
                self.assertIn("snapshot_group", result["baseline"])
                self.assertIn("snapshot_group", result["candidate"])
            alias = root / "project-alias"
            alias.symlink_to(root, target_is_directory=True)
            self.assertTrue(alias.is_symlink())
            self.assertTrue(alias.samefile(root))
            self.assertNotEqual(str(alias), str(root.resolve()))
            tools = optimizer.Tools(alias, root / "output", root / "bin/lake", root / "bin/lean",
                                    Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 840,
                                    root / "bin/time", root / ".lake/lakefile-lean-j2.toml")
            before, journal = list(calls), (root / "output/results.jsonl").read_bytes()
            try:
                with optimizer.analysis_validation_phase(tools):
                    for result in results.values():
                        optimizer.verify_saved_candidate(result, tools.output, tools)
            except ValueError as error:
                self.fail(f"Equivalent project root rejected saved evidence: {error}")
            self.assertEqual(calls, before)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_different_physical_project_does_not_validate_saved_group(self) -> None:
        with self.capture() as (root, calls, invoke):
            self.assertEqual(invoke(), 0)
            results = optimizer.read_journal(root / "output/results.jsonl",
                                            optimizer.read_json(root / "output/run.json")["sources"])
            group = optimizer.read_json(Path(results["A.lean"]["baseline"]["snapshot_group"]["path"]))
            member = group["members"][0]
            other = root / "other-project"
            other.mkdir()
            (other / member["path"]).write_bytes((root / member["path"]).read_bytes())
            (other / "bin").mkdir()
            (other / "bin/time").write_bytes((root / "bin/time").read_bytes())
            self.assertFalse(other.samefile(root))
            self.assertEqual((other / member["path"]).read_bytes(), (root / member["path"]).read_bytes())
            tools = optimizer.Tools(other, root / "output", root / "bin/lake", root / "bin/lean",
                                    Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 840,
                                    other / "bin/time")
            before = list(calls)
            with self.assertRaisesRegex(ValueError, "Snapshot group source belongs to a different project"):
                optimizer.verify_snapshot_group_member(tools, member)
            self.assertEqual(calls, before)


if __name__ == "__main__":
    unittest.main()
