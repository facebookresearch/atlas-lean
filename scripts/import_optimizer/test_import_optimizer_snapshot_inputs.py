#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Shared-input controls use a saved native sibling; Lean/helper calls are mocked."""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tarfile
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_evidence as evidence
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery


ARCHIVE = Path(__file__).parent / "testdata/reference_actual037.tar.gz"
EXTERNAL_ARTIFACTS = [{"external_artifacts_mock": True}]


def native_sibling(root: Path) -> tuple[str, Path]:
    with tarfile.open(ARCHIVE) as archive:
        prefix_file = archive.extractfile("input/original-compiler-prefix.json")
        artifact_file = archive.extractfile("input/Statement.olean")
        assert prefix_file is not None and artifact_file is not None
        prefix = json.load(prefix_file)
        raw = artifact_file.read()
    module = prefix["module"]
    path = root / Path(*module.split(".")).with_suffix(".olean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    original = next(record for record in prefix["artifacts"] if record["path"].endswith(".olean"))
    if len(raw) != original["bytes"] or optimizer.sha256(path) != original["sha256"]:
        raise AssertionError("Saved native sibling does not match its real compiler receipt")
    return module, path


class SharedSnapshotInputTests(unittest.TestCase):
    def capture(self, output: Path, mutate: Callable[[str, Path], None] | None = None
                ) -> tuple[dict[str, object], optimizer.Tools, dict[str, Path]]:
        result, _ = evidence.CompilationInputResumeTests().saved_evidence(output)
        tools = optimizer.Tools(output, output, output / "lake", output / "lean", output, {}, 5,
                                time_binary=output / "time")
        directory = Path(result["attempt_directory"])
        siblings = {}
        for name, filename, field in (("baseline", "owned-before.json", "owned_before_sha256"),
                                      ("candidate", "owned-after.json", "owned_after_sha256")):
            arm = result[name]
            artifacts = Path(arm["artifact_root"])
            outputs.physical_parts(artifacts, Path("A.lean"))
            module, sibling = native_sibling(artifacts)
            siblings[name] = sibling
            calls = []

            def external(argv: list[str], label: Path,
                         environment: dict[str, str] | None = None) -> dict[str, object]:
                assert environment is not None
                phase = "deps" if "--deps" in argv else "snapshot"
                self.assertEqual(environment["LEAN_PATH"], str(artifacts) if phase == "deps" else "")
                calls.append(phase)
                self.assertGreater(sibling.stat().st_size, 0)
                if phase == "deps":
                    Path(str(label) + ".stdout").write_text(str(artifacts / "A.olean") + "\n")
                else:
                    snapshot = recovery.SavedSnapshotRecoveryTests.snapshot("A", artifacts / "A.olean")
                    snapshot.update(batch_modules=["A"], batch_module_count=1,
                                    loaded_modules_scope="whole_batch", loaded_modules=["A", module],
                                    loaded_module_count=2)
                    Path(str(label) + ".stdout").write_text(json.dumps(snapshot) + "\n")
                if name == "candidate" and mutate is not None:
                    mutate(phase, sibling)
                return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "external_lean_helper_mock": True}

            with patch.object(optimizer, "artifact_receipt", return_value=EXTERNAL_ARTIFACTS), \
                    patch.object(optimizer.Tools, "run", side_effect=external):
                snapshot = optimizer.snapshot_batch(tools, [{"path": "A.lean", "module": "A"}],
                                                    artifacts, directory / name, {"A.lean": arm})["A"]
            self.assertEqual(calls, ["deps", "snapshot"])
            self.assertEqual(snapshot["declaration_count"], 1)
            self.assertIn(module, snapshot["loaded_modules"])
            optimizer.write_json(directory / filename, snapshot)
            result[field] = optimizer.sha256(directory / filename)
        return result, tools, siblings

    @staticmethod
    def verify(result: dict[str, object], output: Path, tools: optimizer.Tools) -> None:
        with patch.object(optimizer, "artifact_receipt", return_value=EXTERNAL_ARTIFACTS):
            recovery.verify_saved_fixture(result, output, tools)

    def test_saved_candidate_accepts_unchanged_shared_native_sibling(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory).resolve()
            result, tools, _ = self.capture(output)
            self.verify(result, output, tools)
            self.verify(result, output, tools)

    def test_saved_candidate_rejects_sibling_edit_after_snapshot(self) -> None:
        for name in ("baseline", "candidate"):
            with self.subTest(arm=name), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, tools, siblings = self.capture(output)
                self.verify(result, output, tools)
                sibling = siblings[name]
                before = sibling.stat()
                raw = sibling.read_bytes()
                sibling.write_bytes(raw[:-1] + bytes([raw[-1] ^ 1]))
                os.utime(sibling, ns=(before.st_atime_ns, before.st_mtime_ns))
                self.assertEqual(sibling.stat().st_size, before.st_size)
                self.assertEqual(sibling.stat().st_mtime_ns, before.st_mtime_ns)
                with self.assertRaises(ValueError):
                    self.verify(result, output, tools)

    def test_saved_candidate_rejects_shared_root_membership_changes(self) -> None:
        for defect in ("added", "removed", "symlink"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, tools, siblings = self.capture(output)
                self.verify(result, output, tools)
                sibling = siblings["candidate"]
                if defect == "added":
                    (sibling.parent / "added.ir").write_bytes(b"New external metadata fixture\n")
                elif defect == "removed":
                    sibling.unlink()
                else:
                    copy = output / "external-sibling.olean"
                    copy.write_bytes(sibling.read_bytes())
                    sibling.unlink()
                    sibling.symlink_to(copy)
                with self.assertRaises((ValueError, OSError)):
                    self.verify(result, output, tools)

    def test_shared_snapshot_rejects_sibling_edit_during_each_child(self) -> None:
        for phase in ("deps", "snapshot"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                def mutate(current: str, sibling: Path) -> None:
                    if current == phase:
                        sibling.write_bytes(sibling.read_bytes() + b"External sibling edit\n")

                with self.assertRaises(ValueError):
                    self.capture(Path(directory).resolve(), mutate)

    def test_saved_batch_requires_its_original_complete_input_manifest(self) -> None:
        for defect in ("missing", "empty", "foreign_arm", "omitted_file", "scope_removed"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, tools, _ = self.capture(output)
                self.verify(result, output, tools)
                arm = result["candidate"]
                if defect == "missing":
                    del arm["snapshot_input_manifest"]
                elif defect == "empty":
                    arm["snapshot_input_manifest"] = {}
                elif defect == "foreign_arm":
                    arm["snapshot_input_manifest"] = result["baseline"]["snapshot_input_manifest"]
                elif defect == "scope_removed":
                    path = Path(result["attempt_directory"]) / "owned-after.json"
                    snapshot = optimizer.read_json(path)
                    for field in ("batch_modules", "batch_module_count", "loaded_modules_scope"):
                        del snapshot[field]
                    optimizer.write_json(path, snapshot)
                    result["owned_after_sha256"] = optimizer.sha256(path)
                else:
                    manifest = Path(arm["snapshot_input_manifest"]["path"])
                    value = optimizer.read_json(manifest)
                    value["files"] = []
                    optimizer.write_json(manifest, value)
                    arm["snapshot_input_manifest"] = optimizer.file_pin(manifest)
                with self.assertRaises(ValueError):
                    self.verify(result, output, tools)

    def test_later_capture_preserves_previous_shared_input_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory).resolve()
            result, tools, siblings = self.capture(output)
            saved = result["candidate"]["snapshot_input_manifest"]
            original = Path(saved["path"]).read_bytes()
            siblings["candidate"].write_bytes(siblings["candidate"].read_bytes() + b"Later blocked retry\n")
            root = Path(result["candidate"]["artifact_root"])
            new = optimizer.pin_snapshot_inputs(tools, root)
            self.assertNotEqual(saved["path"], new["path"])
            self.assertEqual(Path(saved["path"]).read_bytes(), original)
            optimizer.verify_snapshot_inputs(new, root, output, tools)
            with self.assertRaises(ValueError):
                self.verify(result, output, tools)

    def test_main_resume_rejects_changed_shared_sibling_before_new_work(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = recovery.main_inputs(root, ("A",))
            calls: list[str] = []
            siblings: dict[str, Path] = {}

            def external(argv: list[str], label: Path,
                         environment: dict[str, str] | None = None) -> dict[str, object]:
                label.parent.mkdir(parents=True, exist_ok=True)
                stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                if "shake" in argv:
                    calls.append("shake")
                    stdout.write_text("A.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n")
                elif "build" in argv:
                    calls.append("prepare")
                    stdout.write_text("External canonical build mocked\n")
                elif "--deps" in argv:
                    calls.append("deps")
                    stdout.write_text(str(Path(argv[-1]).parent / "artifacts/A.olean") + "\n")
                elif "--run" in argv:
                    calls.append("snapshot")
                    snapshot_setup = optimizer.read_json(Path(argv[argv.index("--run") + 2]))
                    artifacts = Path(snapshot_setup["importArts"]["A"][0][0]).parent
                    module = ".".join(siblings[label.parent.parent.name].relative_to(artifacts).with_suffix("").parts)
                    snapshot = recovery.SavedSnapshotRecoveryTests.snapshot("A", artifacts / "A.olean")
                    snapshot.update(batch_modules=["A"], batch_module_count=1,
                                    loaded_modules_scope="whole_batch", loaded_modules=["A", module],
                                    loaded_module_count=2)
                    stdout.write_text(json.dumps(snapshot) + "\n")
                else:
                    raise AssertionError(f"Unexpected external call: {argv}")
                stderr.write_text("")
                command = {"argv": argv, "cwd": str(root), "exit_code": 0, "timed_out": False,
                           "remaining_group_killed": False, "stdout": str(stdout), "stderr": str(stderr)}
                optimizer.write_json(Path(str(label) + ".json"), command)
                return command

            def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                             arm: Path, artifact_root: Path | None = None,
                             source_bytes: bytes | None = None, *,
                             header_is_module: bool = True) -> dict[str, object]:
                assert artifact_root is not None and source_bytes is not None
                calls.append("compile")
                outputs.physical_parts(artifact_root, relative)
                _, siblings[arm.name] = native_sibling(artifact_root)
                return {"artifact_root": str(artifact_root), "artifacts": EXTERNAL_ARTIFACTS,
                        **recovery.mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root)}

            with patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=recovery.environment_stub), \
                    patch.object(optimizer.Tools, "run", side_effect=external), \
                    patch.object(optimizer, "artifact_receipt", return_value=EXTERNAL_ARTIFACTS), \
                    patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                    contextlib.redirect_stdout(io.StringIO()):
                with patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                journal = (root / "output/results.jsonl").read_bytes()
                self.assertEqual((json.loads(journal)["status"], json.loads(journal)["declaration_count"]),
                                 ("verified", 1))
                self.assertEqual((calls.count("compile"), calls.count("snapshot")), (2, 2))
                completed_calls = list(calls)
                with patch.object(sys, "argv", [*arguments, "--resume"]):
                    self.assertEqual(optimizer.main(), 0)
                self.assertEqual(calls, completed_calls)
                sibling = siblings["candidate"]
                sibling.write_bytes(sibling.read_bytes() + b"Changed blocked sibling\n")
                with patch.object(sys, "argv", [*arguments, "--resume", "--retry-blocked"]):
                    with self.assertRaises(ValueError):
                        optimizer.main()
                self.assertEqual(calls, completed_calls)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
                self.assertEqual((root / "A.lean").read_bytes(), recovery.ORIGINAL)

    def test_shared_snapshot_rejects_restored_sibling_edit_during_each_child(self) -> None:
        for phase in ("deps", "snapshot"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                def mutate(current: str, sibling: Path) -> None:
                    if current == phase:
                        before, raw = sibling.stat(), sibling.read_bytes()
                        sibling.write_bytes(raw + b"Transient external sibling edit\n")
                        sibling.write_bytes(raw)
                        os.utime(sibling, ns=(before.st_atime_ns, before.st_mtime_ns))

                with self.assertRaises(ValueError):
                    self.capture(Path(directory).resolve(), mutate)

    def test_shared_snapshot_rejects_restored_membership_during_each_child(self) -> None:
        for phase in ("deps", "snapshot"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                def mutate(current: str, sibling: Path) -> None:
                    if current == phase:
                        transient = sibling.parent / "transient.ir"
                        transient.write_bytes(b"Transient external IR fixture\n")
                        transient.unlink()

                with self.assertRaises(ValueError):
                    self.capture(Path(directory).resolve(), mutate)


if __name__ == "__main__":
    unittest.main()
