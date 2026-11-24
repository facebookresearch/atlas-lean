#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Physical source/output controls; native compiler and helper calls are mocked."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_evidence as evidence
import test_import_optimizer_recovery as recovery


SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".ilean", ".c")


def physical_parts(artifacts: Path, relative: Path,
                   suffixes: tuple[str, ...] = SUFFIXES) -> list[dict[str, object]]:
    prefix = artifacts / relative.with_suffix("")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    for suffix in suffixes:
        Path(str(prefix) + suffix).write_text("Mock compiler output " + suffix + "\n")
    return optimizer.artifact_receipt(artifacts, relative)


def arm_source(arm: Path, relative: Path, data: bytes) -> dict[str, object]:
    root = arm / "source"
    source = root / relative
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(data)
    return {"source_root": str(root), "source_path": str(source), "source_sha256": recovery.digest(data)}


class CompilationOutputResumeTests(unittest.TestCase):
    @staticmethod
    def saved_evidence(output: Path) -> dict[str, object]:
        result, _ = evidence.CompilationInputResumeTests().saved_evidence(output)
        for name, data in (("baseline", recovery.ORIGINAL), ("candidate", recovery.CANDIDATE)):
            arm = Path(result["attempt_directory"]) / name
            artifacts = Path(result[name]["artifact_root"])
            result[name].update(arm_source(arm, Path("A.lean"), data),
                                artifacts=physical_parts(artifacts, Path("A.lean")))
            recovery.bind_mock_snapshot_inputs(recovery.saved_fixture_tools(output), result[name], Path("A.lean"))
        return result

    def test_artifact_receipt_includes_c_without_requiring_canonical_ir_layout(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            canonical = root / ".lake/build/lib/lean"
            canonical.mkdir(parents=True)
            (canonical / "A.olean").write_bytes(b"Mock canonical output\n")
            self.assertEqual(len(optimizer.artifact_receipt(canonical, Path("A.lean"))), 1)
            artifacts = physical_parts(root / "forced", Path("A.lean"))
            self.assertEqual({Path(record["path"]).name for record in artifacts},
                             {"A" + suffix for suffix in SUFFIXES})

    def test_compile_requires_requested_nonempty_c_in_both_arms(self) -> None:
        for name, data in (("baseline", recovery.ORIGINAL), ("candidate", recovery.CANDIDATE)):
            for defect in (None, "missing", "empty"):
                with self.subTest(arm=name, defect=defect), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    recovery.main_inputs(root, ("A",))
                    tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                            root, {}, 5, root / "bin/time")
                    arm = tools.output / name

                    def external(argv: list[str], label: Path,
                                 environment: dict[str, str] | None = None) -> dict[str, object]:
                        physical_parts(arm / "artifacts", Path("A.lean"))
                        c = Path(argv[argv.index("-c") + 1])
                        if defect == "missing":
                            c.unlink()
                        elif defect == "empty":
                            c.write_bytes(b"")
                        Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
                        return recovery.mock_compile_command(tools, argv, label)

                    with patch.object(optimizer.Tools, "run", side_effect=external):
                        if defect:
                            with self.assertRaisesRegex(ValueError, "nonempty target .c"):
                                optimizer.compile_arm(tools, Path("A.lean"), root / ".lake/build/ir/A.setup.json",
                                                      arm, source_bytes=data)
                            self.assertFalse((arm / "compile-receipt.json").exists())
                        else:
                            result = optimizer.compile_arm(tools, Path("A.lean"), root / ".lake/build/ir/A.setup.json",
                                                           arm, source_bytes=data)
                            self.assertEqual(len(result["artifacts"]), 7)
                            self.assertEqual(Path(result["source_path"]).read_bytes(), data)

    def test_saved_candidate_rejects_missing_changed_or_unpinned_c(self) -> None:
        for name in ("baseline", "candidate"):
            for defect in ("missing", "empty", "changed", "unlisted"):
                with self.subTest(arm=name, defect=defect), tempfile.TemporaryDirectory() as directory:
                    output = Path(directory).resolve()
                    result = self.saved_evidence(output)
                    recovery.verify_saved_fixture(result, output)
                    c = Path(result[name]["artifact_root"]) / "A.c"
                    if defect == "missing":
                        c.unlink()
                    elif defect == "empty":
                        c.write_bytes(b"")
                    elif defect == "changed":
                        c.write_bytes(c.read_bytes() + b"changed\n")
                    else:
                        result[name]["artifacts"] = [record for record in result[name]["artifacts"]
                                                     if record["path"] != str(c)]
                    with self.assertRaisesRegex(ValueError, "artifacts|target .c"):
                        recovery.verify_saved_fixture(result, output)

    def test_saved_candidate_links_each_arm_source_to_its_saved_source(self) -> None:
        for name in ("baseline", "candidate"):
            for defect in ("missing_root", "missing_path", "missing_hash", "foreign_root", "foreign_path",
                           "wrong_hash", "changed_bytes", "changed_and_repinned", "other_arm"):
                with self.subTest(arm=name, defect=defect), tempfile.TemporaryDirectory() as directory:
                    output = Path(directory).resolve()
                    result = self.saved_evidence(output)
                    recovery.verify_saved_fixture(result, output)
                    arm = result[name]
                    source = Path(arm["source_path"])
                    if defect.startswith("missing_"):
                        del arm[{"missing_root": "source_root", "missing_path": "source_path",
                                 "missing_hash": "source_sha256"}[defect]]
                    elif defect in ("foreign_root", "foreign_path"):
                        foreign = output / "foreign/source/A.lean"
                        foreign.parent.mkdir(parents=True)
                        foreign.write_bytes(source.read_bytes())
                        arm["source_root" if defect == "foreign_root" else "source_path"] = str(
                            foreign.parent if defect == "foreign_root" else foreign)
                    elif defect == "wrong_hash":
                        arm["source_sha256"] = "0" * 64
                    elif defect == "other_arm":
                        other = result["candidate" if name == "baseline" else "baseline"]
                        arm.update({key: other[key] for key in ("source_root", "source_path", "source_sha256")})
                    else:
                        source.write_bytes(source.read_bytes() + b"-- changed arm source\n")
                        if defect == "changed_and_repinned":
                            arm["source_sha256"] = optimizer.sha256(source)
                    with self.assertRaisesRegex(ValueError, "source"):
                        recovery.verify_saved_fixture(result, output)

    def snapshot(self, tools: optimizer.Tools, artifacts: Path, arm: Path, batch: bool,
                 compilation: dict[str, object] | None = None) -> object:
        if compilation is None:
            setup = arm / "setup.json"
            dependency = arm / "fixture-import-part"
            dependency.write_bytes(b"Explicitly mocked imported module bytes\n")
            optimizer.write_json(setup, {"name": "A", "isModule": True,
                                        "importArts": {"Mathlib": [[str(dependency)], []]}})
            compilation = {"setup": optimizer.file_pin(setup), "header_is_module": True,
                           "standard_library_root": None,
                           "input_manifest": optimizer.pin_setup_inputs(tools, optimizer.read_json(setup))}
        if batch:
            return optimizer.snapshot_batch(tools, [{"path": "A.lean", "module": "A"}], artifacts, arm,
                                            {"A.lean": compilation})
        return optimizer.snapshot_arm(tools, "A", Path("A.lean"), arm, compilation)

    @staticmethod
    def snapshot_external(artifacts: Path, batch: bool, defect: str | None = None, *,
                          is_module: bool = True):
        def external(argv: list[str], label: Path,
                     environment: dict[str, str] | None = None) -> dict[str, object]:
            if "--deps" in argv:
                Path(str(label) + ".stdout").write_text(str(artifacts / "A.olean") + "\n")
            else:
                snapshot = recovery.SavedSnapshotRecoveryTests.snapshot("A", artifacts / "A.olean")
                snapshot["uses_module_system"] = is_module
                if batch:
                    snapshot.update(batch_modules=["A"], batch_module_count=1,
                                    loaded_modules_scope="whole_batch")
                Path(str(label) + ".stdout").write_text(json.dumps(snapshot) + "\n")
                if defect:
                    c = artifacts / "A.c"
                    if defect == "missing":
                        c.unlink()
                    else:
                        c.write_bytes(c.read_bytes() + b"changed during snapshot\n")
            return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "external_lean_helper_mock": True, "batch": batch}
        return external

    def test_single_and_batch_snapshots_pin_c_through_actual_file_changes(self) -> None:
        for batch in (False, True):
            for defect in (None, "changed", "missing"):
                with self.subTest(batch=batch, defect=defect), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arm = root / "arm"
                    artifacts = arm / "artifacts"
                    physical_parts(artifacts, Path("A.lean"))
                    tools = optimizer.Tools(root, root, root / "lake", root / "lean", root, {}, 5,
                                            time_binary=root / "time")
                    with patch.object(optimizer.Tools, "run",
                                      side_effect=self.snapshot_external(artifacts, batch, defect)) as child:
                        if defect:
                            with self.assertRaisesRegex(ValueError, "artifacts|target .c"):
                                self.snapshot(tools, artifacts, arm, batch)
                        else:
                            snapshot = self.snapshot(tools, artifacts, arm, batch)
                            self.assertEqual((snapshot["A"] if batch else snapshot)["declaration_count"], 1)
                        self.assertEqual(child.call_count, 2)

    def test_snapshots_reject_missing_or_empty_c_before_dispatch(self) -> None:
        for batch in (False, True):
            for defect in ("missing", "empty"):
                with self.subTest(batch=batch, defect=defect), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arm = root / "arm"
                    artifacts = arm / "artifacts"
                    physical_parts(artifacts, Path("A.lean"))
                    c = artifacts / "A.c"
                    c.unlink() if defect == "missing" else c.write_bytes(b"")
                    tools = optimizer.Tools(root, root, root / "lake", root / "lean", root, {}, 5,
                                            time_binary=root / "time")
                    with patch.object(optimizer.Tools, "run",
                                      side_effect=self.snapshot_external(artifacts, batch)) as child:
                        with self.assertRaisesRegex(ValueError, "nonempty target .c"):
                            self.snapshot(tools, artifacts, arm, batch)
                        child.assert_not_called()

    def test_main_resume_rejects_arm_source_or_c_without_new_children(self) -> None:
        for name in ("baseline", "candidate"):
            for defect in ("source_path", "source_hash", "changed_c", "missing_c"):
                with self.subTest(arm=name, defect=defect), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arguments = recovery.main_inputs(root, ("A",))
                    compiles, analyses = [], []

                    def external(argv: list[str], label: Path,
                                 environment: dict[str, str] | None = None) -> dict[str, object]:
                        label.parent.mkdir(parents=True, exist_ok=True)
                        stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                        if "shake" in argv:
                            stdout.write_text("A.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n")
                            analyses.append(label)
                        elif "build" in argv:
                            canonical = root / ".lake/build/lib/lean/A.olean"
                            canonical.parent.mkdir(parents=True, exist_ok=True)
                            canonical.write_bytes(b"Mock canonical compiler output\n")
                            stdout.write_text("Mock prepared target\n")
                        else:
                            raise AssertionError(f"Unexpected child: {argv}")
                        stderr.write_text("")
                        command = {"argv": argv, "cwd": str(root), "exit_code": 0,
                                   "timed_out": False, "remaining_group_killed": False,
                                   "stdout": str(stdout), "stderr": str(stderr)}
                        optimizer.write_json(Path(str(label) + ".json"), command)
                        return command

                    def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                                     arm: Path, artifact_root: Path | None = None,
                                     source_bytes: bytes | None = None, *,
                                     header_is_module: bool = True) -> dict[str, object]:
                        self.assertIsNotNone(source_bytes)
                        compiles.append(arm)
                        return {"artifact_root": str(artifact_root),
                                "artifacts": physical_parts(artifact_root, relative),
                                **recovery.mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root),
                                **arm_source(arm, relative, source_bytes)}

                    def snapshots(tools: optimizer.Tools, rows: list[dict[str, object]],
                                  artifacts: Path, arm: Path, compilations: dict[str, dict[str, object]]
                                  ) -> dict[str, dict[str, object]]:
                        return {"A": recovery.SavedSnapshotRecoveryTests.snapshot("A", artifacts / "A.olean")}

                    with patch.object(optimizer.signal, "signal"), \
                            patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                            patch.object(optimizer, "run_command", side_effect=recovery.environment_stub), \
                            patch.object(optimizer.Tools, "run", side_effect=external), \
                            patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                            patch.object(optimizer, "snapshot_batch", side_effect=snapshots), \
                            contextlib.redirect_stdout(io.StringIO()):
                        with patch.object(sys, "argv", arguments):
                            self.assertEqual(optimizer.main(), 0)
                        journal = root / "output/results.jsonl"
                        original = journal.read_bytes()
                        result = json.loads(original)
                        self.assertEqual((result["status"], result["declaration_count"]), ("verified", 1))
                        with patch.object(sys, "argv", arguments + ["--resume"]):
                            self.assertEqual(optimizer.main(), 0)
                        if defect.startswith("source_"):
                            result[name]["source_path" if defect == "source_path" else "source_sha256"] = (
                                str(Path(result["attempt_directory"]) / "original.lean") if defect == "source_path" else "0" * 64)
                            journal.write_text(json.dumps(result) + "\n")
                        else:
                            c = Path(result[name]["artifact_root"]) / "A.c"
                            c.unlink() if defect == "missing_c" else c.write_bytes(b"changed compiler output\n")
                        before_failure = journal.read_bytes()
                        with patch.object(sys, "argv", arguments + ["--resume"]):
                            with self.assertRaisesRegex(ValueError, "source|artifacts|target .c"):
                                optimizer.main()
                        self.assertEqual(journal.read_bytes(), before_failure)
                        self.assertEqual((len(compiles), len(analyses)), (2, 1))
                        self.assertEqual((root / "A.lean").read_bytes(), recovery.ORIGINAL)


class FreshCompilationOutputTests(unittest.TestCase):
    @staticmethod
    def child(tools: optimizer.Tools, mode: str, suffixes: tuple[str, ...] = SUFFIXES):
        def external(argv: list[str], label: Path,
                     environment: dict[str, str] | None = None) -> dict[str, object]:
            prefix = str(Path(argv[argv.index("-i") + 1]).with_suffix(""))
            script = """import json, pathlib, sys
prefix, timing, mode = sys.argv[1:4]
paths = [pathlib.Path(prefix + suffix) for suffix in sys.argv[4:]]
before = sum(path.exists() for path in paths)
receipt = pathlib.Path(timing).with_name('compile-receipt.json')
if mode == 'fresh':
    assert before == 0, ('stale compiler outputs', before)
    assert not receipt.exists(), 'stale successful compile receipt'
if mode != 'none':
    for path in paths:
        path.write_text('Fresh Python child output ' + path.suffix + '\\n')
pathlib.Path(timing).write_text(json.dumps({'wall_seconds': 0}) + '\\n')
print(json.dumps({'mode': mode, 'existing_before_child': before,
                  'created_outputs': 0 if mode == 'none' else len(paths)}))
raise SystemExit(37 if mode == 'failed' else 0)
"""
            timing = argv[argv.index("-o") + 1]
            return optimizer.run_command([sys.executable, "-c", script, prefix, timing, mode, *suffixes],
                                         tools.root, label, tools.environment, tools.timeout)
        return external

    def test_failed_attempt_outputs_cannot_satisfy_successful_empty_retry(self) -> None:
        for name, source in (("baseline", recovery.ORIGINAL), ("candidate", recovery.CANDIDATE)):
            with self.subTest(arm=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                recovery.main_inputs(root, ("A",))
                tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                        root, {}, 5, root / "bin/time")
                arm, artifacts = tools.output / name, tools.output / "batches/0" / name / "artifacts"
                setup = root / ".lake/build/ir/A.setup.json"
                with patch.object(optimizer.Tools, "run", side_effect=self.child(tools, "failed")):
                    with self.assertRaisesRegex(ValueError, "37"):
                        optimizer.compile_arm(tools, Path("A.lean"), setup, arm, artifacts, source)
                self.assertEqual(len(optimizer.artifact_receipt(artifacts, Path("A.lean"))), 7)
                self.assertFalse((arm / "compile-receipt.json").exists())
                with patch.object(optimizer.Tools, "run", side_effect=self.child(tools, "none")):
                    with self.assertRaisesRegex(ValueError, "nonempty target .olean"):
                        optimizer.compile_arm(tools, Path("A.lean"), setup, arm, artifacts, source)
                command = optimizer.read_json(arm / "compile.json")
                self.assertEqual(command["exit_code"], 0)
                self.assertIn('"created_outputs": 0', (arm / "compile.stdout").read_text())
                self.assertFalse((arm / "compile-receipt.json").exists())
                self.assertEqual((root / "A.lean").read_bytes(), recovery.ORIGINAL)

    def test_reset_selected_prefix_preserves_other_complete_package_modules(self) -> None:
        for name, source in (("baseline", recovery.ORIGINAL), ("candidate", recovery.CANDIDATE)):
            with self.subTest(arm=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                recovery.main_inputs(root, ("A", "B"))
                tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                        root, {}, 5, root / "bin/time")
                arm, artifacts = tools.output / name, tools.output / "batches/0" / name / "artifacts"
                previous = physical_parts(artifacts, Path("A.lean"))
                sibling = physical_parts(artifacts, Path("B.lean"))
                sibling_identity = [(Path(row["path"]).stat().st_mtime_ns,
                                     Path(row["path"]).stat().st_mode) for row in sibling]
                arm.mkdir(parents=True, exist_ok=True)
                (arm / "compile-receipt.json").write_text('{"stale": true}\n')
                with patch.object(optimizer.Tools, "run", side_effect=self.child(tools, "fresh")):
                    result = optimizer.compile_arm(tools, Path("A.lean"), root / ".lake/build/ir/A.setup.json",
                                                   arm, artifacts, source)
                self.assertEqual(len(result["artifacts"]), 7)
                self.assertNotEqual(result["artifacts"], previous)
                self.assertEqual(optimizer.artifact_receipt(artifacts, Path("B.lean")), sibling)
                self.assertEqual([(Path(row["path"]).stat().st_mtime_ns,
                                   Path(row["path"]).stat().st_mode) for row in sibling], sibling_identity)
                self.assertIn('"existing_before_child": 0', (arm / "compile.stdout").read_text())
                self.assertEqual((root / "A.lean").read_bytes(), recovery.ORIGINAL)

    def test_forced_receipts_require_all_seven_regular_nonempty_outputs(self) -> None:
        for suffix in SUFFIXES:
            for defect in ("missing", "empty", "symlink"):
                with self.subTest(suffix=suffix, defect=defect), tempfile.TemporaryDirectory() as directory:
                    artifacts = Path(directory).resolve() / "artifacts"
                    physical_parts(artifacts, Path("A.lean"))
                    output = artifacts / ("A" + suffix)
                    if defect == "empty":
                        output.write_bytes(b"")
                    else:
                        output.unlink()
                        if defect == "symlink":
                            other = Path(directory).resolve() / "other-output"
                            other.write_bytes(b"Nonempty symlink target\n")
                            output.symlink_to(other)
                    with self.assertRaisesRegex(ValueError, "nonempty target"):
                        optimizer.artifact_receipt(artifacts, Path("A.lean"), require_c=True)

    def test_incomplete_receipts_are_rejected_before_snapshot_and_on_resume(self) -> None:
        for name in ("baseline", "candidate"):
            for defect in ("missing", "empty"):
                with self.subTest(arm=name, defect=defect), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    result = CompilationOutputResumeTests.saved_evidence(root)
                    artifacts = Path(result[name]["artifact_root"])
                    ilean = artifacts / "A.ilean"
                    ilean.unlink() if defect == "missing" else ilean.write_bytes(b"")
                    result[name]["artifacts"] = optimizer.artifact_receipt(artifacts, Path("A.lean"))
                    with self.assertRaisesRegex(ValueError, "nonempty target .ilean"):
                        recovery.verify_saved_fixture(result, root)
        for batch in (False, True):
            for defect in ("missing", "empty"):
                with self.subTest(batch=batch, defect=defect), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arm, artifacts = root / "arm", root / "arm/artifacts"
                    physical_parts(artifacts, Path("A.lean"))
                    ilean = artifacts / "A.ilean"
                    ilean.unlink() if defect == "missing" else ilean.write_bytes(b"")
                    tools = optimizer.Tools(root, root, root / "lake", root / "lean", root, {}, 5,
                                            time_binary=root / "time")
                    tests = CompilationOutputResumeTests()
                    with patch.object(optimizer.Tools, "run",
                                      side_effect=tests.snapshot_external(artifacts, batch)) as child:
                        with self.assertRaisesRegex(ValueError, "nonempty target .ilean"):
                            tests.snapshot(tools, artifacts, arm, batch)
                        child.assert_not_called()


class CompilationModeTests(unittest.TestCase):
    LEGACY_SUFFIXES = (".olean", ".ilean", ".c")

    def test_forced_compile_uses_effective_pinned_mode_for_both_arms(self) -> None:
        for setup_mode, source_mode in ((False, False), (False, True), (True, False), (True, True)):
            for name, data in (("baseline", recovery.ORIGINAL), ("candidate", recovery.CANDIDATE)):
                with self.subTest(arm=name, setup_mode=setup_mode, source_mode=source_mode), \
                        tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    recovery.main_inputs(root, ("A",))
                    original = recovery.ORIGINAL if source_mode else recovery.ORIGINAL.removeprefix(b"module\n")
                    (root / "A.lean").write_bytes(original)
                    header = optimizer.decode_header(recovery.native_header(root / "A.lean", original,
                                                                             source_mode), original)
                    setup = root / ".lake/build/ir/A.setup.json"
                    metadata = optimizer.read_json(setup)
                    metadata["isModule"] = setup_mode
                    optimizer.write_json(setup, metadata)
                    suffixes = SUFFIXES if setup_mode or source_mode else self.LEGACY_SUFFIXES
                    tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                            root, {}, 5, root / "bin/time")
                    arm = tools.output / name
                    with patch.object(optimizer.Tools, "run", side_effect=FreshCompilationOutputTests.child(
                            tools, "fresh", suffixes)):
                        result = optimizer.compile_arm(tools, Path("A.lean"), setup, arm,
                                                       source_bytes=data if source_mode else
                                                       data.removeprefix(b"module\n"),
                                                       header_is_module=header.is_module)
                    self.assertEqual({Path(row["path"]).name for row in result["artifacts"]},
                                     {"A" + suffix for suffix in suffixes})
                    self.assertEqual(optimizer.read_json(arm / "setup.json")["isModule"], setup_mode)
                    self.assertEqual(result["header_is_module"], source_mode)
                    self.assertTrue(all(row["bytes"] > 0 for row in result["artifacts"]))

    def test_forced_legacy_receipts_require_all_three_regular_nonempty_outputs(self) -> None:
        for suffix in self.LEGACY_SUFFIXES:
            for defect in ("missing", "empty", "symlink"):
                with self.subTest(suffix=suffix, defect=defect), tempfile.TemporaryDirectory() as directory:
                    artifacts = Path(directory).resolve() / "artifacts"
                    physical_parts(artifacts, Path("A.lean"), self.LEGACY_SUFFIXES)
                    path = artifacts / ("A" + suffix)
                    if defect == "empty":
                        path.write_bytes(b"")
                    else:
                        path.unlink()
                        if defect == "symlink":
                            other = Path(directory).resolve() / "other"
                            other.write_bytes(b"Nonempty linked output\n")
                            path.symlink_to(other)
                    with self.assertRaisesRegex(ValueError, "nonempty target"):
                        optimizer.artifact_receipt(artifacts, Path("A.lean"), require_c=True, is_module=False)

    def test_legacy_single_and_shared_snapshots_use_the_pinned_setup_mode(self) -> None:
        for batch in (False, True):
            for wrong_mode in (False, True):
                with self.subTest(batch=batch, wrong_mode=wrong_mode), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arm, artifacts = root / "arm", root / "arm/artifacts"
                    physical_parts(artifacts, Path("A.lean"), self.LEGACY_SUFFIXES)
                    setup = arm / "setup.json"
                    dependency = arm / "fixture-import-part"
                    dependency.write_bytes(b"Explicitly mocked imported module bytes\n")
                    optimizer.write_json(setup, {"name": "A", "isModule": False,
                                                "importArts": {"Mathlib": [[str(dependency)], []]}})
                    tools = optimizer.Tools(root, root, root / "lake", root / "lean", root, {}, 5,
                                            time_binary=root / "time")
                    compilation = {"setup": optimizer.file_pin(setup), "header_is_module": False,
                                   "standard_library_root": None,
                                   "input_manifest": optimizer.pin_setup_inputs(tools, optimizer.read_json(setup))}
                    tests = CompilationOutputResumeTests()
                    with patch.object(optimizer.Tools, "run", side_effect=tests.snapshot_external(
                            artifacts, batch, is_module=wrong_mode)):
                        if wrong_mode:
                            with self.assertRaisesRegex(ValueError, "module mode"):
                                tests.snapshot(tools, artifacts, arm, batch, compilation)
                        else:
                            value = tests.snapshot(tools, artifacts, arm, batch, compilation)
                            snapshot = value["A"] if batch else value
                            self.assertFalse(snapshot["uses_module_system"])
                            self.assertEqual(snapshot["declaration_count"], 1)

    @classmethod
    def legacy_saved_evidence(cls, output: Path) -> dict[str, object]:
        result = CompilationOutputResumeTests.saved_evidence(output)
        directory = Path(result["attempt_directory"])
        production = Path(result["setup_path"])
        metadata = optimizer.read_json(production)
        metadata["isModule"] = False
        optimizer.write_json(production, metadata)
        result["setup_sha256"] = optimizer.sha256(production)
        for name, filename, key, source in (
                ("baseline", "owned-before.json", "owned_before_sha256", "original.lean"),
                ("candidate", "owned-after.json", "owned_after_sha256", "candidate.lean")):
            arm = result[name]
            source_path = directory / source
            data = source_path.read_bytes().removeprefix(b"module\n")
            if name == "candidate":
                data = (directory / "original.lean").read_bytes()
            source_path.write_bytes(data)
            Path(arm["source_path"]).write_bytes(data)
            key_hash = "source_sha256" if name == "baseline" else "candidate_sha256"
            result[key_hash] = arm["source_sha256"] = recovery.digest(data)
            setup = Path(arm["setup"]["path"])
            setup.write_bytes(production.read_bytes())
            arm.update(setup=optimizer.file_pin(setup), setup_source=optimizer.file_pin(production),
                       setup_sha256=result["setup_sha256"], header_is_module=False)
            artifacts = Path(arm["artifact_root"])
            for suffix in set(SUFFIXES) - set(cls.LEGACY_SUFFIXES):
                (artifacts / ("A" + suffix)).unlink()
            arm["artifacts"] = optimizer.artifact_receipt(artifacts, Path("A.lean"))
            recovery.bind_mock_snapshot_inputs(recovery.saved_fixture_tools(output), arm, Path("A.lean"))
            snapshot = optimizer.read_json(directory / filename)
            snapshot["uses_module_system"] = False
            optimizer.write_json(directory / filename, snapshot)
            result[key] = optimizer.sha256(directory / filename)
        native = Path(result["native_header"]["path"])
        original = directory / "original.lean"
        optimizer.write_json(native, recovery.native_header(output / "A.lean", original.read_bytes(), False))
        result["native_header"] = optimizer.file_pin(native)
        recovery.bind_saved_fixture_proposal(result, recovery.saved_fixture_tools(output))
        return result

    def test_false_setup_cannot_suppress_a_parsed_module_header(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            recovery.main_inputs(root, ("A",))
            native = recovery.native_header(root / "A.lean")
            header = optimizer.decode_header(native, (root / "A.lean").read_bytes())
            self.assertTrue(header.is_module)
            setup = root / ".lake/build/ir/A.setup.json"
            metadata = optimizer.read_json(setup)
            metadata["isModule"] = False
            optimizer.write_json(setup, metadata)
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {}, 5, root / "bin/time")
            arm = tools.output / "baseline"
            with patch.object(optimizer.Tools, "run", side_effect=FreshCompilationOutputTests.child(
                    tools, "fresh", self.LEGACY_SUFFIXES)):
                with self.assertRaisesRegex(ValueError, "nonempty target .olean.private"):
                    optimizer.compile_arm(tools, Path("A.lean"), setup, arm,
                                          header_is_module=header.is_module)
            self.assertEqual(optimizer.read_json(arm / "compile.json")["exit_code"], 0)
            self.assertFalse((arm / "compile-receipt.json").exists())

    def test_legacy_saved_resume_keeps_mode_bound_setup_and_output_guards(self) -> None:
        for defect in (None, "missing_ilean", "empty_c", "snapshot_mode", "header_mode", "native_header"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                result = self.legacy_saved_evidence(root)
                recovery.verify_saved_fixture(result, root)
                if defect is None:
                    continue
                artifacts = Path(result["candidate"]["artifact_root"])
                if defect == "missing_ilean":
                    (artifacts / "A.ilean").unlink()
                elif defect == "empty_c":
                    (artifacts / "A.c").write_bytes(b"")
                elif defect == "header_mode":
                    result["candidate"]["header_is_module"] = True
                elif defect == "native_header":
                    native = Path(result["native_header"]["path"])
                    header = optimizer.read_json(native)
                    header["is_module"] = True
                    optimizer.write_json(native, header)
                else:
                    directory = Path(result["attempt_directory"])
                    for filename, key in (("owned-before.json", "owned_before_sha256"),
                                          ("owned-after.json", "owned_after_sha256")):
                        snapshot = optimizer.read_json(directory / filename)
                        snapshot["uses_module_system"] = True
                        optimizer.write_json(directory / filename, snapshot)
                        result[key] = optimizer.sha256(directory / filename)
                with self.assertRaisesRegex(ValueError, "target|module mode|evidence file"):
                    recovery.verify_saved_fixture(result, root)

    def test_missing_or_nonboolean_setup_mode_does_not_relax_forced_checks(self) -> None:
        for mode in (None, "false", 0, 1):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                recovery.main_inputs(root, ("A",))
                setup = root / ".lake/build/ir/A.setup.json"
                metadata = optimizer.read_json(setup)
                if mode is None:
                    del metadata["isModule"]
                else:
                    metadata["isModule"] = mode
                optimizer.write_json(setup, metadata)
                tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                        root, {}, 5, root / "bin/time")
                with patch.object(optimizer.Tools, "run") as child:
                    with self.assertRaisesRegex(ValueError, "module mode"):
                        optimizer.compile_arm(tools, Path("A.lean"), setup, tools.output / "baseline")
                    child.assert_not_called()


if __name__ == "__main__":
    unittest.main()
