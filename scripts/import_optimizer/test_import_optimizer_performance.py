#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Input-cache and acceptance controls; external Lean calls are mocked."""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from collections.abc import Iterator
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_recovery as recovery


# Exact Lean 4.34.1 Lean/CoreM.ir.sig, SHA256 8928b3e2d19ae007e965104fc6b82dd747c3b93d4c58ed0cfcb41169072baaf6.
IR_SIGNATURE = bytes.fromhex(
    "6f6c65616e0201342e33342e31000000000000000000000000000000000000000000000000000000"
    "35303435643030353634313332363665353763363235646364376333363562313065333737633532"
    "0000711fa96600007800711fa966000000000000010000f600000000000000000000000000000000"
    "00000000380005006000711fa96600006000711fa96600006000711fa96600006000711fa9660000"
    "6000711fa96600000000000000000000")


def library_fixture(root: Path) -> tuple[optimizer.Tools, Path]:
    artifact = root / "lib/lean/Lean/CoreM.ir.sig"
    artifact.parent.mkdir(parents=True)
    artifact.write_bytes(IR_SIGNATURE)
    tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                            root / "bin/lean", root, {"LEAN_SYSROOT": str(root)}, 5,
                            time_binary=root / "bin/time")
    return tools, artifact


@contextlib.contextmanager
def candidate_cli(root: Path) -> Iterator[tuple[list[str], list[Path]]]:
    arguments = recovery.main_inputs(root, ("A",))
    library_fixture(root)
    compiles: list[Path] = []

    def external(argv: list[str], label: Path,
                 environment: dict[str, str] | None = None) -> dict[str, object]:
        label.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
        if "shake" in argv:
            stdout.write_text("A.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n")
        elif "build" in argv:
            stdout.write_text("External prepared-target mock\n")
        else:
            raise AssertionError(f"Unexpected external call: {argv}")
        stderr.write_text("")
        command = {"argv": argv, "cwd": str(root), "exit_code": 0, "timed_out": False,
                   "remaining_group_killed": False, "stdout": str(stdout), "stderr": str(stderr)}
        optimizer.write_json(Path(str(label) + ".json"), command)
        return command

    def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path, arm: Path,
                     artifact_root: Path | None = None, source_bytes: bytes | None = None,
                     *, header_is_module: bool = True) -> dict[str, object]:
        assert source_bytes is not None
        compiles.append(arm)
        return {"artifact_root": str(artifact_root),
                "artifacts": [{"external_artifacts_mock": True}],
                **recovery.mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root)}

    def snapshot_stub(tools: optimizer.Tools, rows: list[dict[str, object]],
                      artifacts: Path, arm: Path, compilations: dict[str, dict[str, object]]
                      ) -> dict[str, dict[str, object]]:
        return {"A": recovery.SavedSnapshotRecoveryTests.snapshot("A", artifacts / "A.olean")}

    with patch.dict(os.environ, {"LEAN_SYSROOT": str(root)}), \
            patch.object(optimizer.signal, "signal"), \
            patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
            patch.object(optimizer, "run_command", side_effect=recovery.environment_stub), \
            patch.object(optimizer.Tools, "run", side_effect=external), \
            patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
            patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
            patch.object(optimizer, "snapshot_batch", side_effect=snapshot_stub), \
            contextlib.redirect_stdout(io.StringIO()):
        yield arguments, compiles


class StandardLibraryInventoryTests(unittest.TestCase):
    def test_warm_input_validation_does_not_walk_the_library_again(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tools, artifact = library_fixture(Path(directory).resolve())
            walk = Path.rglob
            visits: list[Path] = []

            def counted(path: Path, pattern: str) -> Iterator[Path]:
                visits.append(path)
                return walk(path, pattern)

            with patch.object(Path, "rglob", new=counted):
                original = optimizer.pin_setup_inputs(tools, {"importArts": {}})
                self.assertGreater(len(visits), 0)
                visits.clear()
                for _ in range(3):
                    self.assertEqual(optimizer.pin_setup_inputs(tools, {"importArts": {}}), original)
                self.assertEqual(visits, [])
            records = optimizer.read_json(Path(str(original["path"])))["files"]
            self.assertEqual([row["path"] for row in records], [str(artifact)])

    def test_cached_inventory_rejects_changed_directory_membership(self) -> None:
        for mutation in ("add_file", "add_directory", "remove_file", "rename_directory", "remove_root"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                tools, artifact = library_fixture(Path(directory).resolve())
                original = optimizer.pin_setup_inputs(tools, {"importArts": {}})
                manifest = Path(str(original["path"])).read_bytes()
                if mutation == "add_file":
                    (artifact.parent / "Other.ir.sig").write_bytes(IR_SIGNATURE)
                elif mutation == "add_directory":
                    (artifact.parent / "Other").mkdir()
                elif mutation == "remove_file":
                    artifact.unlink()
                elif mutation == "rename_directory":
                    artifact.parent.rename(artifact.parent.with_name("Other"))
                else:
                    artifact.parents[1].rename(artifact.parents[1].with_name("old-lean"))
                with self.assertRaises((ValueError, OSError)):
                    optimizer.pin_setup_inputs(tools, {"importArts": {}})
                self.assertEqual(Path(str(original["path"])).read_bytes(), manifest)

    def test_cached_inventory_revalidates_changed_file_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tools, artifact = library_fixture(Path(directory).resolve())
            original = optimizer.pin_setup_inputs(tools, {"importArts": {}})
            artifact.write_bytes(IR_SIGNATURE + b"corrupted\n")
            with self.assertRaisesRegex(ValueError, "evidence file changed"):
                optimizer.pin_setup_inputs(tools, {"importArts": {}})
            self.assertEqual(optimizer.read_json(Path(str(original["path"])))["files"][0]["sha256"],
                             recovery.digest(IR_SIGNATURE))

    def test_compilation_rejects_transient_file_and_directory_edits(self) -> None:
        for mutation in ("restored_bytes", "directory"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                recovery.main_inputs(root, ("A",))
                tools, artifact = library_fixture(root)

                def external(argv: list[str], label: Path,
                             environment: dict[str, str] | None = None) -> dict[str, object]:
                    if mutation == "restored_bytes":
                        artifact.write_bytes(IR_SIGNATURE + b"changed\n")
                        artifact.write_bytes(IR_SIGNATURE)
                    else:
                        (artifact.parent / "New").mkdir()
                    Path(argv[argv.index("-o") + 1]).write_text(json.dumps({
                        "wall_seconds": 0, "user_seconds": 0, "system_seconds": 0, "max_rss_kib": 0}) + "\n")
                    return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "external_lean_mock": True}

                with patch.object(optimizer.Tools, "run", side_effect=external), \
                        patch.object(optimizer, "artifact_receipt",
                                     return_value=[{"external_artifacts_mock": True}]) as artifacts:
                    with self.assertRaisesRegex(ValueError, "changed"):
                        optimizer.compile_arm(tools, Path("A.lean"), root / ".lake/build/ir/A.setup.json",
                                              tools.output / "baseline", source_bytes=recovery.ORIGINAL)
                    artifacts.assert_not_called()


class FreshCandidateAcceptanceTests(unittest.TestCase):
    def test_fresh_candidate_checks_creation_and_journal_once_each(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            verification = optimizer.verify_saved_candidate
            stages: list[str] = []

            def counted(result: dict[str, object], output: Path,
                        tools: optimizer.Tools | None = None) -> None:
                stages.append(str(result["status"]))
                verification(result, output, tools)

            with candidate_cli(root) as (arguments, compiles), \
                    patch.object(optimizer, "verify_saved_candidate", side_effect=counted):
                with patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                self.assertEqual(stages, ["compiled", "verified"])
                journal = (root / "output/results.jsonl").read_bytes()
                self.assertEqual(json.loads(journal)["status"], "verified")
                stages.clear()
                with patch.object(sys, "argv", [*arguments, "--resume"]):
                    self.assertEqual(optimizer.main(), 0)
                self.assertEqual(stages, ["verified"])
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
                self.assertEqual(len(compiles), 2)

    def test_final_journal_check_rejects_post_creation_input_change(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            verification = optimizer.verify_saved_candidate
            calls: list[str] = []

            def mutate(result: dict[str, object], output: Path,
                       tools: optimizer.Tools | None = None) -> None:
                calls.append(str(result["status"]))
                verification(result, output, tools)
                if result["status"] == "verified":
                    artifact = root / "lib/lean/Lean/CoreM.ir.sig"
                    artifact.write_bytes(IR_SIGNATURE + b"changed after creation\n")

            with candidate_cli(root) as (arguments, compiles), \
                    patch.object(optimizer, "verify_saved_candidate", side_effect=mutate), \
                    patch.object(sys, "argv", arguments):
                with self.assertRaisesRegex(ValueError, "evidence file changed"):
                    optimizer.main()
                self.assertEqual(calls, ["compiled", "verified"])
                self.assertEqual((root / "output/results.jsonl").read_bytes(), b"")
                self.assertEqual(len(compiles), 2)
                self.assertEqual((root / "A.lean").read_bytes(), recovery.ORIGINAL)


if __name__ == "__main__":
    unittest.main()
