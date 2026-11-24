#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Resume admission tests using real marker executables, without Lean builds."""

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
from test_import_optimizer_recovery import ORIGINAL, main_inputs


def marker_executable(path: Path, marker: Path, event: str, body: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"#!{sys.executable}\n"
        "from pathlib import Path\nimport json, subprocess, sys\n"
        f"with Path({str(marker)!r}).open('a') as stream:\n"
        f"    stream.write({(event + chr(10))!r})\n" + body)
    path.chmod(0o755)


def executable_inputs(root: Path) -> tuple[list[str], dict[str, Path]]:
    arguments = main_inputs(root, ("A",)) + ["--timeout", "5"]
    manifest = root / "manifest.jsonl"
    row = json.loads(manifest.read_text())
    row["analysis_status"] = "helper_readonly"
    manifest.write_text(json.dumps(row) + "\n")
    marker = root / "executed.txt"
    selected = root / "selected-lake.txt"
    native_lake = root / "toolchain/bin/lake"
    native_lean = native_lake.with_name("lean")
    native_time = root / "native/time"
    launcher = root / "launchers/lake"
    marker_executable(native_lake, marker, "native_lake",
                      "print(json.dumps({'LAKE': str(Path(__file__).resolve()), "
                      "'LEAN_SYSROOT': str(Path(__file__).resolve().parents[1])}))\n")
    marker_executable(native_lean, marker, "native_lean", "print('unused compiler fixture')\n")
    marker_executable(native_time, marker, "time", "print('GNU time fixture')\n")
    marker_executable(launcher, marker, "lake_launcher",
                      f"subprocess.run([Path({str(selected)!r}).read_text().strip(), "
                      "*sys.argv[1:]], check=True)\n")
    marker_executable(root / "bin/lean", marker, "compiler_launcher",
                      "print('unused compiler launcher fixture')\n")
    selected.write_text(str(native_lake))
    for name, target in (("lake", launcher), ("time", native_time)):
        configured = root / "bin" / name
        configured.unlink()
        configured.symlink_to(target)
    return arguments, {"marker": marker, "selected": selected, "time": root / "bin/time",
                       "lake_launcher": root / "bin/lake", "compiler_launcher": root / "bin/lean",
                       "native_lake": native_lake, "native_compiler": native_lean}


def invoke(arguments: list[str]) -> int:
    with patch.object(sys, "argv", arguments), patch.object(optimizer.signal, "signal"), \
            patch.object(optimizer.Tools, "run",
                         side_effect=AssertionError("Read-only resume invoked a Lean/backend child")), \
            contextlib.redirect_stdout(io.StringIO()):
        return optimizer.main()


class ResumeExecutableTests(unittest.TestCase):
    def test_changed_executables_are_rejected_before_any_resume_child(self) -> None:
        for role in ("time", "lake_launcher", "compiler_launcher", "native_lake", "native_compiler"):
            for mutation in ("bytes", "resolved_path"):
                with self.subTest(role=role, mutation=mutation), \
                        tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arguments, paths = executable_inputs(root)
                    self.assertEqual(invoke(arguments), 0)
                    self.assertEqual(paths["marker"].read_text().splitlines(),
                                     ["time", "lake_launcher", "native_lake"])
                    before = {name: (root / "output" / name).read_bytes()
                              for name in ("run.json", "results.jsonl", "environment.json")}
                    paths["marker"].write_bytes(b"")
                    executable = paths[role]
                    if mutation == "bytes":
                        executable.write_bytes(executable.read_bytes() + b"\n# changed executable\n")
                    else:
                        replacement = executable.with_name(executable.name + "-replacement")
                        replacement.write_bytes(executable.read_bytes())
                        replacement.chmod(0o755)
                        executable.unlink()
                        executable.symlink_to(replacement)
                    with self.assertRaisesRegex(ValueError, "Resume inputs, compiler, or backend bytes changed"):
                        invoke(arguments + ["--resume"])
                    self.assertEqual(paths["marker"].read_bytes(), b"",
                                     "A changed executable ran before resume was rejected")
                    for name, data in before.items():
                        self.assertEqual((root / "output" / name).read_bytes(), data)
                    self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
                    self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_unchanged_resume_refreshes_environment_and_preserves_results(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments, paths = executable_inputs(root)
            self.assertEqual(invoke(arguments), 0)
            identity = (root / "output/run.json").read_bytes()
            journal = (root / "output/results.jsonl").read_bytes()
            self.assertEqual(json.loads(journal)["status"], "readonly")
            self.assertEqual(invoke(arguments + ["--resume"]), 0)
            self.assertEqual(paths["marker"].read_text().splitlines(),
                             ["time", "lake_launcher", "native_lake"] * 2)
            environment = optimizer.read_json(root / "output/environment.json")
            self.assertEqual(environment["exit_code"], 0)
            self.assertFalse(environment["timed_out"])
            self.assertEqual(optimizer.read_json(root / "output/environment.stdout")["LAKE"],
                             str(paths["native_lake"]))
            self.assertEqual((root / "output/run.json").read_bytes(), identity)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
            self.assertEqual(optimizer.read_json(root / "output/summary.json")["status_counts"]["readonly"], 1)
            self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
            self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_missing_saved_native_pin_rejects_before_environment_refresh(self) -> None:
        for field in ("lake_binary", "compiler_binary"):
            with self.subTest(field=field), \
                    tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments, paths = executable_inputs(root)
                self.assertEqual(invoke(arguments), 0)
                identity_path = root / "output/run.json"
                saved = optimizer.read_json(identity_path)
                del saved[field]
                optimizer.write_json(identity_path, saved)
                damaged = identity_path.read_bytes()
                journal = (root / "output/results.jsonl").read_bytes()
                paths["marker"].write_bytes(b"")
                with self.assertRaisesRegex(ValueError, "Resume inputs, compiler, or backend bytes changed"):
                    invoke(arguments + ["--resume"])
                self.assertEqual(paths["marker"].read_bytes(), b"")
                self.assertEqual(identity_path.read_bytes(), damaged)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_environment_refresh_cannot_replace_the_full_identity_check(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments, paths = executable_inputs(root)
            self.assertEqual(invoke(arguments), 0)
            before = {name: (root / "output" / name).read_bytes()
                      for name in ("run.json", "results.jsonl")}
            replacement = root / "other-toolchain/bin/lake"
            replacement.parent.mkdir(parents=True)
            replacement.write_bytes(paths["native_lake"].read_bytes())
            replacement.chmod(0o755)
            replacement.with_name("lean").write_bytes(paths["native_compiler"].read_bytes())
            paths["selected"].write_text(str(replacement))
            paths["marker"].write_bytes(b"")
            with self.assertRaisesRegex(ValueError, "Resume inputs, compiler, or backend bytes changed"):
                invoke(arguments + ["--resume"])
            self.assertEqual(paths["marker"].read_text().splitlines(),
                             ["time", "lake_launcher", "native_lake"])
            for name, data in before.items():
                self.assertEqual((root / "output" / name).read_bytes(), data)


if __name__ == "__main__":
    unittest.main()
