#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Retry the real CLI with native sibling bytes and mocked Lean/Lake calls."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery
import test_import_optimizer_snapshot_inputs as shared


class BatchRetryTests(unittest.TestCase):
    def test_retry_preserves_verified_sibling_and_then_resumes_without_work(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = recovery.main_inputs(root, ("A", "B"))
            calls: list[tuple[str, object]] = []
            retry = False

            with tarfile.open(shared.ARCHIVE) as archive:
                member = archive.extractfile("input/Statement.ilean")
                prefix_member = archive.extractfile("input/original-compiler-prefix.json")
                assert member is not None and prefix_member is not None
                native_ilean = member.read()
                prefix = json.load(prefix_member)
            receipt = next(row for row in prefix["artifacts"] if row["path"].endswith(".ilean"))
            self.assertEqual((len(native_ilean), recovery.digest(native_ilean)),
                             (receipt["bytes"], receipt["sha256"]))
            native_module = prefix["module"]

            def external(argv: list[str], label: Path,
                         environment: dict[str, str] | None = None) -> dict[str, object]:
                label.parent.mkdir(parents=True, exist_ok=True)
                stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                if "shake" in argv:
                    modules = [argv[i + 1] for i, word in enumerate(argv) if word == "--only"]
                    calls.append(("shake", modules))
                    stdout.write_text("".join(f"{name}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                                              for name in modules))
                elif "build" in argv:
                    modules = [word[1:] for word in argv if word.startswith("+")]
                    calls.append(("prepare", modules))
                    stdout.write_text("External canonical build mocked: " + ",".join(modules) + "\n")
                elif "--deps" in argv:
                    scratch = Path(argv[-1]).read_text().splitlines()
                    modules = [line.removeprefix("import all ") for line in scratch]
                    self.assertTrue(all(line.startswith("import all ") for line in scratch))
                    calls.append(("deps", modules))
                    stdout.write_text("".join(str(Path(argv[-1]).parent / "artifacts" / (name + ".olean")) + "\n"
                                              for name in modules))
                elif "--run" in argv:
                    modules = argv[argv.index("--run") + 3:]
                    calls.append(("snapshot", modules))
                    assert environment is not None
                    snapshot_setup = optimizer.read_json(Path(argv[argv.index("--run") + 2]))
                    artifacts = Path(snapshot_setup["importArts"][modules[0]][0][0]).parent
                    self.assertEqual(environment["LEAN_PATH"], "")
                    self.assertEqual(artifacts, label.parent.parent / "artifacts")
                    rows = []
                    for name in modules:
                        row = recovery.SavedSnapshotRecoveryTests.snapshot(name, artifacts / (name + ".olean"))
                        row.update(batch_modules=modules, batch_module_count=len(modules),
                                   loaded_modules_scope="whole_batch", loaded_modules=[*modules, native_module],
                                   loaded_module_count=len(modules) + 1)
                        rows.append(row)
                    stdout.write_text("".join(json.dumps(row) + "\n" for row in rows))
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
                calls.append(("compile", (relative.stem, arm.name)))
                if relative.stem == "B" and not retry:
                    raise ValueError("External B baseline compiler mocked as blocked")
                outputs.physical_parts(artifact_root, relative)
                _, sibling = shared.native_sibling(artifact_root)
                if relative.stem == "B":
                    sibling.with_suffix(".ilean").write_bytes(native_ilean)
                return {"artifact_root": str(artifact_root), "artifacts": shared.EXTERNAL_ARTIFACTS,
                        **recovery.mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root)}

            def invoke(extra: list[str]) -> int:
                with patch.object(sys, "argv", [*arguments, *extra]):
                    return optimizer.main()

            def tree(path: Path) -> dict[str, bytes]:
                return {str(item.relative_to(path)): item.read_bytes()
                        for item in path.rglob("*") if item.is_file()}

            with patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=recovery.environment_stub), \
                    patch.object(optimizer.Tools, "run", side_effect=external), \
                    patch.object(optimizer, "artifact_receipt", return_value=shared.EXTERNAL_ARTIFACTS), \
                    patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(invoke([]), 1)
                journal = root / "output/results.jsonl"
                lines = journal.read_bytes().splitlines(keepends=True)
                first = [json.loads(line) for line in lines]
                self.assertEqual([(r["module"], r["status"]) for r in first],
                                 [("A", "verified"), ("B", "blocked")])
                self.assertEqual(first[0]["declaration_count"], 1)
                saved_a = first[0]
                shared_dirs = [Path(saved_a[name]["artifact_root"]).parent for name in ("baseline", "candidate")]
                snapshots = [tree(path) for path in shared_dirs]
                attempt = Path(saved_a["attempt_directory"])
                saved_attempt = tree(attempt)
                preparation = saved_a["baseline_build"]
                prepare_paths = [Path(preparation[name]) for name in ("stdout", "stderr")]
                prepare_paths.append(prepare_paths[0].with_suffix(".json"))
                prepare_bytes = {path: path.read_bytes() for path in prepare_paths}
                self.assertEqual([row[1] for row in calls if row[0] == "snapshot"], [["A"], ["A"]])
                retry = True
                self.assertEqual(invoke(["--resume", "--retry-blocked"]), 0)
                complete = optimizer.read_journal(journal, {"A.lean": recovery.digest(recovery.ORIGINAL),
                                                           "B.lean": recovery.digest(recovery.ORIGINAL)})
                self.assertEqual({key: value["status"] for key, value in complete.items()},
                                 {"A.lean": "verified", "B.lean": "verified"})
                self.assertEqual(complete["A.lean"], saved_a)
                self.assertEqual(journal.read_bytes().splitlines(keepends=True)[0], lines[0])
                completed_calls, complete_journal = list(calls), journal.read_bytes()
                self.assertEqual(invoke(["--resume"]), 0)
                self.assertEqual(calls, completed_calls)
                self.assertEqual(journal.read_bytes(), complete_journal)
                for path, expected in zip(shared_dirs, snapshots):
                    self.assertEqual(tree(path), expected)
                self.assertEqual(tree(attempt), saved_attempt)
                self.assertEqual({path: path.read_bytes() for path in prepare_paths}, prepare_bytes)
                self.assertEqual([row[1] for row in calls if row[0] == "compile"],
                                 [("A", "baseline"), ("A", "candidate"), ("B", "baseline"),
                                  ("B", "baseline"), ("B", "candidate")])
                self.assertEqual([row[1] for row in calls if row[0] == "snapshot"],
                                 [["A"], ["A"], ["B"], ["B"]])
                self.assertEqual((root / "A.lean").read_bytes(), recovery.ORIGINAL)
                self.assertEqual((root / "B.lean").read_bytes(), recovery.ORIGINAL)


if __name__ == "__main__":
    unittest.main()
