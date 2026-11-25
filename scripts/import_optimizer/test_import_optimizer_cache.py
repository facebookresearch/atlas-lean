#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Cache controls use real source files; external Lean and Lake are mocked."""

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
from test_import_optimizer_recovery import (
    ORIGINAL, digest, environment_stub, main_inputs, mock_no_change_proposals, native_header,
    time_version_stub,
)


@contextlib.contextmanager
def runtime_stubs(root: Path, failed_header: str | None = None,
                  transient_source: Path | None = None) -> Iterator[list[list[str]]]:
    native_calls: list[list[str]] = []

    def lake_stub(argv: list[str], label: Path,
                  environment: dict[str, str] | None = None) -> dict[str, object]:
        label.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
        if "--run" in argv:
            native_calls.append(argv)
            headers = []
            for name in argv[argv.index("--run") + 2:]:
                if Path(name) == transient_source:
                    transient_source.write_bytes(ORIGINAL.replace(b"Mathlib", b"Other__"))
                row = native_header(Path(name))
                if Path(name) == transient_source:
                    transient_source.write_bytes(ORIGINAL)
                if Path(name).name == failed_header:
                    row.update(status="parse_error", parse_errors=["External parser error fixture"])
                headers.append(row)
            stdout.write_text("".join(json.dumps(row) + "\n" for row in headers))
        else:
            if "build" not in argv:
                raise AssertionError(f"Unexpected external command: {argv}")
            stdout.write_text("External Lake build fixture\n")
        stderr.write_text("")
        return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stdout": str(stdout), "stderr": str(stderr)}

    with patch.object(optimizer.signal, "signal"), \
            patch.object(optimizer.subprocess, "check_output", side_effect=time_version_stub), \
            patch.object(optimizer, "run_command", side_effect=environment_stub), \
            patch.object(optimizer.Tools, "run", side_effect=lake_stub), \
            patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifact_mock": True}]), \
            patch.object(optimizer, "analyze_batch", side_effect=mock_no_change_proposals), \
            patch.object(optimizer, "compile_arm", side_effect=AssertionError("Unexpected Lean compile")), \
            contextlib.redirect_stdout(io.StringIO()):
        yield native_calls


def arguments_without_headers(root: Path) -> list[str]:
    arguments = main_inputs(root, ("A", "B"))
    index = arguments.index("--headers")
    del arguments[index:index + 2]
    return arguments + ["--batch-size", "1", "--max-batches", "1"]


class NativeHeaderReuseTests(unittest.TestCase):
    def test_edit_then_restore_during_native_parse_is_not_pinned(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = arguments_without_headers(root)
            source = root / "A.lean"
            before = optimizer.source_identity(source)
            with runtime_stubs(root, transient_source=source) as native_calls, \
                    patch.object(sys, "argv", arguments):
                with self.assertRaisesRegex(ValueError, "Native header source changed during parsing"):
                    optimizer.main()
            self.assertEqual(source.read_bytes(), ORIGINAL)
            self.assertNotEqual(optimizer.source_identity(source), before)
            self.assertEqual(len(native_calls), 1)
            self.assertIsNone(optimizer.read_json(root / "output/run.json")["generated_headers_sha256"])
            self.assertFalse((root / "output/results.jsonl").exists())

    def test_actual_main_resume_reuses_generated_cache_and_completes_pending_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = arguments_without_headers(root)
            with runtime_stubs(root) as native_calls:
                with patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                cache = root / "output/native-headers.jsonl"
                saved = cache.read_bytes()
                timestamp = cache.stat().st_mtime_ns
                self.assertEqual(optimizer.read_json(root / "output/summary.json")["pending_count"], 1)
                self.assertEqual(optimizer.read_json(root / "output/run.json")["generated_headers_sha256"],
                                 digest(saved))
                with patch.object(sys, "argv", arguments + ["--resume"]):
                    self.assertEqual(optimizer.main(), 0)
                rows = [json.loads(line) for line in (root / "output/results.jsonl").read_text().splitlines()]
                self.assertEqual([(row["path"], row["status"]) for row in rows],
                                 [("A.lean", "no_change"), ("B.lean", "no_change")])
                self.assertEqual(optimizer.read_json(root / "output/summary.json")["pending_count"], 0)
                self.assertEqual(len(native_calls), 1)
                self.assertEqual(cache.read_bytes(), saved)
                self.assertEqual(cache.stat().st_mtime_ns, timestamp)
            self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_tampered_or_missing_generated_cache_preserves_journal_and_identity(self) -> None:
        for mutation in ("bytes", "missing"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = arguments_without_headers(root)
                with runtime_stubs(root) as native_calls:
                    with patch.object(sys, "argv", arguments):
                        self.assertEqual(optimizer.main(), 0)
                    cache = root / "output/native-headers.jsonl"
                    journal = (root / "output/results.jsonl").read_bytes()
                    identity = (root / "output/run.json").read_bytes()
                    if mutation == "bytes":
                        cache.write_bytes(cache.read_bytes() + b"\n")
                    else:
                        cache.unlink()
                    with patch.object(sys, "argv", arguments + ["--resume"]):
                        with self.assertRaisesRegex(ValueError, "Generated native header cache"):
                            optimizer.main()
                    self.assertEqual(len(native_calls), 1)
                    self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
                    self.assertEqual((root / "output/run.json").read_bytes(), identity)
                    self.assertEqual(cache.exists(), mutation == "bytes")

    def test_failed_header_row_is_preserved_and_reused_as_blocked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = arguments_without_headers(root)
            with runtime_stubs(root, failed_header="B.lean") as native_calls:
                with patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                cache = root / "output/native-headers.jsonl"
                saved = cache.read_bytes()
                with patch.object(sys, "argv", arguments + ["--resume"]):
                    self.assertEqual(optimizer.main(), 1)
                rows = [json.loads(line) for line in (root / "output/results.jsonl").read_text().splitlines()]
                self.assertEqual([(row["path"], row["status"]) for row in rows],
                                 [("A.lean", "no_change"), ("B.lean", "blocked")])
                self.assertEqual(len(native_calls), 1)
                self.assertEqual(cache.read_bytes(), saved)


class SourceIdentityCacheTests(unittest.TestCase):
    def test_real_main_batches_hash_unchanged_inventory_only_once(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B", "C")) + ["--batch-size", "1"]
            counts = {root / (name + ".lean"): 0 for name in ("A", "B", "C")}
            actual = optimizer.sha256

            def counted(path: Path) -> str:
                if path in counts:
                    counts[path] += 1
                return actual(path)

            with runtime_stubs(root), patch.object(optimizer, "sha256", side_effect=counted), \
                    patch.object(sys, "argv", arguments):
                self.assertEqual(optimizer.main(), 0)
            # Initial inventory validation and each module's final no-change check.
            self.assertEqual(counts, {path: 2 for path in counts})
            self.assertEqual(optimizer.read_json(root / "output/summary.json")["result_count"], 3)

    def test_metadata_changes_rehash_without_hiding_same_size_dependency_edit(self) -> None:
        for mutation in ("mode", "mtime", "inode", "same_size_edit"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                main_inputs(root, ("A", "B"))
                rows = [json.loads(line) for line in (root / "manifest.jsonl").read_text().splitlines()]
                cache: optimizer.SourceCache = {}
                optimizer.validate_inventory_sources(root, rows, cache)
                source = root / "B.lean"
                before = source.stat()
                if mutation == "mode":
                    source.chmod(0o444)
                elif mutation == "mtime":
                    os.utime(source, ns=(before.st_atime_ns, before.st_mtime_ns + 1))
                elif mutation == "inode":
                    replacement = root / "replacement"
                    replacement.write_bytes(ORIGINAL)
                    os.utime(replacement, ns=(before.st_atime_ns, before.st_mtime_ns))
                    replacement.replace(source)
                    self.assertNotEqual(source.stat().st_ino, before.st_ino)
                else:
                    source.write_bytes(ORIGINAL.replace(b":= 0", b":= 1"))
                    os.utime(source, ns=(before.st_atime_ns, before.st_mtime_ns))
                    self.assertEqual(source.stat().st_size, before.st_size)
                    self.assertEqual(source.stat().st_mtime_ns, before.st_mtime_ns)
                with patch.object(optimizer, "sha256", wraps=optimizer.sha256) as hashed:
                    if mutation == "same_size_edit":
                        with self.assertRaisesRegex(ValueError, "Inventory source hash changed"):
                            optimizer.validate_inventory_sources(root, rows, cache)
                    else:
                        optimizer.validate_inventory_sources(root, rows, cache)
                    hashed.assert_called_once_with(source)
                self.assertEqual(source.read_bytes(), ORIGINAL if mutation != "same_size_edit" else
                                 ORIGINAL.replace(b":= 0", b":= 1"))

    def test_edit_after_hash_is_preserved_and_not_cached(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            main_inputs(root, ("A", "B"))
            rows = [json.loads(line) for line in (root / "manifest.jsonl").read_text().splitlines()]
            cache: optimizer.SourceCache = {}
            source = root / "B.lean"
            actual = optimizer.sha256
            changed = ORIGINAL.replace(b":= 0", b":= 1")

            def edit_after_hash(path: Path) -> str:
                result = actual(path)
                if path == source:
                    source.write_bytes(changed)
                return result

            with patch.object(optimizer, "sha256", side_effect=edit_after_hash):
                with self.assertRaisesRegex(ValueError, "Inventory source changed while hashing"):
                    optimizer.validate_inventory_sources(root, rows, cache)
            self.assertEqual(source.read_bytes(), changed)
            self.assertNotIn("B.lean", cache)

    def test_cached_identity_also_requires_the_same_expected_hash(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            main_inputs(root, ("A",))
            rows = [json.loads(line) for line in (root / "manifest.jsonl").read_text().splitlines()]
            cache: optimizer.SourceCache = {}
            optimizer.validate_inventory_sources(root, rows, cache)
            rows[0]["source_sha256"] = "0" * 64
            with patch.object(optimizer, "sha256", wraps=optimizer.sha256) as hashed:
                with self.assertRaisesRegex(ValueError, "Inventory source hash changed"):
                    optimizer.validate_inventory_sources(root, rows, cache)
                hashed.assert_called_once_with(root / "A.lean")


if __name__ == "__main__":
    unittest.main()
