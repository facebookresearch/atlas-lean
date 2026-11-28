#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved. Licensed under the LICENSE in this repository.
"""Test archive validation and the fresh-directory restoration contract.

Set ATLAS_SNAPSHOT_VERIFY_SCRIPT to exercise another matching snapshot utility.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(os.environ.get(
    "ATLAS_SNAPSHOT_VERIFY_SCRIPT", str(Path(__file__).resolve().parents[1] / "verify_snapshot.py")))
SPEC = importlib.util.spec_from_file_location("snapshot_under_test", SCRIPT)
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)


def digest(data):
    return hashlib.sha256(data).hexdigest()


class SnapshotRestoreContract(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.sources = [
            ("MathlibExt/First.lean", b"-- first source\n"),
            ("MathlibExt/Sub/Second.lean", "-- second: λ\r\n".encode("utf-8")),
        ]

    def archive(self, *, separate_chunks=False, sources=None):
        sources = self.sources if sources is None else sources
        archive = self.root / "archive"
        archive.mkdir()
        groups = [[source] for source in sources] if separate_chunks else [sources]
        manifest = {"schema": "atlas.mathlibext-source-snapshot.v1",
                    "file_count": len(sources), "files": [], "chunks": []}
        for index, group in enumerate(groups, 1):
            name = f"part-{index:04d}.jsonl"
            rows = []
            for line_number, (path, data) in enumerate(group, 1):
                row = {"original_path": path, "original_sha256": digest(data),
                       "original_bytes": len(data), "source_text": data.decode("utf-8")}
                rows.append(row)
                manifest["files"].append({
                    key: row[key] for key in ("original_path", "original_sha256", "original_bytes")})
                manifest["files"][-1].update(snapshot_file=name, snapshot_line=line_number)
            chunk = b"".join((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8")
                             for row in rows)
            (archive / name).write_bytes(chunk)
            manifest["chunks"].append({"file": name, "sha256": digest(chunk),
                                       "bytes": len(chunk), "rows": len(rows)})
        path = archive / "manifest.json"
        path.write_text(json.dumps(manifest), encoding="utf-8")
        return path, manifest

    def test_valid_archive_restores_exact_bytes_to_new_directory(self):
        manifest_path, _ = self.archive()
        output = self.root / "new-parent" / "restored"
        result = VERIFIER.verify(manifest_path, output)
        self.assertEqual(result, {
            "verified_files": len(self.sources),
            "original_bytes": sum(len(data) for _, data in self.sources),
            "manifest_sha256": digest(manifest_path.read_bytes()), "byte_exact": True,
        })
        for path, data in self.sources:
            self.assertEqual((output / path).read_bytes(), data)
        self.assertEqual(VERIFIER.verify(manifest_path), result)

    def test_invalid_late_row_makes_no_output_or_parent(self):
        manifest_path, manifest = self.archive()
        chunk_path = manifest_path.parent / manifest["chunks"][0]["file"]
        rows = [json.loads(line) for line in chunk_path.read_bytes().splitlines()]
        rows[-1]["original_sha256"] = "0" * 64
        chunk = b"".join((json.dumps(row) + "\n").encode("utf-8") for row in rows)
        chunk_path.write_bytes(chunk)
        manifest["chunks"][0].update(sha256=digest(chunk), bytes=len(chunk))
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        output = self.root / "new-parent" / "restored"
        with self.assertRaisesRegex(ValueError, "original source hash or size mismatch"):
            VERIFIER.verify(manifest_path, output)
        self.assertFalse(output.parent.exists())

    def test_missing_late_archive_makes_no_output_or_parent(self):
        manifest_path, manifest = self.archive(separate_chunks=True)
        (manifest_path.parent / manifest["chunks"][-1]["file"]).unlink()
        output = self.root / "new-parent" / "restored"
        with self.assertRaises(FileNotFoundError):
            VERIFIER.verify(manifest_path, output)
        self.assertFalse(output.parent.exists())

    def test_malformed_late_json_row_makes_no_output_or_parent(self):
        manifest_path, manifest = self.archive()
        chunk_path = manifest_path.parent / manifest["chunks"][0]["file"]
        chunk = chunk_path.read_bytes().splitlines()[0] + b"\n{invalid JSON\n"
        chunk_path.write_bytes(chunk)
        manifest["chunks"][0].update(sha256=digest(chunk), bytes=len(chunk))
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        output = self.root / "new-parent" / "restored"
        with self.assertRaises(json.JSONDecodeError):
            VERIFIER.verify(manifest_path, output)
        self.assertFalse(output.parent.exists())

    def test_incomplete_manifest_scope_makes_no_output(self):
        manifest_path, manifest = self.archive()
        manifest["file_count"] += 1
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        output = self.root / "restored"
        with self.assertRaisesRegex(ValueError, "scope incomplete"):
            VERIFIER.verify(manifest_path, output)
        self.assertFalse(output.exists())

    def test_late_source_path_traversal_makes_no_output(self):
        sources = [self.sources[0], ("MathlibExt/../../escape.lean", self.sources[1][1])]
        manifest_path, _ = self.archive(sources=sources)
        output = self.root / "restored"
        with self.assertRaisesRegex(ValueError, "safe relative POSIX paths"):
            VERIFIER.verify(manifest_path, output)
        self.assertFalse(output.exists())
        self.assertFalse((self.root / "escape.lean").exists())

    def test_destination_symlink_is_rejected(self):
        manifest_path, _ = self.archive()
        outside = self.root / "outside"
        outside.mkdir()
        output = self.root / "restored"
        output.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "must not be symlinks"):
            VERIFIER.verify(manifest_path, output)
        self.assertEqual(list(outside.iterdir()), [])
        self.assertTrue(output.is_symlink())

    def test_broken_destination_symlink_is_rejected(self):
        manifest_path, _ = self.archive()
        outside = self.root / "missing"
        output = self.root / "restored"
        output.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "must not be symlinks"):
            VERIFIER.verify(manifest_path, output)
        self.assertFalse(outside.exists())
        self.assertTrue(output.is_symlink())

    def test_destination_ancestor_symlink_is_rejected(self):
        manifest_path, _ = self.archive()
        outside = self.root / "outside"
        outside.mkdir()
        parent = self.root / "parent"
        parent.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "must not be symlinks"):
            VERIFIER.verify(manifest_path, parent / "restored")
        self.assertEqual(list(outside.iterdir()), [])

    def test_archive_chunk_symlink_escape_is_rejected(self):
        manifest_path, manifest = self.archive()
        chunk_path = manifest_path.parent / manifest["chunks"][0]["file"]
        data = chunk_path.read_bytes()
        outside = self.root / "outside.jsonl"
        outside.write_bytes(data)
        chunk_path.unlink()
        chunk_path.symlink_to(outside)
        output = self.root / "restored"
        with self.assertRaisesRegex(ValueError, "resolves outside its root"):
            VERIFIER.verify(manifest_path, output)
        self.assertFalse(output.exists())
        self.assertEqual(outside.read_bytes(), data)

    def test_existing_destination_is_refused_without_modification(self):
        manifest_path, _ = self.archive()
        directory = self.root / "existing-directory"
        directory.mkdir()
        sentinel = directory / "keep.txt"
        sentinel.write_bytes(b"do not overwrite\n")
        file = self.root / "existing-file"
        file.write_bytes(b"keep this file\n")
        for output in (directory, file):
            with self.subTest(output=output.name):
                with self.assertRaises(FileExistsError):
                    VERIFIER.verify(manifest_path, output)
        self.assertEqual(sentinel.read_bytes(), b"do not overwrite\n")
        self.assertEqual(list(directory.iterdir()), [sentinel])
        self.assertEqual(file.read_bytes(), b"keep this file\n")


if __name__ == "__main__":
    unittest.main()
