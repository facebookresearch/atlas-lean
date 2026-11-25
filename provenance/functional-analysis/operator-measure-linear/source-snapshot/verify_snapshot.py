#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved. Licensed under the LICENSE in this repository.
"""Verify or rehydrate readable MathlibExt source snapshot JSONL chunks."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

def digest(data):
    return hashlib.sha256(data).hexdigest()

def relative_path(value, *, source=False):
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "\\" in value:
        raise ValueError("snapshot paths must be safe relative POSIX paths")
    if source and (path.parts[0] != "MathlibExt" or path.suffix != ".lean"):
        raise ValueError("source snapshot scope is restricted to MathlibExt Lean files")
    return Path(*path.parts)

def verify(manifest_path, output=None):
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    if manifest["schema"] != "atlas.mathlibext-source-snapshot.v1":
        raise ValueError("unsupported snapshot schema")
    expected = {entry["original_path"]: entry for entry in manifest["files"]}
    if len(expected) != len(manifest["files"]):
        raise ValueError("duplicate manifest source path")
    seen = set()
    total = 0
    for chunk in manifest["chunks"]:
        chunk_bytes = (manifest_path.parent / relative_path(chunk["file"])).read_bytes()
        if digest(chunk_bytes) != chunk["sha256"] or len(chunk_bytes) != chunk["bytes"]:
            raise ValueError("snapshot chunk hash or size mismatch")
        lines = chunk_bytes.splitlines()
        if len(lines) != chunk["rows"]:
            raise ValueError("snapshot chunk row count mismatch")
        for line_number, line in enumerate(lines, 1):
            record = json.loads(line)
            name = record["original_path"]
            source_path = relative_path(name, source=True)
            if name in seen or name not in expected:
                raise ValueError("duplicate or unlisted source path")
            entry = expected[name]
            data = record["source_text"].encode("utf-8")
            if digest(data) != record["original_sha256"] or len(data) != record["original_bytes"]:
                raise ValueError("rehydrated original source hash or size mismatch")
            if (record["original_sha256"] != entry["original_sha256"] or
                    len(data) != entry["original_bytes"] or
                    chunk["file"] != entry["snapshot_file"] or
                    line_number != entry["snapshot_line"]):
                raise ValueError("source manifest binding mismatch")
            seen.add(name)
            total += len(data)
            if output is not None:
                target = output / source_path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
    if seen != set(expected) or len(seen) != manifest["file_count"]:
        raise ValueError("source snapshot scope incomplete")
    return {"verified_files": len(seen), "original_bytes": total,
            "manifest_sha256": digest(manifest_bytes), "byte_exact": True}

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.manifest, args.output), sort_keys=True))
