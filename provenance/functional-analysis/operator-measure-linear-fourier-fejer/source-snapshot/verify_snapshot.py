#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved. Licensed under the LICENSE in this repository.
"""Verify complete source snapshot archives before restoring into a new directory."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative_path(value, *, source=False):
    if not isinstance(value, str) or not value or "\0" in value:
        raise ValueError("snapshot paths must be nonempty relative POSIX paths")
    path = PurePosixPath(value)
    if (path.is_absolute() or ".." in path.parts or "\\" in value or
            not path.parts or str(path) != value):
        raise ValueError("snapshot paths must be safe relative POSIX paths")
    if source and (path.parts[0] != "MathlibExt" or path.suffix != ".lean"):
        raise ValueError("source snapshot scope is restricted to MathlibExt Lean files")
    return Path(*path.parts)


def contained_path(root, relative):
    target = root / relative
    if not target.resolve().is_relative_to(root.resolve()):
        raise ValueError("snapshot path resolves outside its root")
    return target


def reject_symlink_ancestors(path):
    if any(parent.is_symlink() for parent in (path, *path.parents)):
        raise ValueError("restoration destination and ancestors must not be symlinks")


def fresh_destination(output):
    destination = Path.cwd() / output
    reject_symlink_ancestors(destination)
    if destination.exists():
        raise FileExistsError("restoration destination must not already exist")
    return destination.resolve()


def restore(sources, output):
    destination = fresh_destination(output)
    destination.parent.mkdir(parents=True, exist_ok=True)
    fresh_destination(destination)
    destination.mkdir()
    for source_path, data in sources:
        target = contained_path(destination, source_path)
        reject_symlink_ancestors(target)
        target.parent.mkdir(parents=True, exist_ok=True)
        reject_symlink_ancestors(target)
        contained_path(destination, source_path)
        with target.open("xb") as stream:
            stream.write(data)


def verify(manifest_path, output=None):
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    if manifest["schema"] != "atlas.mathlibext-source-snapshot.v1":
        raise ValueError("unsupported snapshot schema")
    expected = {entry["original_path"]: entry for entry in manifest["files"]}
    if len(expected) != len(manifest["files"]):
        raise ValueError("duplicate manifest source path")
    seen = set()
    sources = []
    total = 0
    for chunk in manifest["chunks"]:
        chunk_path = contained_path(manifest_path.parent, relative_path(chunk["file"]))
        chunk_bytes = chunk_path.read_bytes()
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
            sources.append((source_path, data))
            total += len(data)
    if seen != set(expected) or len(seen) != manifest["file_count"]:
        raise ValueError("source snapshot scope incomplete")
    if output is not None:
        restore(sources, output)
    return {"verified_files": len(seen), "original_bytes": total,
            "manifest_sha256": digest(manifest_bytes), "byte_exact": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--output", type=Path,
                        help="Restore after full validation into a new directory with no symlink ancestors")
    args = parser.parse_args()
    print(json.dumps(verify(args.manifest, args.output), sort_keys=True))
