#!/usr/bin/env python3
"""Inventory pinned v1 target/report metadata without compiling or scanning Lean."""

import argparse
from collections import Counter, defaultdict
import ctypes
import decimal
import errno
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile

import yaml

FIELDS = {"description", "kind", "location", "name"}
HISTORICAL = "HISTORICAL ONLY"
SCHEMA = "atlas-v1-inventory/2"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


class StrictSafeLoader(yaml.SafeLoader):
    """Safe YAML, without aliases, merges or silently overwritten mapping keys."""

    def compose_node(self, parent, index):
        if self.check_event(yaml.AliasEvent):
            raise ValueError("YAML aliases are not supported")
        return super().compose_node(parent, index)

    def construct_mapping(self, node, deep=False):
        result = {}
        for key_node, value_node in node.value:
            if key_node.tag != "tag:yaml.org,2002:str":
                raise ValueError(
                    "YAML mapping keys must be strings; merges are unsupported"
                )
            key = self.construct_object(key_node, deep=deep)
            if key in result:
                raise ValueError(f"Duplicate YAML key: {key}")
            result[key] = self.construct_object(value_node, deep=deep)
        return result


def parse_targets(data):
    text = data.decode("utf-8")
    loader = StrictSafeLoader(text)
    try:
        node = loader.get_single_node()
        if not isinstance(node, yaml.SequenceNode) or not node.value:
            raise ValueError("Targets must be a nonempty YAML sequence")
        values = loader.construct_document(node)
        targets = []
        for value, item in zip(values, node.value):
            if (
                not isinstance(value, dict)
                or set(value) != FIELDS
                or any(not isinstance(v, str) for v in value.values())
            ):
                raise ValueError("Each target must have exactly four string fields")
            # Block mapping end marks absorb separator trivia. Scalar extents
            # preserve quoted/block content (including keep-chomping blanks).
            # Flow mappings also need their closing brace in the raw span.
            end_mark = (
                item.end_mark
                if item.flow_style
                else max(
                    (part.end_mark for pair in item.value for part in pair),
                    key=lambda mark: mark.index,
                )
            )
            start = len(text[: item.start_mark.index].encode("utf-8"))
            end = len(text[: end_mark.index].encode("utf-8"))
            targets.append(
                {
                    "fields": value,
                    "source_sha256": sha256(canonical(value)),
                    "span": {
                        "byte_start": start,
                        "byte_end": end,
                        "line_start": item.start_mark.line + 1,
                        "line_end": end_mark.line + (1 if end_mark.column else 0),
                        "raw_sha256": sha256(data[start:end]),
                    },
                }
            )
        return targets
    finally:
        loader.dispose()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f"Non-finite JSON value: {value}")


def finite_float(literal):
    value = float(literal)
    if not math.isfinite(value):
        raise ValueError(f"Non-finite JSON number: {literal}")
    # Reject literals whose decimal value binary floating point cannot
    # represent faithfully (underflow such as 1e-9999 -> 0.0, or extra
    # precision silently rounded away): the inventory retains historical
    # claims unmodified and hashes them, so an altered value is worse
    # than an explicit failure.  Values whose shortest repr denotes the
    # same decimal (such as 0.1) round-trip exactly and are accepted.
    if decimal.Decimal(literal) != decimal.Decimal(repr(value)):
        raise ValueError(f"JSON number not exactly representable: {literal}")
    return value


def parse_report(data):
    report = json.loads(
        data,
        object_pairs_hook=unique_object,
        parse_constant=reject_constant,
        parse_float=finite_float,
    )
    if not isinstance(report, dict) or not isinstance(report.get("statements"), dict):
        raise ValueError("Report must contain a statements object")
    details = report["statements"].get("details")
    if not isinstance(details, list):
        raise ValueError("Report statements.details must be a list")
    for row in details:
        if (
            not isinstance(row, dict)
            or type(row.get("idx")) is not int
            or row["idx"] < 0
        ):
            raise ValueError("Report rows must have a nonnegative integer idx")
        if any(not isinstance(row.get(field), str) for field in FIELDS):
            raise ValueError("Report target metadata must have four string fields")
        for field in ("lean_declaration", "lean_file", "deps"):
            if row.get(field) is not None and not isinstance(row[field], str):
                raise ValueError(f"Report {field} must be a string or null")
    return report


# Repository-selecting Git environment settings must never redirect a
# pinned snapshot read to a different repository or object store.
_FORBIDDEN_GIT_ENV = {
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_CEILING_DIRECTORIES",
    "GIT_COMMON_DIR",
    "GIT_CONFIG",
    "GIT_CONFIG_COUNT",
    "GIT_CONFIG_GLOBAL",
    "GIT_CONFIG_LOCAL",
    "GIT_CONFIG_SYSTEM",
    "GIT_DIR",
    "GIT_DISCOVERY_ACROSS_FILESYSTEM",
    "GIT_INDEX_FILE",
    "GIT_NAMESPACE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_WORK_TREE",
}


def _git_env():
    env = {
        key: value
        for key, value in os.environ.items()
        if key not in _FORBIDDEN_GIT_ENV
        and not key.startswith(("GIT_CONFIG_KEY_", "GIT_CONFIG_VALUE_"))
    }
    env["GIT_OPTIONAL_LOCKS"] = "0"
    # A local refs/replace entry must not substitute replacement bytes
    # for the pinned commit's actual tree.
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    return env


class GitSource:
    def __init__(self, repo, ref):
        self.repo = str(repo)
        self.commands = []
        self.revision = (
            self.run("rev-parse", "--verify", "--end-of-options", ref + "^{commit}")
            .decode()
            .strip()
        )
        self.tree = {}
        for entry in self.run("ls-tree", "-r", "-l", "-z", self.revision).split(b"\0"):
            if entry:
                header, path = entry.decode("utf-8").split("\t", 1)
                mode, kind, blob, size = header.split()
                self.tree[path] = {
                    "git_blob": blob,
                    "kind": kind,
                    "mode": mode,
                    "bytes": int(size) if size.isdigit() else None,
                }

    def run(self, *args):
        command = ["git", "-C", self.repo, *args]
        self.commands.append(command)
        return subprocess.check_output(command, env=_git_env())

    def read(self, path):
        if self.tree[path]["kind"] != "blob" or self.tree[path]["mode"] != "100644":
            raise ValueError(f"Expected a regular metadata file: {path}")
        return self.run("show", self.revision + ":" + path)

    def provenance(self, path, data=None):
        record = {"revision": self.revision, "path": path, **self.tree[path]}
        if data is not None:
            record["sha256"] = sha256(data)
        return record


def split_names(value):
    return [name.strip() for name in (value or "").split(",") if name.strip()]


def historical(value):
    return {"evidence": HISTORICAL, "claims": value}


def roadmap_paths(prior, book):
    paths = defaultdict(list)
    if prior is not None:
        for path in prior.tree:
            parts = PurePosixPath(path).parts
            match = re.match(r"^(\d+)-.*\.md$", parts[-1])
            if (
                path.startswith("blueprint/roadmap/")
                and len(parts) >= 5
                and parts[3] == book
                and match
            ):
                paths[int(match[1]) - 1].append(prior.provenance(path))
    return paths


def book_inventory(source, book, prior=None):
    root = f"v1/Atlas/{book}"
    target_path = root + "/targets.yaml"
    report_path = root + "/report.json"
    target_data = source.read(target_path) if target_path in source.tree else None
    report_data = source.read(report_path) if report_path in source.tree else None
    targets = parse_targets(target_data) if target_data is not None else []
    report = parse_report(report_data) if report_data is not None else None
    details = report["statements"]["details"] if report is not None else []
    by_idx = defaultdict(list)
    declaration_targets = defaultdict(set)
    for ordinal, row in enumerate(details):
        by_idx[row["idx"]].append((ordinal, row))
        for name in split_names(row.get("lean_declaration")):
            declaration_targets[name].add(row["idx"])
    duplicates = defaultdict(list)
    for ordinal, target in enumerate(targets):
        duplicates[target["source_sha256"]].append(ordinal)
    pointers = roadmap_paths(prior, book)
    records = []
    for ordinal, target in enumerate(targets):
        gaps = []
        matches = []
        rows = by_idx[ordinal]
        if not rows:
            gaps.append(
                "missing_report_row" if report is not None else "missing_report_file"
            )
        if len(rows) > 1:
            gaps.append("ambiguous_report_ordinal")
        for report_ordinal, row in rows:
            difference = sorted(
                field
                for field in FIELDS
                if " ".join(row[field].split())
                != " ".join(target["fields"][field].split())
            )
            if difference:
                gaps.append("report_metadata_differs")
            files = []
            for path in split_names(row.get("lean_file")):
                path = path if path.startswith("v1/") else "v1/" + path
                if path in source.tree:
                    files.append(source.provenance(path))
                else:
                    files.append({"path": path, "missing": True})
                    gaps.append("reported_file_missing")
            declarations = split_names(row.get("lean_declaration"))
            if not declarations:
                gaps.append("no_reported_declaration")
            matches.append(
                {
                    "report_row_ordinal": report_ordinal,
                    "report_row_sha256": sha256(canonical(row)),
                    "declarations": declarations,
                    "files": files,
                    "metadata_difference_fields": difference,
                    "historical_report": historical(row),
                }
            )
        records.append(
            {
                "schema": SCHEMA,
                "key": {
                    "book": book,
                    "target_ordinal": ordinal,
                    "source_sha256": target["source_sha256"],
                },
                "source": source.provenance(target_path, target_data),
                "source_span": target["span"],
                "source_fields": target["fields"],
                "legacy_matches": matches,
                "duplicate_source_ordinals": (
                    duplicates[target["source_sha256"]]
                    if len(duplicates[target["source_sha256"]]) > 1
                    else []
                ),
                "prior_roadmap_candidates": pointers[ordinal],
                "gaps": sorted(set(gaps)),
            }
        )
    metadata = {
        key: value for key, value in (report or {}).items() if key != "statements"
    }
    if report is not None:
        metadata["statements"] = {
            key: value
            for key, value in report["statements"].items()
            if key != "details"
        }
    summary = {
        "book": book,
        "target_count": len(targets),
        "report_row_count": len(details),
        "sources": [
            source.provenance(path, data)
            for path, data in ((target_path, target_data), (report_path, report_data))
            if data is not None
        ],
        "missing_metadata_files": [
            path
            for path, data in ((target_path, target_data), (report_path, report_data))
            if data is None
        ],
        "historical_report_metadata": historical(metadata),
        "orphan_report_rows": [
            {
                "report_row_ordinal": ordinal,
                "report_row_sha256": sha256(canonical(row)),
                "historical_report": historical(row),
            }
            for ordinal, row in enumerate(details)
            if row["idx"] >= len(targets)
        ],
        "reported_declaration_reference_count": sum(
            len(split_names(row.get("lean_declaration"))) for row in details
        ),
        "reported_unique_declaration_name_count": len(declaration_targets),
        "shared_reported_declarations": {
            name: sorted(indices)
            for name, indices in declaration_targets.items()
            if len(indices) > 1
        },
        "report_mentioned_non_target_dependencies": sorted(
            {name for row in details for name in split_names(row.get("deps"))}
            - declaration_targets.keys()
        ),
        "gap_counts": dict(Counter(gap for row in records for gap in row["gaps"])),
    }
    return records, summary


def rename_no_replace(source, destination):
    """Publish atomically without the empty-directory overwrite race of rename."""
    try:
        rename = ctypes.CDLL(None, use_errno=True).renameat2
    except AttributeError:
        raise OSError(
            errno.ENOSYS, "Atomic publication requires Linux renameat2"
        ) from None
    rename.argtypes = [
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_uint,
    ]
    rename.restype = ctypes.c_int
    # AT_FDCWD = -100; RENAME_NOREPLACE = 1. No destructive fallback.
    if rename(-100, os.fsencode(source), -100, os.fsencode(destination), 1):
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error), os.fspath(destination))


def publish_outputs(output, inventory_data, manifest_data):
    if not sys.platform.startswith("linux"):
        raise OSError(errno.ENOSYS, "Atomic publication requires Linux renameat2")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        dir=output.parent, prefix=f".{output.name}.tmp-"
    ) as directory:
        temporary = Path(directory)
        for name, data in (
            ("inventory.jsonl", inventory_data),
            ("manifest.json", manifest_data),
        ):
            with (temporary / name).open("wb") as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
        descriptor = os.open(temporary, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        rename_no_replace(temporary, output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=".")
    parser.add_argument("--base", required=True)
    parser.add_argument(
        "--prior",
        help="Optional existing blueprint commit, used for path pointers only",
    )
    parser.add_argument("--book", help="Limit the inventory to one book")
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="New output directory; never overwritten",
    )
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("Output directory already exists")
    source = GitSource(args.repo, args.base)
    prior = GitSource(args.repo, args.prior) if args.prior else None
    books = sorted(
        {
            PurePosixPath(path).parent.name
            for path in source.tree
            if re.fullmatch(r"v1/Atlas/[^/]+/(targets\.yaml|report\.json)", path)
        }
    )
    if args.book:
        if args.book not in books:
            raise ValueError(f"Unknown book: {args.book}")
        books = [args.book]
    if not books:
        raise ValueError("No v1 target/report metadata found")
    records = []
    summaries = []
    for book in books:
        rows, summary = book_inventory(source, book, prior)
        records.extend(rows)
        summaries.append(summary)
    if not records:
        raise ValueError("No source targets found")
    inventory = b"".join(canonical(row) + b"\n" for row in records)
    manifest = {
        "schema": SCHEMA,
        "base": source.revision,
        "prior": prior.revision if prior else None,
        "pyyaml_version": yaml.__version__,
        "tool_sha256": sha256(Path(__file__).read_bytes()),
        "books": summaries,
        "target_count": len(records),
        "book_count": len(books),
        "inventory_sha256": sha256(inventory),
        "commands": source.commands + (prior.commands if prior else []),
        "evidence": "Metadata only; no compiler, semantic, declaration-resolution or dependency-closure evidence",
    }
    manifest_data = canonical(manifest) + b"\n"
    publish_outputs(args.output, inventory, manifest_data)
    print(
        json.dumps(
            {
                "books": len(books),
                "targets": len(records),
                "report_rows": sum(book["report_row_count"] for book in summaries),
                "inventory_sha256": manifest["inventory_sha256"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (
        ValueError,
        yaml.YAMLError,
        UnicodeError,
        OSError,
        subprocess.CalledProcessError,
    ) as error:
        print(f"inventory: {error}", file=sys.stderr)
        sys.exit(1)
