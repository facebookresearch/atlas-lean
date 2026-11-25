#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Create a frozen tracked-source inventory with Lean's official header parser."""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path, PurePosixPath


READONLY_STATUSES = frozenset({
    "reserved_readonly", "reserved_consumer_readonly", "parent_owned_checkpoint",
    "generated_readonly", "generated_pending_regeneration_policy", "helper_readonly",
})
PENDING_STATUSES = frozenset({"pending", "pending_official_dependency_analysis"})


def validate_manifest_row(row: object) -> None:
    if not isinstance(row, dict):
        raise ValueError("Inventory row must be a JSON object")
    required = ("path", "module", "source_sha256", "analysis_status")
    if any(not isinstance(row.get(key), str) or not row[key] for key in required):
        raise ValueError("Inventory requires path/module/source_sha256/analysis_status strings")
    path = PurePosixPath(row["path"])
    if (path.is_absolute() or ".." in path.parts or str(path) != row["path"] or
            path.suffix != ".lean" or "\\" in row["path"]):
        raise ValueError("Inventory path must be a canonical relative Lean source")
    if row["module"] != str(path.with_suffix("")).replace("/", "."):
        raise ValueError("Inventory module differs from its source path")
    digest = row["source_sha256"]
    if len(digest) != 64 or any(char not in "0123456789abcdef" for char in digest):
        raise ValueError("Inventory source_sha256 must be a lowercase SHA-256 digest")
    if row["analysis_status"] not in READONLY_STATUSES | PENDING_STATUSES:
        raise ValueError("Unknown inventory analysis_status")
    for key in ("topological_index", "bytes"):
        if key in row and (type(row[key]) is not int or row[key] < 0):
            raise ValueError(f"Inventory {key} must be a nonnegative integer")


def header_trivia_end(source: bytes, start: int) -> int:
    """Lean.Parser.whitespace, including nested comments and raw CRLF positions."""
    position = start
    while position < len(source):
        if source[position] in (32, 10):
            position += 1
        elif source.startswith(b"\r\n", position):
            position += 2
        elif source[position] in (9, 13):
            raise ValueError("Native header contains a tab or isolated carriage return")
        elif source.startswith(b"--", position):
            newline = source.find(b"\n", position + 2)
            position = len(source) if newline < 0 else newline
        elif source.startswith(b"/-", position) and not source.startswith((b"/--", b"/-!"), position):
            position += 3
            nesting = 1
            while nesting and position < len(source):
                if source.startswith(b"/-", position):
                    nesting += 1
                    position += 2
                elif source.startswith(b"-/", position):
                    nesting -= 1
                    position += 2
                else:
                    position += 1
            if nesting:
                raise ValueError("Native header contains an unterminated comment")
        else:
            break
    return position


def header_identifier_char(source: bytes, position: int, *, first: bool) -> bool:
    """The identifier character classes in Lean's Init.Meta.Defs."""
    if position >= len(source):
        return False
    byte = source[position]
    width = 1 if byte < 0x80 else 2 if byte < 0xe0 else 3 if byte < 0xf0 else 4
    code = ord(source[position:position + width].decode("utf-8"))
    letter = (65 <= code <= 90 or 97 <= code <= 122 or code == 95 or
              0x3b1 <= code <= 0x3c9 and code != 0x3bb or
              0x391 <= code <= 0x3a9 and code not in (0x3a0, 0x3a3) or
              0x3ca <= code <= 0x3fb or 0x1f00 <= code <= 0x1ffe or
              0x2100 <= code <= 0x214f or 0x1d49c <= code <= 0x1d59f or
              0xc0 <= code <= 0xff and code not in (0xd7, 0xf7) or 0x100 <= code <= 0x17f)
    return letter or not first and (48 <= code <= 57 or code in (39, 33, 63, 0x2c7c) or
                                   0x2080 <= code <= 0x2089 or 0x2090 <= code <= 0x209c or
                                   0x1d62 <= code <= 0x1d6a)


def header_identifier_end(source: bytes, start: int) -> int:
    """Bind the full dotted/escaped token using Lean.Parser.identFnAux's edges."""
    position = start
    while True:
        if source.startswith("«".encode(), position):
            closing = source.find("»".encode(), position + 2)
            if closing < 0:
                raise ValueError("Native header contains an unterminated identifier escape")
            position = closing + 2
        elif header_identifier_char(source, position, first=True):
            while header_identifier_char(source, position, first=position == start):
                byte = source[position]
                position += 1 if byte < 0x80 else 2 if byte < 0xe0 else 3 if byte < 0xf0 else 4
        else:
            raise ValueError("Native header token is not an identifier or keyword")
        if source.startswith(b".", position) and (
                header_identifier_char(source, position + 1, first=True) or
                source.startswith("«".encode(), position + 1)):
            position += 1
        else:
            return position


def verify_header_positions(row: dict, source: bytes) -> None:
    cursor = header_trivia_end(source, 0)
    tokens = []

    def keyword(position: int, spelling: str) -> bool:
        return (source.startswith(spelling.encode(), position) and
                header_identifier_end(source, position) == position + len(spelling))

    def consume(syntax: dict) -> None:
        nonlocal cursor
        items = syntax["tokens"]
        for token in items:
            start, end = token["span"]["start_byte"], token["span"]["end_byte"]
            if start != cursor or header_identifier_end(source, start) != end:
                raise ValueError("Native header token is not at the initial source header cursor")
            leading = {"start_byte": start if tokens else 0, "end_byte": start}
            cursor = header_trivia_end(source, end)
            trailing = {"start_byte": end, "end_byte": cursor}
            if token["leading_span"] != leading or token["trailing_span"] != trailing:
                raise ValueError("Native header token trivia differs from the initial source header")
            tokens.append(token)
        if (not items or syntax["span"] != {"start_byte": items[0]["span"]["start_byte"],
                                           "end_byte": items[-1]["span"]["end_byte"]} or
                syntax.get("leading_span") != items[0]["leading_span"] or
                syntax.get("trailing_span") != items[-1]["trailing_span"]):
            raise ValueError("Native header syntax span differs from its initial source tokens")

    for key, spelling in (("module_token", "module"), ("prelude_token", "prelude")):
        syntax = row[key]
        if keyword(cursor, spelling) != (syntax is not None):
            raise ValueError("Native header mode is absent from the initial source header")
        if syntax is not None:
            consume(syntax)
    for item in row["imports"]:
        consume(item["source"])
    lookahead = cursor
    for spelling in ("public", "meta"):
        if keyword(lookahead, spelling):
            lookahead = header_trivia_end(source, lookahead + len(spelling))
    if keyword(lookahead, "import"):
        raise ValueError("Native header omits an initial source import")
    span = ({"start_byte": tokens[0]["span"]["start_byte"],
             "end_byte": tokens[-1]["span"]["end_byte"]} if tokens else None)
    end = tokens[-1]["span"]["end_byte"] if tokens else cursor
    newline = source.find(b"\n", end)
    shake_insertion = len(source) if newline < 0 else newline + 1
    if (row.get("header_span") != span or row["header_end_byte"] != end or
            row["body_boundary_byte"] != cursor or row["shake_insertion_byte"] != shake_insertion or
            row["insertion_byte"] != (shake_insertion if tokens else cursor)):
        raise ValueError("Native header boundaries differ from the initial source header")


def verify_header(row: dict, source: bytes, counts: Counter) -> None:
    from optimize_imports import decode_header

    decode_header(row, source)
    source.decode("utf-8")

    def position(value: object) -> None:
        if (type(value) is not int or not 0 <= value <= len(source) or
                (value < len(source) and source[value] & 0xc0 == 0x80)):
            raise ValueError("Native header position is not a raw UTF-8 byte boundary")

    def text(span: dict) -> str:
        start, end = span["start_byte"], span["end_byte"]
        position(start)
        position(end)
        if start > end:
            raise ValueError("Reversed native header span")
        return source[start:end].decode("utf-8")

    def walk(value: object) -> None:
        if isinstance(value, dict):
            if set(value) == {"start_byte", "end_byte"}:
                text(value)
                counts["spans"] += 1
            if {"kind", "text", "parsed_text", "span", "leading_span", "trailing_span"} <= value.keys():
                actual = text(value["span"])
                if actual != value["text"] or actual.replace("\r\n", "\n") != value["parsed_text"]:
                    raise ValueError("Native token text differs from the frozen raw source")
                counts["tokens"] += 1
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)

    walk(row)
    if row.get("parse_errors") != []:
        raise ValueError("Native header contains parse errors")
    for key in ("header_end_byte", "insertion_byte", "shake_insertion_byte", "body_boundary_byte"):
        position(row.get(key))
    for flag, key, spelling in (("is_module", "module_token", "module"),
                                ("is_prelude", "prelude_token", "prelude")):
        token = row.get(key)
        if type(row.get(flag)) is not bool or (token is not None) != row[flag]:
            raise ValueError("Native header mode differs from its parser tokens")
        if token is not None and [item["text"] for item in token["tokens"]] != [spelling]:
            raise ValueError("Native module/prelude token is invalid")
    for item in row["imports"]:
        modifiers = item["modifiers"]
        if modifiers != [word for word in ("public", "meta", "all") if word in modifiers]:
            raise ValueError("Native import modifiers are not canonical")
        for flag, modifier in (("is_exported", "public"), ("is_meta", "meta"), ("import_all", "all")):
            if type(item.get(flag)) is not bool or item[flag] != (modifier in modifiers):
                raise ValueError("Native import flags differ from the canonical modifiers")
        tokens = item["source"]["tokens"]
        words = [word for word in modifiers if word != "all"] + ["import"]
        if item["import_all"]:
            words.append("all")
        span = item["source"]["span"]
        if (not tokens or tokens[-1]["kind"] != "ident" or not item["module"] or
                [token["text"] for token in tokens[:-1]] != words or
                span["start_byte"] != tokens[0]["span"]["start_byte"] or
                span["end_byte"] != tokens[-1]["span"]["end_byte"]):
            raise ValueError("Native import differs from its parser tokens")
        if item["module"] != tokens[-1]["parsed_text"]:
            raise ValueError("Native module identity differs from its source identifier")
        counts["imports"] += 1
    verify_header_positions(row, source)


def is_generated_source(source: bytes) -> bool:
    """Recognize the generated marker after an optional first author line."""
    offset = 0
    if source.startswith(b"-- Author: "):
        newline = source.find(b"\n")
        if newline < 0:
            return False
        offset = newline + 1
    return source.startswith(b"-- DO NOT EDIT MANUALLY. This file is autogenerated", offset)


def tracked_sources(root: Path) -> list[str]:
    """Root-package sources only; the older packages have their own toolchains."""
    paths = subprocess.check_output([
        "git", "ls-files", "-z", "--", "*.lean",
        ":(top,exclude)Atlas/**", ":(top,exclude)v1/**", ":(top,exclude)docs/**",
    ], cwd=root)
    names = sorted(path.decode("utf-8") for path in paths.split(b"\0") if path)
    if not names or len(names) != len(set(names)):
        raise ValueError("Git returned empty or duplicated tracked Lean paths")
    return names


def create_inventory(*, root: Path, output: Path, headers: Path | None = None,
                     headers_sha256: str | None = None, lean: Path | None = None,
                     reserve: tuple[str, ...] = (), checkpoints: tuple[str, ...] = (),
                     timeout: int = 120) -> dict:
    from optimize_imports import Tools, cached_headers, native_headers, sha256, source_path, write_json

    root, output = root.resolve(), output.resolve()
    if output.suffix != ".jsonl" or (headers is not None and output == headers.resolve()):
        raise ValueError("Output must be a separate JSONL manifest, not an input or Lean source")
    lean = lean.absolute() if lean else None
    names = tracked_sources(root)
    rows = {}
    for name in names:
        source = source_path(root, name).read_bytes()
        row = {"path": name, "module": name.removesuffix(".lean").replace("/", "."),
               "source_sha256": hashlib.sha256(source).hexdigest(), "bytes": len(source),
               "analysis_status": "pending",
               "generated": is_generated_source(source)}
        validate_manifest_row(row)
        if row["module"] in rows:
            raise ValueError("Tracked sources have duplicate module names")
        rows[row["module"]] = row
    helper = Path(__file__).resolve().parent / "import_optimizer/header.lean"
    optimizer = Path(__file__).resolve().with_name("optimize_imports.py")
    project_pin_paths = [root / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    if (root / "atlas.lock.json").is_file():
        project_pin_paths.append(root / "atlas.lock.json")
    frozen = {path: sha256(path) for path in (Path(__file__).resolve(), optimizer, helper, *project_pin_paths)}
    if lean is not None:
        frozen[lean] = sha256(lean)
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root).decode().strip()
    if headers is not None:
        if headers_sha256 is None or sha256(headers) != headers_sha256:
            raise ValueError("Cached native headers require their frozen --headers-sha256")
        native = cached_headers(root, headers, list(rows.values()))
        header_mode = "cache"
    else:
        if lean is None or timeout <= 0:
            raise ValueError("Fresh native headers require a pinned --lean and positive timeout")
        workspace = Path(str(output) + ".headers")
        workspace.mkdir(parents=True, exist_ok=True)
        tools = Tools(root, workspace, lean.with_name("lake"), lean, helper.parent,
                      dict(os.environ), timeout)
        native = native_headers(tools, list(rows.values()))
        headers = workspace / "native-headers.jsonl"
        header_mode = "native"
    counts = Counter()
    for row in rows.values():
        source = source_path(root, row["path"]).read_bytes()
        header = native[row["path"]]
        if hashlib.sha256(source).hexdigest() != row["source_sha256"] or header.get("source_sha256") != row["source_sha256"]:
            raise ValueError("Source hash changed while obtaining native headers")
        verify_header(header, source, counts)
        row["uses_module_system"], row["is_prelude"] = header["is_module"], header["is_prelude"]
        row["old_imports"] = [{"module": item["module"], "modifiers": item["modifiers"]}
                              for item in header["imports"]]
    edges = {name: {item["module"] for item in row["old_imports"] if item["module"] in rows}
             for name, row in rows.items()}
    reverse = {name: set() for name in rows}
    for name, dependencies in edges.items():
        for dependency in dependencies:
            reverse[dependency].add(name)
    degree = {name: len(dependencies) for name, dependencies in edges.items()}
    ready = [name for name, count in degree.items() if not count]
    heapq.heapify(ready)
    order = []
    while ready:
        name = heapq.heappop(ready)
        order.append(name)
        for consumer in sorted(reverse[name]):
            degree[consumer] -= 1
            if not degree[consumer]:
                heapq.heappush(ready, consumer)
    if len(order) != len(rows):
        raise ValueError("Native local import graph contains a cycle; no manifest written")
    reserved = set()
    for prefix in reserve:
        path = PurePosixPath(prefix)
        if not prefix or path.is_absolute() or ".." in path.parts:
            raise ValueError("Reservation must be a relative file or directory prefix")
        matched = {name for name, row in rows.items() if row["path"] == prefix or
                   (not prefix.endswith(".lean") and row["path"].startswith(prefix.rstrip("/") + "/"))}
        if not matched:
            raise ValueError(f"Reservation prefix matched no tracked source: {prefix}")
        reserved.update(matched)
    if not set(checkpoints) <= set(names):
        raise ValueError("Checkpoint is absent from the tracked sources")
    consumers, pending = set(), list(reserved)
    while pending:
        for consumer in reverse[pending.pop()]:
            if consumer not in reserved and consumer not in consumers:
                consumers.add(consumer)
                pending.append(consumer)
    closure = {}
    for index, name in enumerate(order):
        row = rows[name]
        bits = 0
        for dependency in edges[name]:
            bits |= closure[dependency] | (1 << rows[dependency]["topological_index"])
        closure[name] = bits
        row.update({"topological_index": index, "direct_local_dependencies": sorted(edges[name]),
                    "direct_local_consumers": sorted(reverse[name]),
                    "engine": "official Lake shake" if row["uses_module_system"] else "official ImportGraph legacy fallback",
                    "old_dependency_cost": {"kind": "static_local_source_import_closure_only",
                        "direct_header_import_count": len(row["old_imports"]),
                        "local_source_dependency_count": bits.bit_count(),
                        "external_closure_status": "not_run", "runtime_cost_status": "unmeasured"},
                    "proposed_imports": None, "new_dependency_cost": None})
        if name in reserved:
            row["analysis_status"] = "reserved_readonly"
        elif name in consumers:
            row["analysis_status"] = "reserved_consumer_readonly"
        elif row["path"] in checkpoints:
            row["analysis_status"] = "parent_owned_checkpoint"
        elif row["generated"]:
            row["analysis_status"] = "generated_readonly"
        elif row["path"].startswith("scripts/"):
            row["analysis_status"] = "helper_readonly"
        row["pending_reason"] = ("Read-only scope: " + row["analysis_status"] if row["analysis_status"] in READONLY_STATUSES
                                 else "Compiled dependency analysis, candidate/API/consumer checks and timing have not run.")
        for gate in ("baseline_compile", "candidate_compile", "declaration_comparison", "axiom_comparison",
                     "consumer_validation", "measurement"):
            row[gate] = {"status": "not_run"}
        validate_manifest_row(row)
    if (tracked_sources(root) != names or
            subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root).decode().strip() != head or
            any(sha256(path) != digest for path, digest in frozen.items()) or
            any(sha256(source_path(root, row["path"])) != row["source_sha256"] for row in rows.values())):
        raise ValueError("Tracked sources, project pins, or implementation changed during inventory")
    if header_mode == "cache" and sha256(headers) != headers_sha256:
        raise ValueError("Native header cache changed during inventory")
    headers_digest = sha256(headers)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(json.dumps(rows[name], ensure_ascii=False, separators=(",", ":")) + "\n"
                              for name in order), encoding="utf-8")
    receipt = {"schema_version": 1, "git_head": head, "source_count": len(rows),
               "source_bytes": sum(row["bytes"] for row in rows.values()),
               "source_hashes_sha256": hashlib.sha256(json.dumps({row["path"]: row["source_sha256"]
                   for row in rows.values()}, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
               "producer_sha256": frozen[Path(__file__).resolve()], "optimizer_sha256": frozen[optimizer],
               "header_helper_sha256": frozen[helper], "headers": str(headers), "headers_sha256": headers_digest,
               "header_mode": header_mode, "native_counts": dict(counts),
               "project_pins": {path.name: frozen[path] for path in project_pin_paths},
               "declared_toolchain": (root / "lean-toolchain").read_text().strip(),
               "compiler_sha256": frozen[lean] if lean else None,
               "reserve": sorted(reserve), "checkpoints": sorted(checkpoints),
               "reserved_count": len(reserved), "reserved_consumer_count": len(consumers),
               "generated_count": sum(row["generated"] for row in rows.values()),
               "topological_nodes": len(order), "local_edge_count": sum(map(len, edges.values())),
               "status_counts": dict(Counter(row["analysis_status"] for row in rows.values())),
               "engine_counts": dict(Counter(row["engine"] for row in rows.values())),
               "manifest": str(output), "manifest_sha256": sha256(output),
               "project_modules_compiled": 0, "consumer_validation": "not_run", "global_optimality": "not_claimed"}
    write_json(Path(str(output) + ".meta.json"), receipt)
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True, help="Manifest JSONL file")
    parser.add_argument("--headers", type=Path, help="Stamped native header cache; omit to run the official helper")
    parser.add_argument("--headers-sha256", help="Previously recorded digest of the native cache")
    parser.add_argument("--lean", type=Path, help="Pinned Lean executable, required for fresh headers")
    parser.add_argument("--reserve", action="append", default=[], help="Read-only source file or directory prefix")
    parser.add_argument("--checkpoint", action="append", default=[], help="Read-only tracked source checkpoint")
    parser.add_argument("--timeout", type=int, default=120, help="Seconds per native header helper batch")
    options = parser.parse_args()
    receipt = create_inventory(root=options.root, output=options.output, headers=options.headers,
        headers_sha256=options.headers_sha256, lean=options.lean, reserve=tuple(options.reserve),
        checkpoints=tuple(options.checkpoint), timeout=options.timeout)
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"Inventory failed: {error}", file=sys.stderr)
        raise SystemExit(2) from error
