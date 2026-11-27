#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Optimize Lean import headers using the project's pinned dependency tools."""

from __future__ import annotations

import argparse
import ctypes
import difflib
import errno
import fcntl
import hashlib
import json
import os
import re
import select
import shutil
import signal
import stat
import struct
import subprocess
import sys
import time
from collections import Counter
from collections.abc import Callable, Iterable, Iterator
from contextlib import contextmanager
from contextvars import ContextVar
from copy import deepcopy
from dataclasses import dataclass, field
from pathlib import Path
from typing import cast

from generate_import_inventory import (
    READONLY_STATUSES, is_generated_source, tracked_sources, validate_manifest_row, verify_header,
)


ARTIFACT_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".ilean", ".c")
LEGACY_ARTIFACT_SUFFIXES = (".olean", ".ilean", ".c")
DEFAULT_LEAN_THREADS = 2
DEFAULT_LAKE_JOBS = 1
MAX_THREAD_COUNT = 1024


def validate_thread_count(name: str, value: object) -> int:
    """Accept only a plain integer in 1..MAX_THREAD_COUNT; bool is not a count."""
    if type(value) is not int or not 1 <= value <= MAX_THREAD_COUNT:
        raise ValueError(f"{name} must be an integer from 1 to {MAX_THREAD_COUNT}")
    return value


def thread_count_argument(text: str) -> int:
    if re.fullmatch(r"[1-9][0-9]{0,3}", text) is None:
        raise argparse.ArgumentTypeError(f"expected an integer from 1 to {MAX_THREAD_COUNT}")
    try:
        return validate_thread_count("thread count", int(text))
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from None


@dataclass(frozen=True)
class ImportSpec:
    module: str
    modifiers: tuple[str, ...] = ()

    def render(self) -> str:
        words = [word for word in self.modifiers if word != "all"]
        words.append("import")
        if "all" in self.modifiers:
            words.append("all")
        return " ".join([*words, self.module])

    @staticmethod
    def parse(text: str) -> ImportSpec:
        match = re.fullmatch(
            r"(?:(public)\s+)?(?:(meta)\s+)?import\s+(?:(all)\s+)?(.+)",
            text.strip(),
        )
        if match is None:
            raise ValueError(f"Invalid import rendering: {text!r}")
        public, meta, all_, module = match.groups()
        if not module or "\n" in module:
            raise ValueError("Missing or multiline module identifier")
        return ImportSpec(module, tuple(x for x in (public, meta, all_) if x))


@dataclass(frozen=True)
class ImportSpan:
    spec: ImportSpec
    start: int
    end: int


@dataclass(frozen=True)
class Header:
    is_module: bool
    imports: tuple[ImportSpan, ...]
    insertion: int
    body_boundary: int

    def specs(self) -> tuple[ImportSpec, ...]:
        return tuple(span.spec for span in self.imports)


@dataclass(frozen=True)
class Proposal:
    remove: tuple[ImportSpec, ...] = ()
    add: tuple[ImportSpec, ...] = ()
    evidence: dict[str, object] | None = field(default=None, compare=False, repr=False)


class ShakeAnalysisError(ValueError):
    def __init__(self, error: str, evidence: dict[str, object]) -> None:
        super().__init__(error)
        self.evidence = evidence


def decode_header(row: dict[str, object], source: bytes) -> Header:
    if row.get("status") != "parsed":
        raise ValueError("Lean did not parse the import header")
    if row.get("source_utf8_bytes") != len(source):
        raise ValueError("Header byte count differs from the original source")
    is_module = row.get("is_module")
    insertion, boundary = row.get("insertion_byte"), row.get("body_boundary_byte")
    records = row.get("imports")
    if not isinstance(is_module, bool) or not isinstance(records, list):
        raise ValueError("Invalid native header record")
    if not isinstance(insertion, int) or not isinstance(boundary, int):
        raise ValueError("Invalid header byte boundary")
    if not 0 <= insertion <= boundary <= len(source):
        raise ValueError("Invalid header byte boundary")
    imports: list[ImportSpan] = []
    previous = 0
    for record in records:
        if not isinstance(record, dict) or not isinstance(record.get("source"), dict):
            raise ValueError("Invalid native import record")
        module, modifiers = record.get("module"), record.get("modifiers")
        span = record["source"].get("span")
        if not isinstance(module, str) or not isinstance(modifiers, list):
            raise ValueError("Invalid native import identity")
        if any(word not in ("public", "meta", "all") for word in modifiers):
            raise ValueError("Invalid native import modifiers")
        if not isinstance(span, dict):
            raise ValueError("Missing native import byte span")
        start, end = span.get("start_byte"), span.get("end_byte")
        if not isinstance(start, int) or not isinstance(end, int):
            raise ValueError("Invalid native import byte span")
        if not previous <= start < end <= boundary:
            raise ValueError("Overlapping or out-of-header native import span")
        imports.append(ImportSpan(ImportSpec(module, tuple(modifiers)), start, end))
        previous = end
    return Header(is_module, tuple(imports), insertion, boundary)


def parse_import_array(text: str) -> list[ImportSpec]:
    text = text.strip()
    if not (text.startswith("#[") and text.endswith("]")):
        raise ValueError(f"Invalid shake array: {text!r}")
    contents = text[2:-1]
    if not contents.strip():
        return []
    fields: list[str] = []
    start = 0
    escaped = False
    for index, char in enumerate(contents):
        if char == "«":
            if escaped:
                raise ValueError("Nested escaped module identifier")
            escaped = True
        elif char == "»":
            if not escaped:
                raise ValueError("Unmatched escaped module identifier")
            escaped = False
        elif char == "," and not escaped:
            fields.append(contents[start:index])
            start = index + 1
    if escaped:
        raise ValueError("Unclosed escaped module identifier")
    fields.append(contents[start:])
    return [ImportSpec.parse(field) for field in fields]


def parse_shake_output(output: str, exit_code: int, target: Path,
                       cwd: Path | None = None) -> Proposal:
    if exit_code not in (0, 1):
        raise ValueError(f"Shake failed with exit {exit_code}")
    if re.search(r"(?:^\s*|:\d+:\d+:\s*)(?:error:|PANIC|panic:|uncaught exception:)|parse errors in file",
                 output, re.MULTILINE):
        raise ValueError("Shake reported an error")
    base = cwd if cwd is not None else Path.cwd()
    found = False
    selected = False
    removed: list[ImportSpec] = []
    added: list[ImportSpec] = []
    for line in output.splitlines():
        if not line.startswith(" ") and line.endswith(".lean:"):
            path = Path(line[:-1])
            selected = (path if path.is_absolute() else base / path).resolve() == target.resolve()
            found = found or selected
        elif selected and line.startswith("  remove "):
            removed.extend(parse_import_array(line.removeprefix("  remove ")))
        elif selected and line.startswith("  add "):
            added.extend(parse_import_array(line.removeprefix("  add ")))
    if not found:
        raise ValueError("Shake did not report the selected module")
    return Proposal(tuple(removed), tuple(added))


def source_path(root: Path, relative: str) -> Path:
    requested = Path(relative)
    if requested.is_absolute() or ".." in requested.parts or requested.suffix != ".lean":
        raise ValueError(f"Not a relative Lean source path: {relative!r}")
    result = (root / requested).resolve(strict=True)
    if not result.is_relative_to(root.resolve()):
        raise ValueError(f"Source escapes the project: {relative!r}")
    return result


def rewrite_imports(source: bytes, header: Header, remove: tuple[ImportSpec, ...],
                    add: tuple[ImportSpec, ...]) -> bytes:
    unknown = set(remove) - set(header.specs())
    if unknown:
        raise ValueError(f"Requested removal is absent from the header: {unknown}")
    additions = tuple(dict.fromkeys(spec for spec in add if spec not in header.specs()
                                   or spec in remove))
    edits: list[tuple[int, int, bytes]] = []
    for span in header.imports:
        if not (0 <= span.start < span.end <= header.body_boundary <= len(source)):
            raise ValueError("Invalid source byte span")
        if span.spec not in remove:
            continue
        directive = source[span.start:span.end]
        if b"--" in directive or b"/-" in directive:
            raise ValueError("Import contains an interstitial comment; retain it for manual editing")
        if ImportSpec.parse(directive.decode("utf-8")) != span.spec:
            raise ValueError("Source bytes do not match the parsed import")
        start, end = span.start, span.end
        line_start = source.rfind(b"\n", 0, start) + 1
        next_newline = source.find(b"\n", end)
        line_end = len(source) if next_newline < 0 else next_newline + 1
        if not source[line_start:start].strip() and not source[end:line_end].strip():
            start, end = line_start, line_end
        edits.append((start, end, b""))
    if additions:
        if not header.imports:
            raise ValueError("Adding to an empty import header requires a reviewed insertion point")
        insertion = header.imports[0].start
        line_start = source.rfind(b"\n", 0, insertion) + 1
        if not source[line_start:insertion].strip():
            insertion = line_start
        for start, end, _ in edits:
            if start <= insertion < end:
                insertion = start
        first_newline = source.find(b"\n", header.imports[0].end)
        newline = "\r\n" if first_newline > 0 and source[first_newline - 1] == 13 else "\n"
        block = "".join(spec.render() + newline for spec in additions).encode()
        edits.append((insertion, insertion, block))
    edits.sort(key=lambda edit: (edit[0], edit[1]))
    out = bytearray()
    previous = 0
    for start, end, replacement in edits:
        if start < previous or not (0 <= start <= end <= header.body_boundary):
            raise ValueError("Overlapping or out-of-header edits")
        out.extend(source[previous:start])
        out.extend(replacement)
        previous = end
    out.extend(source[previous:])
    result = bytes(out)
    if not result.endswith(source[header.body_boundary:]):
        raise ValueError("Import edit changed declaration bytes")
    return result


def compare_snapshots(before: dict[str, object], after: dict[str, object]) -> list[str]:
    if before.get("module") != after.get("module"):
        return ["Snapshot module identity changed"]
    def declarations(snapshot: dict[str, object]) -> dict[str, dict[str, object]]:
        records = snapshot.get("declarations")
        if not isinstance(records, list):
            raise ValueError("Snapshot has no declaration list")
        result: dict[str, dict[str, object]] = {}
        for record in records:
            if not isinstance(record, dict) or not isinstance(record.get("name"), str):
                raise ValueError("Invalid declaration snapshot")
            normalized = dict(record)
            normalized["axioms"] = sorted(record.get("axioms", []))
            if record["name"] in result:
                raise ValueError("Duplicate declaration in snapshot")
            result[record["name"]] = normalized
        return result
    old, new = declarations(before), declarations(after)
    return [f"Declaration changed: {name}" for name in sorted(old.keys() | new.keys())
            if old.get(name) != new.get(name)]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"Expected a JSON object in {path}")
    return value


def write_json(path: Path, value: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n",
                         encoding="utf-8")
    temporary.replace(path)


def _owned_child_exited_without_reaping(pid: int, observation_timeout: float = 1.0) -> bool:
    """Observe only the caller's unreaped child, retaining its process-group identity."""
    waitid = getattr(os, "waitid", None)
    names = ("P_PID", "WEXITED", "WNOHANG", "WNOWAIT")
    if callable(waitid) and all(hasattr(os, name) for name in names):
        try:
            state = waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
        except (AttributeError, NotImplementedError):
            pass
        except OSError as exc:
            if isinstance(exc, PermissionError) or exc.errno not in {errno.ENOSYS, errno.EINVAL}:
                raise
        else:
            if state is None or state.si_pid == 0:
                return False
            if state.si_pid != pid:
                raise RuntimeError("Exit observation returned a different owned child")
            return True
    result = subprocess.run(["ps", "-p", str(pid), "-o", "stat="], capture_output=True,
                            text=True, timeout=observation_timeout, check=False)
    states = result.stdout.split()
    if not states and result.returncode in (0, 1) and not result.stderr.strip():
        return True
    if result.returncode != 0 or len(states) != 1:
        raise RuntimeError(f"Cannot observe owned child status: {result.stderr.strip()}")
    return states[0][0] in {"Z", "X"}


def _owned_group_only_has_zombies(pid: int) -> bool:
    """Confirm the unreaped leader and every group member have exited."""
    result = subprocess.run(["ps", "-A", "-o", "pid=,pgid=,stat="], capture_output=True,
                            text=True, timeout=1.0, check=False)
    if result.returncode != 0 or result.stderr.strip():
        return False
    leader_present = False
    for line in result.stdout.splitlines():
        fields = line.split()
        if len(fields) != 3 or not fields[0].isdigit() or not fields[1].isdigit():
            return False
        member, group = int(fields[0]), int(fields[1])
        if group != pid:
            continue
        if fields[2][0] not in {"Z", "X"}:
            return False
        leader_present |= member == pid
    return leader_present


def run_command(argv: list[str], cwd: Path, label: Path,
                environment: dict[str, str], timeout: int) -> dict[str, object]:
    """Save the real child status and both output streams, including failures."""
    label.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    timed_out = False
    remaining_group_killed = False
    with Path(str(label) + ".stdout").open("wb") as stdout, \
            Path(str(label) + ".stderr").open("wb") as stderr:
        child = subprocess.Popen(argv, cwd=cwd, env=environment, stdout=stdout,
                                 stderr=stderr, start_new_session=True)
        process_group = child.pid
        group_signals_attempted: set[int] = set()

        def signal_owned_group(sig: int) -> bool:
            if sig in group_signals_attempted:
                return False
            if process_group <= 0 or process_group == os.getpgrp():
                raise RuntimeError("Refusing to signal an invalid or parent process group")
            if child.returncode is not None:
                try:
                    os.getpgid(process_group)
                except ProcessLookupError:
                    pass
                else:
                    raise RuntimeError("Refusing cleanup after the owned leader PID was reused")
            group_signals_attempted.add(sig)
            try:
                os.killpg(process_group, sig)
            except ProcessLookupError:
                return False
            except PermissionError:
                # Darwin excludes zombies from killpg's signalable members and
                # returns EPERM for a group containing only zombies. Retaining
                # the leader prevents PID reuse while checking the whole group.
                if (sys.platform == "darwin" and sig == signal.SIGKILL and
                        child.returncode is None and _owned_group_only_has_zombies(process_group)):
                    return False
                raise
            return True

        try:
            code = child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            # Retain the old TERM grace while keeping the leader unreaped until
            # KILL has also reached any TERM-ignoring descendants in its group.
            try:
                signal_owned_group(signal.SIGTERM)
                grace_deadline = time.monotonic() + 10
                while (remaining := grace_deadline - time.monotonic()) > 0:
                    try:
                        if _owned_child_exited_without_reaping(process_group, min(1.0, remaining)):
                            break
                    except subprocess.TimeoutExpired:
                        if time.monotonic() < grace_deadline:
                            raise
                        break
                    remaining = grace_deadline - time.monotonic()
                    if remaining <= 0:
                        break
                    time.sleep(min(0.1, remaining))
            finally:
                remaining_group_killed = signal_owned_group(signal.SIGKILL)
                child.wait()
            code = 124
        except (KeyboardInterrupt, SystemExit):
            remaining_group_killed = signal_owned_group(signal.SIGKILL)
            child.wait()
            raise
        finally:
            if signal.SIGKILL not in group_signals_attempted:
                remaining_group_killed = signal_owned_group(signal.SIGKILL)
            if remaining_group_killed:
                time.sleep(0.02)
    result: dict[str, object] = {
        "argv": argv, "cwd": str(cwd), "exit_code": code, "timed_out": timed_out,
        "elapsed_seconds": time.monotonic() - started,
        "remaining_group_killed": remaining_group_killed,
        "stdout": str(label) + ".stdout", "stderr": str(label) + ".stderr",
    }
    write_json(Path(str(label) + ".json"), result)
    return result


def require_completion(result: dict[str, object]) -> None:
    if (type(result.get("exit_code")) is not int or result.get("timed_out") is not False or
            result.get("remaining_group_killed") is not False or result.get("remaining_group_members")):
        raise ValueError(f"Command completion is not clean; see {result.get('stderr')}")


def require_success(result: dict[str, object]) -> None:
    require_completion(result)
    if result["exit_code"] != 0:
        raise ValueError(f"Command exited {result['exit_code']}; see {result['stderr']}")


def recover_source_edit(root: Path, transaction: Path) -> None:
    if not transaction.exists():
        return
    record = read_json(transaction)
    source = source_path(root, str(record["path"]))
    backup = Path(str(record["backup"]))
    if sha256(backup) != record["source_sha256"]:
        raise ValueError("Source recovery backup changed")
    current = sha256(source)
    if current == record["candidate_sha256"]:
        raise ValueError(f"Legacy candidate remains at {source}; manually restore {backup} "
                         f"before resuming; retained recovery file {transaction}")
    elif current != record["source_sha256"]:
        raise ValueError(f"Source changed outside this run; retained recovery file {transaction}")
    transaction.unlink()


def read_journal(path: Path, sources: dict[str, object]) -> dict[str, dict[str, object]]:
    if not path.exists():
        return {}
    data = path.read_bytes()
    records = data.splitlines(keepends=True)
    completed: dict[str, dict[str, object]] = {}
    offset = 0
    for index, line in enumerate(records):
        try:
            record = json.loads(line)
        except (json.JSONDecodeError, UnicodeDecodeError) as error:
            if index != len(records) - 1 or line.endswith(b"\n"):
                raise ValueError("Result journal contains a corrupt complete record") from error
            torn = path.with_name(f"{path.name}.torn-{time.time_ns()}")
            torn.write_bytes(line)
            path.write_bytes(data[:offset])
            break
        if not isinstance(record, dict) or record.get("path") not in sources:
            raise ValueError("Result journal contains a file outside this run")
        if record.get("source_sha256") != sources[record["path"]]:
            raise ValueError("Result journal source hash differs from the frozen input")
        if record.get("status") not in ("verified", "no_change", "blocked", "readonly"):
            raise ValueError("Result journal contains an incomplete status")
        completed[record["path"]] = record
        offset += len(line)
    if data and records and not records[-1].endswith(b"\n") and offset == len(data):
        with path.open("ab") as journal:
            journal.write(b"\n")
    return completed


@dataclass(frozen=True)
class ValidatedSnapshotGroup:
    evidence: dict[str, object]
    members: dict[str, dict[str, object]]
    snapshots: dict[str, dict[str, object]]


def resolve_inventory_path(path: Path) -> Path:
    return path.resolve()


_guarded_inventory_canonical_paths: ContextVar[frozenset[Path]] = ContextVar(
    "guarded_inventory_canonical_paths", default=frozenset())


# Filesystem facts read by a recorded whole-batch input derivation (see
# `PreparedInputs`); `None` while nothing is being recorded.
_recorded_input_facts: ContextVar[dict[tuple[str, str], object] | None] = ContextVar(
    "recorded_input_facts", default=None)


def read_input_fact(kind: str, path: Path) -> object:
    if kind == "exists":
        return path.exists()
    if kind == "is_file":
        return path.is_file()
    if kind == "is_dir":
        return path.is_dir()
    if kind == "inventory_resolve" and sys.platform == "linux" and \
            path in _guarded_inventory_canonical_paths.get():
        # An active Linux inventory guard proved every component of this
        # path canonical (no symlink, no `..`) and watches it for moves.
        return str(path)
    if kind in ("resolve", "inventory_resolve"):
        try:
            return str(path.resolve() if kind == "resolve" else resolve_inventory_path(path))
        except OSError as error:
            return ("OSError", error.errno)
    if kind == "children":
        try:
            return ("entries", tuple(sorted(os.listdir(path))))
        except OSError as error:
            return ("OSError", error.errno)
    raise ValueError(f"Unknown compilation input fact: {kind}")


def input_fact(kind: str, path: Path) -> object:
    value = read_input_fact(kind, path)
    facts = _recorded_input_facts.get()
    if facts is not None and facts.setdefault((kind, str(path)), value) != value:
        raise ValueError(f"Compilation input changed while its inputs were derived: {path}")
    return value


def fact_exists(path: Path) -> bool:
    return cast(bool, input_fact("exists", path))


def fact_is_file(path: Path) -> bool:
    return cast(bool, input_fact("is_file", path))


def fact_is_dir(path: Path) -> bool:
    return cast(bool, input_fact("is_dir", path))


def _resolved_fact(path: Path, value: object) -> Path:
    if isinstance(value, tuple):
        raise OSError(value[1], "Could not resolve compilation input path", str(path))
    return Path(cast(str, value))


def fact_resolve(path: Path) -> Path:
    return _resolved_fact(path, input_fact("resolve", path))


def fact_inventory_resolve(path: Path) -> Path:
    return _resolved_fact(path, input_fact("inventory_resolve", path))


def fact_children(path: Path) -> list[Path]:
    """Sorted directory entries, as `sorted(path.iterdir())` returns them."""
    kind, value = cast(tuple[str, object], input_fact("children", path))
    if kind != "entries":
        raise OSError(value, "Could not list compilation input directory", str(path))
    return [path / name for name in cast(tuple[str, ...], value)]


def inventory_path_outside_output(path: Path, output_parts: tuple[str, ...]) -> bool:
    # Inside a Linux inventory guard the fact read returns the guarded
    # canonical path itself; a recorded fact is re-read, with or without
    # a guard, before its derivation is reused.
    return fact_inventory_resolve(path).parts[:len(output_parts)] != output_parts


@dataclass(frozen=True)
class Tools:
    root: Path
    output: Path
    lake: Path
    lean: Path
    helpers: Path
    environment: dict[str, str]
    timeout: int
    time_binary: Path = Path("/usr/bin/time")
    lake_config: Path | None = None
    # Threads per Lean compiler or helper process (`lean -jN`).
    lean_threads: int = DEFAULT_LEAN_THREADS
    # Lake's build scheduler threads, passed to every child as
    # LEAN_NUM_THREADS. The Lean frontend does not read that variable.
    lake_jobs: int = DEFAULT_LAKE_JOBS
    file_cache: SourceCache = field(default_factory=dict, compare=False, repr=False)
    input_manifests: dict[tuple[str, ...], tuple[dict[str, object], list[dict[str, object]]]] = field(
        default_factory=dict, compare=False, repr=False)
    library_inventories: dict[Path, tuple[tuple[str, ...], dict[Path, SourceIdentity]]] = field(
        default_factory=dict, compare=False, repr=False)
    validated_analysis_inputs: dict[str, list[tuple[dict[str, object], list[dict[str, object]]]]] = field(
        default_factory=dict, compare=False, repr=False)
    validated_snapshot_groups: dict[str, dict[str, list[ValidatedSnapshotGroup]]] = field(
        default_factory=dict, compare=False, repr=False)
    prepared_inputs: dict[str, PreparedInputs] = field(default_factory=dict, compare=False, repr=False)
    # Root-package artifacts pinned by this process: the receipt and the full
    # file identity at their first pin. Written once, so a later re-hash of a
    # changed file cannot replace the expectation (see `record_root_custody`).
    root_custody: dict[str, tuple[dict[str, object], SourceIdentity]] = field(
        default_factory=dict, compare=False, repr=False)
    # The first rejected Lake preparation; every later preparation is refused.
    lake_custody_failure: list[str] = field(default_factory=list, compare=False, repr=False)
    # The root artifact root's top-level listing after the last accepted preparation.
    root_listing: dict[str, tuple[frozenset[Path], frozenset[Path]]] = field(
        default_factory=dict, compare=False, repr=False)
    # Lake-manifest bytes pinned before Lake's environment is
    # captured (production `main` passes them in explicitly; other
    # callers pin at first derivation in `__post_init__`).
    # Manifest-derived canonical roots are parsed only from these
    # bytes, never reread live, so a later manifest rewrite cannot
    # reclassify an ambient `LEAN_PATH` entry as a trusted package
    # root. A `None` value pins a missing/unreadable manifest.
    lake_manifest_bytes: dict[Path, bytes | None] = field(
        default_factory=dict, compare=False, repr=False)

    def __post_init__(self) -> None:
        validate_thread_count("lean_threads", self.lean_threads)
        validate_thread_count("lake_jobs", self.lake_jobs)
        object.__setattr__(self, "root", fact_resolve(self.root))
        roots = canonical_artifact_roots(self)
        library = standard_library_root(self)
        if library is not None:
            roots.append(library)
        # Saved-fixture/verification callers construct Tools(root,
        # root) and use explicit file pins only; the canonical root
        # is necessarily beneath that output. Construction keeps the
        # historically enforced output-under-root rejection and
        # defers the inverse-overlap rejection to compile/fallback/
        # discovery trust call sites.
        reject_output_nested_in_roots(self, roots, _during_post_init=True)

    @property
    def lean_thread_argument(self) -> str:
        return f"-j{self.lean_threads}"

    def lake_command(self, *arguments: str) -> list[str]:
        config = ["-f", str(self.lake_config)] if self.lake_config is not None else []
        return [str(self.lake), "--no-cache", *config, *arguments]

    def run(self, argv: list[str], label: Path,
            environment: dict[str, str] | None = None) -> dict[str, object]:
        prepared = self.prepared_inputs.get("phase")
        if prepared is not None:
            prepared.new_window()
        revalidate_analysis_inputs(self)
        child_environment = {**(self.environment if environment is None else environment),
                             "LEAN_NUM_THREADS": str(self.lake_jobs)}
        try:
            return run_command(argv, self.root, label, child_environment, self.timeout)
        finally:
            cached = self.validated_analysis_inputs.get("phase")
            if cached is not None:
                cached.clear()
            groups = self.validated_snapshot_groups.get("phase")
            if groups is not None:
                groups.clear()
            if prepared is not None:
                prepared.new_window()


class PreparedInputs:
    """Phase-scoped reuse of whole-batch compilation input derivations.

    Rechecking a shared Shake bundle rebuilds every member's compilation
    input paths: optional-artifact probes, strict root selection, canonical
    path resolution and namespace inventories over each dependency closure.
    That cost scales with the whole batch and was paid before every native
    command.

    A derivation is stored with every filesystem fact it read
    (`input_fact`, plus each namespace or library inventory as one fact
    checked through its directory identities). It is reused only when each
    of those facts, read again, still has its recorded value: the
    derivation is deterministic in its key (setup metadata and the `Tools`
    configuration) and those facts, so it would follow the same path and
    return the same paths. Anything else derives again from scratch.

    A fact read is shared only within one window. A window ends at every
    native boundary, before the boundary's revalidation and after its
    child, and before a phase's closing revalidation: the same points that
    already drop the phase's validated bundles. File pins and inventory
    directory identities from input manifests are deduplicated the same
    way. Only saved-evidence validation in an open phase uses this object:
    Shake bundle checks, boundary revalidation and saved candidates.
    """

    def __init__(self, tools: Tools) -> None:
        self.tools = tools
        self.derivations: dict[tuple[object, ...],
                               tuple[tuple[str, ...], dict[tuple[str, str], object]]] = {}
        self.window: dict[tuple[str, str], object] = {}

    def new_window(self) -> None:
        self.window.clear()

    def fact(self, kind: str, path: str) -> object:
        key = (kind, path)
        if key not in self.window:
            self.window[key] = self.read(kind, Path(path))
        return self.window[key]

    def read(self, kind: str, path: Path) -> object:
        unreadable = object()
        try:
            if kind == "inventory":
                cached = self.tools.library_inventories.get(path)
                if cached is None:
                    return unreadable
                self.verify_directories(cached[1])
                return cached[0]
            if kind == "volatile":
                return unreadable
            return read_input_fact(kind, path)
        except (OSError, RuntimeError, ValueError):
            return unreadable

    def derive(self, key: tuple[object, ...],
               derivation: Callable[[], tuple[str, ...]]) -> tuple[str, ...]:
        stored = self.derivations.pop(key, None)
        if stored is not None and all(self.fact(kind, path) == value
                                      for (kind, path), value in stored[1].items()):
            self.derivations[key] = stored
            return stored[0]
        facts: dict[tuple[str, str], object] = {}
        token = _recorded_input_facts.set(facts)
        try:
            result = derivation()
        finally:
            _recorded_input_facts.reset(token)
        self.derivations[key] = (result, facts)
        return result

    def verify_pin(self, receipt: object) -> None:
        key = ("pin", str(receipt.get("path"))) if isinstance(receipt, dict) else None
        if key is not None and self.window.get(key) == receipt:
            return
        verify_file_pin(receipt, cache=self.tools.file_cache)
        self.window[cast(tuple[str, str], key)] = dict(cast(dict[str, object], receipt))

    def verify_directories(self, directories: dict[Path, SourceIdentity]) -> None:
        for path, identity in directories.items():
            key = ("identity", str(path))
            if self.window.get(key) != identity:
                if source_identity(path) != identity:
                    raise ValueError(f"Compiler standard-library inventory changed: {path}")
                self.window[key] = identity


_active_prepared_inputs: ContextVar[PreparedInputs | None] = ContextVar(
    "active_prepared_inputs", default=None)


@contextmanager
def using_prepared_inputs(tools: Tools) -> Iterator[None]:
    token = _active_prepared_inputs.set(tools.prepared_inputs.get("phase"))
    try:
        yield
    finally:
        _active_prepared_inputs.reset(token)


def new_prepared_window(tools: Tools) -> None:
    """Re-read every fact before the next reuse, as at a native boundary."""
    prepared = tools.prepared_inputs.get("phase")
    if prepared is not None:
        prepared.new_window()


def active_prepared_inputs(tools: Tools | None) -> PreparedInputs | None:
    prepared = _active_prepared_inputs.get()
    return prepared if prepared is not None and tools is prepared.tools else None


def bounded_lake_config(root: Path, lean_threads: int = DEFAULT_LEAN_THREADS) -> Path:
    validate_thread_count("lean_threads", lean_threads)
    original = (root / "lakefile.toml").read_bytes()
    if re.search(rb"(?m)^\s*moreLeanArgs\s*=", original):
        raise ValueError("Existing moreLeanArgs require an explicit bounded configuration")
    first, separator, rest = original.partition(b"\n")
    if not separator or first.lstrip().startswith(b"["):
        raise ValueError("Lake configuration needs a root section before compiler arguments")
    content = first + separator + f'moreLeanArgs = ["-j{lean_threads}"]\n'.encode() + rest
    # One file per thread count, so a run never rewrites the configuration
    # another thread setting's saved Lake commands name.
    path = root / f".lake/lakefile-lean-j{lean_threads}.toml"
    if not path.exists() or path.read_bytes() != content:
        path.write_bytes(content)
    return path


def artifact_receipt(directory: Path, relative: Path, *, require_c: bool = False,
                     is_module: bool = True, cache: SourceCache | None = None) -> list[dict[str, object]]:
    prefix = directory / relative.with_suffix("")
    artifacts = []
    if require_c and type(is_module) is not bool:
        raise ValueError("Forced artifacts require a boolean module mode")
    suffixes = ARTIFACT_SUFFIXES if not require_c or is_module else LEGACY_ARTIFACT_SUFFIXES
    for suffix in suffixes:
        path = Path(str(prefix) + suffix)
        if require_c and (not path.is_file() or path.is_symlink() or not path.stat().st_size):
            raise ValueError(f"Compile did not produce a nonempty target {suffix}")
        if path.is_file():
            artifacts.append(file_pin(path, cache) if cache is not None else
                             {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256(path)})
    if not any(record["path"] == str(prefix) + ".olean" and record["bytes"]
               for record in artifacts):
        raise ValueError("Compile did not produce a nonempty target .olean")
    return artifacts


def file_pin(path: Path, cache: SourceCache | None = None) -> dict[str, object]:
    if not path.is_absolute():
        raise ValueError(f"Missing absolute evidence file: {path}")
    before = source_identity(path)
    if not stat.S_ISREG(before[5]):
        raise ValueError(f"Evidence path is not a regular file: {path}")
    cached = cache.get(str(path)) if cache is not None else None
    if cached is not None and cached[1] == before:
        digest = cached[0]
    else:
        digest = sha256(path)
        if source_identity(path) != before:
            raise ValueError(f"Evidence file changed while hashing: {path}")
        if cache is not None:
            cache[str(path)] = (digest, before)
    return {"path": str(path), "bytes": before[4], "sha256": digest}


def verify_file_pin(record: object, output: Path | None = None,
                    cache: SourceCache | None = None) -> Path:
    if (not isinstance(record, dict) or not isinstance(record.get("path"), str) or
            type(record.get("bytes")) is not int or not isinstance(record.get("sha256"), str)):
        raise ValueError("Missing saved file receipt")
    path = Path(record["path"])
    if output is not None and not path.resolve().is_relative_to(output.resolve()):
        raise ValueError("Saved evidence file is outside its run directory")
    if file_pin(path, cache) != record:
        raise ValueError(f"Saved evidence file changed: {path}")
    return path


def setup_module_mode(metadata: dict[str, object]) -> bool:
    mode = metadata.get("isModule")
    if type(mode) is not bool:
        raise ValueError("Compilation setup has no boolean module mode")
    return mode


def effective_module_mode(metadata: dict[str, object], header_is_module: object) -> bool:
    if type(header_is_module) is not bool:
        raise ValueError("Compilation has no boolean native source module mode")
    return setup_module_mode(metadata) or cast(bool, header_is_module)


def compilation_module_mode(tools: Tools, compilation: dict[str, object]) -> bool:
    setup = verify_file_pin(compilation.get("setup"), tools.output, tools.file_cache)
    return effective_module_mode(read_json(setup), compilation.get("header_is_module"))


def setup_input_paths(metadata: dict[str, object], root: Path) -> tuple[str, ...]:
    arts = metadata.get("importArts")
    if not isinstance(arts, dict):
        raise ValueError("Lake setup has no import artifact map")
    paths: list[object] = []
    for parts in arts.values():
        if (not isinstance(parts, list) or len(parts) != 2 or
                any(not isinstance(group, list) for group in parts)):
            raise ValueError("Lake setup import artifacts are not two nested arrays")
        for group in parts:
            paths.extend(group)
    dynlibs, plugins = metadata.get("dynlibs", []), metadata.get("plugins", [])
    if not isinstance(dynlibs, list) or not isinstance(plugins, list):
        raise ValueError("Invalid Lake setup dynamic library or plugin list")
    paths.extend(dynlibs)
    paths.extend(plugin.get("path") if isinstance(plugin, dict) else plugin for plugin in plugins)
    if any(not isinstance(path, str) or not path for path in paths):
        raise ValueError("Invalid Lake setup input path")
    return tuple(sorted({str(Path(path) if Path(path).is_absolute() else root / path)
                         for path in cast(list[str], paths)}))


def standard_library_root(tools: Tools) -> Path | None:
    sysroot = Path(tools.environment.get("LEAN_SYSROOT", str(fact_resolve(tools.lean).parent.parent)))
    library = sysroot / "lib/lean"
    if library in tools.library_inventories and not fact_is_dir(library):
        raise ValueError("Compiler standard-library inventory changed")
    return library if fact_is_dir(library) else None


def verify_library_directories(directories: dict[Path, SourceIdentity],
                               inventory: tuple[str, ...] | None = None) -> None:
    # Empty inventories retain directory custody too: an existing empty
    # namespace directory is part of the ordered search space, so a
    # transient artifact created and removed there must change its
    # directory identity rather than slipping past exact verification.
    for path, identity in directories.items():
        if source_identity(path) != identity:
            raise ValueError(f"Compiler standard-library inventory changed: {path}")


def standard_library_paths(library: Path, tools: Tools | None = None) -> tuple[str, ...]:
    facts = _recorded_input_facts.get()
    if facts is None:
        return _standard_library_paths(library, tools)
    # A recorded derivation keeps a whole inventory as one fact. Reading it
    # again verifies its cached directory identities, exactly as this
    # function does for a cached inventory; an uncached result is volatile.
    token = _recorded_input_facts.set(None)
    try:
        result = _standard_library_paths(library, tools)
    finally:
        _recorded_input_facts.reset(token)
    cached = tools.library_inventories.get(library) if tools is not None else None
    if cached is not None and cached[0] == result:
        if facts.setdefault(("inventory", str(library)), result) != result:
            raise ValueError(f"Compilation input changed while its inputs were derived: {library}")
    else:
        facts[("volatile", str(library))] = object()
    return result


def _standard_library_paths(library: Path, tools: Tools | None = None) -> tuple[str, ...]:
    if not library.is_absolute() or not library.is_dir():
        raise ValueError("Saved compiler standard library is missing")
    cached = tools.library_inventories.get(library) if tools is not None else None
    if cached is not None:
        verify_library_directories(cached[1], cached[0])
        return cached[0]
    output = resolve_inventory_path(tools.output) if tools is not None else None
    output_parts = output.parts if output is not None else ()
    resolved_library = resolve_inventory_path(library)
    if output is not None and resolved_library.parts[:len(output_parts)] == output_parts:
        return ()

    def in_output(path: Path) -> bool:
        if output is None:
            return False
        return not inventory_path_outside_output(path, output_parts)

    directories = {library: source_identity(library)}
    directories.update((path, source_identity(path)) for path in library.rglob("*")
                       if path.is_dir() and not in_output(path))
    suffixes = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".so", ".dylib")
    paths = []
    for path in library.rglob("*"):
        if in_output(path):
            continue
        if path.is_dir() and path not in directories:
            raise ValueError(f"Compiler standard-library inventory changed: {path}")
        if path.name.endswith(suffixes) and path.is_file():
            paths.append(str(path))
    result = tuple(sorted(paths))
    verify_library_directories(directories, result)
    if tools is not None:
        tools.library_inventories[library] = (result, directories)
    return result


def cached_empty_inventory_directories(tools: Tools) -> set[Path]:
    """Directories belonging to cached inventories with no artifact files.

    File paths alone cannot place an empty namespace directory in a
    path-component guard. Including these directories lets Linux
    inotify watch their children and lets post-command identity checks
    observe a transient create/delete sequence there.
    """
    directories: set[Path] = set()
    for paths, inventory_directories in tools.library_inventories.values():
        if not paths:
            directories.update(inventory_directories)
    return directories


INVENTORY_SUFFIXES = (".olean.private", ".olean.server", ".olean", ".ir.sig", ".ir", ".so", ".dylib")
LAKE_GROWTH_DIRECTORY = "lake-growth"
# Lake custody that must outlive one invocation of a run: the first rejected
# preparation and the root artifact root's listing after the last accepted one.
LAKE_CUSTODY_DIRECTORY = "lake-custody"
# Written before each Lake preparation starts its child and removed only after every custody
# record of that preparation is saved. Its presence means a preparation's effects were never
# checked or recorded, so the output directory may not run another one.
PENDING_PREPARATION = "pending.json"


def refuse_interrupted_preparation(output: Path) -> None:
    pending = output / LAKE_CUSTODY_DIRECTORY / PENDING_PREPARATION
    if os.path.lexists(pending):
        raise ValueError(f"A Lake preparation was interrupted before its custody records were saved ({pending}); "
                         "start a new output directory")

# Root-package artifacts this run's own Lake preparations added (path to file
# pin), consulted only while saved rows are validated on resume.
_recorded_lake_growth: ContextVar[dict[str, dict[str, object]] | None] = ContextVar(
    "recorded_lake_growth", default=None)


def artifact_stem(path: str) -> str:
    for suffix in INVENTORY_SUFFIXES:
        if path.endswith(suffix):
            return path.removesuffix(suffix)
    return path


def build_artifact_module(tools: Tools, path: str) -> str | None:
    """Module named by an artifact inside the root package's artifact root."""
    build_root = resolve_inventory_path(tools.root / ".lake/build/lib/lean")
    resolved = resolve_inventory_path(Path(path))
    if not resolved.is_relative_to(build_root) or artifact_stem(str(resolved)) == str(resolved):
        return None
    return ".".join(Path(artifact_stem(str(resolved.relative_to(build_root)))).parts)


def provider_modules(tools: Tools, paths: Iterable[str]) -> set[str]:
    """Modules the given artifacts provide under any root Lean searches.

    Each artifact is matched under both its own spelling and its resolved
    path, so a symlinked search root cannot hide a provider.
    """
    build_root = tools.root / ".lake/build/lib/lean"
    roots = {build_root, resolve_inventory_path(build_root), *private_search_roots(tools)}
    library = standard_library_root(tools)
    if library is not None:
        roots.update((library, resolve_inventory_path(library)))
    parents: dict[Path, Path] = {}
    modules = set()
    for path in paths:
        if artifact_stem(path) == path:
            continue
        candidate = Path(path)
        try:
            if candidate.is_symlink():
                resolved = resolve_inventory_path(candidate)
            else:
                if candidate.parent not in parents:
                    parents[candidate.parent] = resolve_inventory_path(candidate.parent)
                resolved = parents[candidate.parent] / candidate.name
        except (OSError, RuntimeError):
            resolved = candidate
        for spelling in (path, str(resolved)):
            stem = Path(artifact_stem(spelling))
            if str(stem) == spelling:
                continue
            for root in roots:
                if stem.is_relative_to(root):
                    modules.add(".".join(stem.relative_to(root).parts))
    return modules


def shadowed_provider(tools: Tools, added: Iterable[str], existing: Iterable[str]) -> str | None:
    """An added artifact for a module some existing artifact already provides.

    A new artifact may only belong to a new module. One for a module that an
    existing artifact provides, in this root or another searched root, could
    add parts to or shadow a provider that was already resolved.
    """
    modules = provider_modules(tools, existing)
    for path in sorted(added):
        module = build_artifact_module(tools, path)
        if module is None or module in modules:
            return path
    return None


def searched_roots(tools: Tools) -> list[Path]:
    """Every root Lean searches for modules, under each spelling.

    The captured `LEAN_PATH` entries (absolute, as written and resolved,
    including entries that do not exist yet), the root package's artifact
    root and the compiler's standard library.
    """
    candidates = [tools.root / ".lake/build/lib/lean"]
    for entry in tools.environment.get("LEAN_PATH", "").split(os.pathsep):
        if entry.strip():
            path = Path(entry.strip())
            candidates.append(path if path.is_absolute() else tools.root / path)
    library = standard_library_root(tools)
    if library is not None:
        candidates.append(library)
    roots: list[Path] = []
    for path in candidates:
        for spelling in (path, resolve_inventory_path(path)):
            if spelling not in roots:
                roots.append(spelling)
    return roots


def module_artifact_paths(root: Path, module: str) -> list[Path]:
    relative = Path(*module.split("."))
    return [root / (str(relative) + suffix) for suffix in INVENTORY_SUFFIXES]


def path_state(path: Path) -> PathState | None:
    """The `lstat` identity of a path and of the file it resolves to, or None when it does not exist.

    A write through a symlink, or a change of where its target path leads,
    leaves the link's own identity unchanged, so a symlink's state also holds
    the full identity of the file it resolves to (None when it resolves to
    nothing). Retargeting or replacing the link changes its own identity.
    """
    try:
        own = path_component_identity(path, strict=True)
    except (FileNotFoundError, NotADirectoryError):
        return None
    if not stat.S_ISLNK(own[5]):
        return own, own
    try:
        return own, source_identity(path)
    except (FileNotFoundError, NotADirectoryError):
        return own, None


def provider_probes(tools: Tools, modules: Iterable[str], roots: list[Path]
                    ) -> dict[Path, PathState | None]:
    """The state of each artifact path under every searched root for each of `modules`.

    The lookup is targeted: only names a preparation may add are probed,
    so no dependency or compiler inventory is enumerated.
    """
    probes: dict[Path, PathState | None] = {}
    for module in sorted(modules):
        for root in roots:
            for path in module_artifact_paths(root, module):
                if path not in probes:
                    probes[path] = path_state(path)
    return probes


def nearest_existing(path: Path) -> tuple[Path, Path]:
    """The resolved nearest existing ancestor of a path and the rest of the path below it."""
    parent = path.parent
    while not os.path.lexists(parent) and parent != parent.parent:
        parent = parent.parent
    return resolve_inventory_path(parent), path.relative_to(parent)


def outside_build_root(path: Path, build_root: Path) -> bool:
    """Whether a path, resolved through its existing parents, lies outside the root artifact root."""
    parent, rest = nearest_existing(path)
    return not (parent / rest).is_relative_to(build_root)


def artifact_module_names(path: str, roots: list[Path]) -> dict[str, Path]:
    """Every module name an artifact provides, with a searched root that gives it."""
    names: dict[str, Path] = {}
    candidate = Path(path)
    spellings = [candidate]
    try:
        spellings.append(resolve_inventory_path(candidate))
    except (OSError, RuntimeError):
        pass
    for spelling in spellings:
        stem = Path(artifact_stem(str(spelling)))
        if str(stem) == str(spelling):
            continue
        for root in roots:
            if stem.is_relative_to(root) and stem != root:
                names.setdefault(".".join(stem.relative_to(root).parts), root)
    return names


def addition_conflict(tools: Tools, path: str, build_root: Path, roots: list[Path],
                      probes: dict[Path, PathState | None] | None = None) -> str | None:
    """Why an added root artifact shadows or aliases another provider, or None.

    It must provide exactly one module name across every searched root (no
    nested or aliased root may give it another), and no searched root may
    provide that module elsewhere. With `probes` (a preparation), every
    artifact path of the module under every root, the root artifact root
    included, must have been absent before the build. Without (a resume),
    no artifact path of the module outside the root artifact root may exist
    now; saved inputs decide inside it.
    """
    own = build_artifact_module(tools, path)
    names = artifact_module_names(path, roots)
    aliases = sorted(set(names) - {own})
    if own is None or aliases:
        alias = aliases[0] if aliases else str(path)
        return f"visible as module {alias} under searched root {names.get(alias, build_root)}"
    for root in roots:
        for candidate in module_artifact_paths(root, own):
            if probes is not None:
                if candidate not in probes:
                    return f"module {own} was not probed under {root}"
                if probes[candidate] is not None:
                    return f"module {own} was already provided by {candidate}"
            elif outside_build_root(candidate, build_root) and path_state(candidate) is not None:
                return f"module {own} is provided by {candidate}"
    return None


IDENTITY_FIELDS = ("dev", "ino", "ctime", "mtime", "size", "mode")


def root_artifact_prefixes(root: Path) -> tuple[str, ...]:
    build = root / ".lake/build/lib/lean"
    return tuple(dict.fromkeys((str(build) + os.sep, str(resolve_inventory_path(build)) + os.sep)))


def is_root_artifact_path(path: object, prefixes: tuple[str, ...]) -> bool:
    return isinstance(path, str) and path.startswith(prefixes) and artifact_stem(path) != path


def record_root_custody(tools: Tools, receipts: Iterable[object]) -> None:
    """Remember the identity of root-package artifacts at their first pin.

    Called where receipts are made or checked, right after `file_pin` filled
    the cache with the identity it hashed. An existing record is kept, so the
    expectation is the one from the first pin.
    """
    prefixes = root_artifact_prefixes(tools.root)
    for receipt in receipts:
        path = receipt.get("path") if isinstance(receipt, dict) else None
        if not is_root_artifact_path(path, prefixes) or path in tools.root_custody:
            continue
        cached = tools.file_cache.get(cast(str, path))
        if cached is not None and cached[0] == receipt.get("sha256"):
            tools.root_custody[cast(str, path)] = (dict(receipt), cached[1])


SAVED_INPUT_MANIFEST = re.compile(r"[0-9a-f]{64}\.json")


def saved_root_receipts(root: Path, output: Path, growth: dict[str, dict[str, object]],
                        rewrites: dict[str, dict[str, object]] | None = None) -> dict[str, dict[str, object]]:
    """Every root-package artifact receipt an earlier invocation of this run saved.

    These are the additions and rewrites its accepted Lake preparations
    recorded (`lake-growth/`) and the root-package entries of every compilation input
    manifest it pinned (`inputs/`), whether or not a successful row refers
    to them. Each path must have one receipt.
    """
    prefixes = root_artifact_prefixes(root)
    receipts: dict[str, dict[str, object]] = {}

    def add(receipt: object, source: Path) -> None:
        if (not isinstance(receipt, dict) or not isinstance(receipt.get("path"), str) or
                type(receipt.get("bytes")) is not int or not isinstance(receipt.get("sha256"), str)):
            raise ValueError(f"Invalid saved artifact receipt in {source}")
        if receipts.setdefault(receipt["path"], receipt) != receipt:
            raise ValueError(f"Saved receipts disagree on a root-package artifact: {receipt['path']}")

    for path, receipt in [*growth.items(), *(rewrites or {}).items()]:
        if not is_root_artifact_path(path, prefixes) or not Path(path).is_absolute():
            raise ValueError(f"Recorded Lake growth is outside the root artifact root: {path}")
        add(receipt, output / LAKE_GROWTH_DIRECTORY)
    inputs = output / "inputs"
    for manifest in sorted(inputs.iterdir()) if inputs.is_dir() else ():
        if not SAVED_INPUT_MANIFEST.fullmatch(manifest.name):
            continue
        files = read_json(manifest).get("files")
        if not isinstance(files, list):
            raise ValueError(f"Invalid saved compilation input manifest: {manifest}")
        for receipt in files:
            if isinstance(receipt, dict) and is_root_artifact_path(receipt.get("path"), prefixes):
                add(receipt, manifest)
    return receipts


def verify_saved_root_receipts(receipts: dict[str, dict[str, object]], cache: SourceCache) -> None:
    """Each saved root-package receipt still describes its file, before any Lake command."""
    for path, receipt in receipts.items():
        try:
            unchanged = file_pin(Path(path), cache) == receipt
        except (OSError, ValueError):
            unchanged = False
        if not unchanged:
            raise ValueError(f"Saved root-package artifact is missing or changed since it was pinned: {path}")


def verify_root_custody(tools: Tools, custody: dict[str, tuple[dict[str, object], SourceIdentity]]) -> None:
    """Each pinned root-package artifact keeps the identity and bytes of its first pin."""
    for path, (receipt, identity) in custody.items():
        try:
            current = source_identity(Path(path))
        except OSError as error:
            raise ValueError(f"Pinned root-package artifact was removed: {path}") from error
        changed = [name for name, before, after in zip(IDENTITY_FIELDS, identity, current) if before != after]
        if not changed and file_pin(Path(path), tools.file_cache) != receipt:
            changed = ["sha256"]
        if changed:
            raise ValueError(f"Pinned root-package artifact changed ({', '.join(changed)}): {path}")


def namespace_topology(paths: Iterable[Path]) -> dict[Path, tuple[SourceIdentity, Path]]:
    """Each directory's own node (lstat device, inode and mode) and resolved path.

    Additions may change a directory's timestamps, never its node or where
    its path leads.
    """
    topology = {}
    for path in paths:
        try:
            topology[path] = (path_component_identity(path, mutable=True), resolve_inventory_path(path))
        except OSError:
            topology[path] = ((0, 0, 0, 0, 0, 0), path)
    return topology


def build_root_listing(tools: Tools, build_root: Path) -> tuple[set[Path], set[Path]]:
    """Top-level namespace directories and module artifacts of the root artifact root."""
    output_parts = resolve_inventory_path(tools.output).parts
    directories: set[Path] = set()
    files: set[Path] = set()
    for child in sorted(build_root.iterdir()) if build_root.is_dir() else ():
        if not inventory_path_outside_output(child, output_parts):
            continue
        if child.is_dir():
            directories.add(child)
        elif child.is_file() and artifact_stem(str(child)) != str(child):
            files.add(child)
    return directories, files


def run_lake_preparation(tools: Tools, argv: list[str], label: Path,
                         modules: frozenset[str]) -> dict[str, object]:
    """Run a Lake build that may add root-package artifacts, then renew their custody.

    A batch's Lake preparation legitimately adds artifacts to the root
    package's build tree, so an inventory an earlier batch cached there no
    longer describes it. Before the build, every cached inventory is
    verified, every root-package artifact pinned so far must still have the
    full identity and bytes of its first pin (`root_custody`), and the root
    artifact root's top-level listing must match the one left by the last
    accepted preparation. Every top-level namespace is then inventoried.
    During the build, the root namespaces and the artifact root's ancestors
    are watched for moves and attribute changes where the platform allows;
    after it, each keeps its directory node and resolved path, pinned
    artifacts are checked again, nothing may be removed, and only artifacts
    of new modules among `modules` (the requested targets and their frozen
    local dependencies) may be added. Every existing root artifact is stated
    before the build, a symlink with the file it resolves to; one whose state
    changed was rewritten, which only a module among `modules` may be, and
    never a pinned one. Root inventories
    are then taken again with new directory custody, and the additions and
    rewrites are taken into custody and recorded under the output directory
    for resume. Compiler and dependency inventories stay
    cached. Independently of any cache, every artifact path of each module
    in `modules` under every searched root (`LEAN_PATH` entries under both
    spellings, the root artifact root and the compiler library) is probed
    before the build: those outside the root artifact root must keep their
    state through it (watched on Linux), and an addition must have been
    absent everywhere and may not be visible as another module under a
    nested or enclosing root. The first rejection is kept on `tools`, and
    every later preparation is refused.
    """
    custody_directory = tools.output / LAKE_CUSTODY_DIRECTORY
    refuse_interrupted_preparation(tools.output)
    if not tools.lake_custody_failure and (custody_directory / "rejected.json").exists():
        recorded = read_json(custody_directory / "rejected.json").get("error")
        tools.lake_custody_failure.append(recorded if isinstance(recorded, str) else "unreadable rejection record")
    if tools.lake_custody_failure:
        raise ValueError(f"An earlier Lake preparation was rejected: {tools.lake_custody_failure[0]}")
    cached_before = dict(tools.library_inventories)
    released: dict[Path, tuple[tuple[str, ...], dict[Path, SourceIdentity]]] = {}
    rewritten: dict[str, dict[str, object]] = {}
    try:
        for paths, directories in tools.library_inventories.values():
            verify_library_directories(directories, paths)
        custody = dict(tools.root_custody)
        verify_root_custody(tools, custody)
        build_root = resolve_inventory_path(tools.root / ".lake/build/lib/lean")
        namespaces_before, files_before = build_root_listing(tools, build_root)
        if "after" not in tools.root_listing and (custody_directory / "listing.json").exists():
            # A resumed invocation starts from the listing the previous one accepted.
            listing = read_json(custody_directory / "listing.json")
            names = [listing.get(key) for key in ("namespaces", "files")]
            if any(not isinstance(group, list) or any(not isinstance(name, str) for name in group)
                   for group in names):
                raise ValueError("Recorded root artifact listing is invalid")
            tools.root_listing["after"] = tuple(frozenset(build_root / name for name in group)
                                                for group in names)
        expected = tools.root_listing.get("after")
        if expected is not None and (frozenset(namespaces_before), frozenset(files_before)) != expected:
            changed = sorted(set(namespaces_before) ^ set(expected[0]) | set(files_before) ^ set(expected[1]))
            raise ValueError(f"Root artifact root changed since the last Lake preparation: {changed[0]}")
        for namespace in sorted(namespaces_before):
            standard_library_paths(namespace, tools)
        released = {library: entry for library, entry in tools.library_inventories.items()
                    if all(resolve_inventory_path(path).is_relative_to(build_root)
                           for path in (library, *entry[1]))}
        existing = [*(path for paths, _ in tools.library_inventories.values() for path in paths),
                    *map(str, files_before)]
        ancestors = [tools.root / ".lake/build/lib/lean", *(tools.root / ".lake/build/lib/lean").parents]
        ancestors = ancestors[:ancestors.index(tools.root)]
        watched = {path for path in (*(path for library, (_, directories) in released.items()
                                       for path in (library, *directories)), *ancestors)
                   if path.exists() or path.is_symlink()}
        topology = namespace_topology(watched)
        identities = path_component_identities(set(watched))
        # Every searched root's artifact paths for the modules this build may
        # add, taken now whatever is cached. Those outside the root artifact
        # root belong to other writers: they must keep their state through the
        # build, and on Linux their nearest existing directory is watched for
        # those names.
        roots = searched_roots(tools)
        probes = provider_probes(tools, modules, roots)
        external: dict[Path, PathState | None] = {}
        absent_names: dict[Path, set[str]] = {}
        located: dict[Path, tuple[Path, Path]] = {}
        for path, state in probes.items():
            if path.parent not in located:
                ancestor, rest = nearest_existing(path.parent / path.name)
                located[path.parent] = (ancestor, rest.parent)
            ancestor, rest = located[path.parent]
            if (ancestor / rest / path.name).is_relative_to(build_root):
                continue
            external[path] = state
            if ancestor.is_dir():
                absent_names.setdefault(ancestor, set()).add((rest / path.name).parts[0])
        for parent in absent_names:
            identities.setdefault(parent, path_component_identity(parent))
        # Every existing root artifact, stated (not hashed): an identity that
        # changes through the build is a rewrite. A symlink's state includes the
        # file it resolves to, which a write through the link changes.
        states = {path: path_state(Path(path)) for paths, _ in released.values() for path in paths}
        states.update((str(path), path_state(path)) for path in files_before)
        # From here until every record below is saved, an interruption leaves this marker.
        write_json(custody_directory / PENDING_PREPARATION, {"preparation": str(label), "modules": sorted(modules)})
        with guard_path_component_moves(identities, mutable_roots=(*watched, build_root, tools.output),
                                        child_names=absent_names):
            result = tools.run(argv, label)
        for path, before in external.items():
            if path_state(path) != before:
                raise ValueError(f"Lake preparation changed a module artifact outside the root package: {path}")
        for path, before in topology.items():
            after = namespace_topology([path])[path]
            if after != before:
                raise ValueError(f"Lake preparation moved or replaced a root namespace: {path}")
        verify_root_custody(tools, custody)
        for library, (paths, directories) in tools.library_inventories.items():
            if library not in released:
                verify_library_directories(directories, paths)
        added: dict[str, dict[str, object]] = {}
        for library, (paths, _) in released.items():
            del tools.library_inventories[library]
            current = set(standard_library_paths(library, tools))
            removed = sorted(set(paths) - current)
            if removed:
                raise ValueError(f"Lake preparation removed a root-package artifact: {removed[0]}")
            for path in current - set(paths):
                added[path] = file_pin(Path(path), tools.file_cache)
        namespaces_after, files_after = build_root_listing(tools, build_root)
        removed_files = sorted(files_before - files_after)
        if removed_files:
            raise ValueError(f"Lake preparation removed a root-package artifact: {removed_files[0]}")
        for namespace in sorted(namespaces_after - namespaces_before):
            for path in standard_library_paths(namespace, tools):
                added[path] = file_pin(Path(path), tools.file_cache)
        for path in sorted(files_after - files_before):
            added[str(path)] = file_pin(path, tools.file_cache)
        for path in sorted(added):
            if build_artifact_module(tools, path) not in modules:
                raise ValueError(f"Lake preparation added an artifact outside its requested modules: {path}")
        for path, before in states.items():
            if path not in custody and path_state(Path(path)) != before:
                rewritten[path] = file_pin(Path(path), tools.file_cache)
        for path in sorted(rewritten):
            own = build_artifact_module(tools, path)
            if own not in modules:
                raise ValueError(f"Lake preparation rewrote an artifact outside its requested modules: {path}")
            aliases = sorted(set(artifact_module_names(path, roots)) - {own})
            if aliases:
                raise ValueError(f"Lake preparation rewrote an artifact visible as module {aliases[0]}: {path}")
        shadow = shadowed_provider(tools, added, existing)
        if shadow is not None:
            raise ValueError(f"Lake preparation added an artifact for an existing module: {shadow}")
        for path in sorted(added):
            conflict = addition_conflict(tools, path, build_root, roots, probes)
            if conflict is not None:
                raise ValueError(f"Lake preparation added a shadowing artifact: {path} ({conflict})")
    except (OSError, ValueError) as error:
        # Nothing taken during a rejected attempt becomes trusted, and every
        # later preparation is refused.
        tools.library_inventories.clear()
        tools.library_inventories.update(cached_before)
        tools.lake_custody_failure.append(str(error))
        if not (custody_directory / "rejected.json").exists():
            write_json(custody_directory / "rejected.json", {"preparation": str(label), "error": str(error)})
        # The rejection record now keeps the output directory closed.
        (custody_directory / PENDING_PREPARATION).unlink(missing_ok=True)
        raise
    tools.root_listing["after"] = (frozenset(namespaces_after), frozenset(files_after))
    write_json(custody_directory / "listing.json",
               {"namespaces": sorted(path.name for path in namespaces_after),
                "files": sorted(path.name for path in files_after)})
    if added or rewritten:
        # Accepted growth and rewrites are under custody from now on, as if pinned.
        record_root_custody(tools, [*added.values(), *rewritten.values()])
        write_json(tools.output / LAKE_GROWTH_DIRECTORY / f"{time.time_ns()}.json",
                   {"preparation": str(label), "added": [added[path] for path in sorted(added)],
                    "rewritten": [rewritten[path] for path in sorted(rewritten)]})
    (custody_directory / PENDING_PREPARATION).unlink()
    return result


def local_dependency_closure(inventory: list[dict[str, object]], targets: set[str]) -> frozenset[str]:
    """Requested modules and their frozen local dependencies: what Lake may build."""
    dependencies = {str(row["module"]): row.get("direct_local_dependencies") for row in inventory}
    closure: set[str] = set()
    pending = list(targets)
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        closure.add(module)
        direct = dependencies.get(module)
        if isinstance(direct, list):
            pending.extend(str(name) for name in direct)
    return frozenset(closure)


def read_lake_growth(output: Path, key: str = "added") -> dict[str, dict[str, object]]:
    """Recorded additions (`added`) or rewrites of existing artifacts (`rewritten`), by path."""
    growth: dict[str, dict[str, object]] = {}
    directory = output / LAKE_GROWTH_DIRECTORY
    for record in sorted(directory.glob("*.json")) if directory.is_dir() else ():
        added = read_json(record).get(key, [] if key == "rewritten" else None)
        if not isinstance(added, list):
            raise ValueError(f"Invalid recorded Lake growth: {record}")
        for pin in added:
            if (not isinstance(pin, dict) or not isinstance(pin.get("path"), str) or
                    growth.setdefault(pin["path"], pin) != pin):
                raise ValueError(f"Invalid recorded Lake growth: {record}")
    return growth


def verify_recorded_growth(tools: Tools | None, saved: tuple[str, ...], current: tuple[str, ...]) -> None:
    """Accept a saved row's input set that later recorded Lake preparations grew.

    Only while saved rows are validated on resume. Every saved input must
    remain; each new one must be a root-package artifact a recorded Lake
    preparation added, with its recorded bytes, for a module none of the
    saved inputs provides. The saved pins are verified by the caller.
    """
    growth = _recorded_lake_growth.get()
    added = set(current) - set(saved)
    if tools is None or growth is None or not added or not set(saved) <= set(current):
        raise ValueError("Saved compilation input manifest has a different setup path set")
    for path in sorted(added):
        try:
            recorded = path in growth and file_pin(Path(path), tools.file_cache) == growth[path]
        except (OSError, ValueError):
            recorded = False
        if not recorded or build_artifact_module(tools, path) is None:
            raise ValueError(f"Saved compilation inputs gained an unrecorded artifact: {path}")
    shadow = shadowed_provider(tools, added, saved)
    if shadow is not None:
        raise ValueError(f"Saved compilation inputs gained a provider for a consumed module: {shadow}")
    build_root = resolve_inventory_path(tools.root / ".lake/build/lib/lean")
    roots = searched_roots(tools)
    for path in sorted(added):
        conflict = addition_conflict(tools, path, build_root, roots)
        if conflict is not None:
            raise ValueError(f"Saved compilation inputs gained a shadowing artifact: {path} ({conflict})")


def full_import_artifacts(metadata: dict[str, object], root: Path) -> dict[str, list[list[str]]]:
    setup_input_paths(metadata, root)
    result = {}
    for module, original in cast(dict[str, list[list[str]]], metadata["importArts"]).items():
        groups = [[str(Path(path) if Path(path).is_absolute() else root / path)
                   for path in group] for group in original]
        prefixes = [group[0].removesuffix(suffix) if group and group[0].endswith(suffix) else None
                    for group, suffix in zip(groups, (".olean", ".ir.sig"))]
        for index, suffixes in enumerate(((".olean", ".olean.server", ".olean.private"),
                                          (".ir.sig", ".ir"))):
            prefix = (prefixes[index] or prefixes[1 - index]) if not groups[index] or prefixes[index] else None
            if prefix is not None:
                if not groups[index] and not fact_exists(Path(prefix + suffixes[0])):
                    continue
                groups[index] = list(dict.fromkeys([*groups[index],
                    *(prefix + suffix for suffix in suffixes if fact_exists(Path(prefix + suffix)))]))
                if index == 0 and prefix + ".olean.private" in groups[index] and prefix + ".olean.server" not in groups[index]:
                    raise ValueError("Snapshot private input has no server artifact")
                if index == 0 and prefix + ".olean.server" in groups[index] and prefix + ".olean.private" not in groups[index]:
                    raise ValueError("Snapshot server input has no private artifact")
                if index == 1 and prefix + ".ir.sig" in groups[index] and prefix + ".ir" not in groups[index]:
                    raise ValueError("Snapshot IR signature has no IR artifact")
        result[module] = groups
    return result


def selected_namespace_artifact_paths(metadata: dict[str, object], root: Path,
                                      library: Path | None, tools: Tools | None = None) -> tuple[str, ...]:
    # Pinning follows the same strict root inference as compilation
    # and discovery: a top-level artifact whose parent is not an
    # explicitly captured search root does not make its containing
    # directory a trusted namespace inventory.
    strict_roots = {
        str(fact_resolve(Path(candidate)))
        for candidate in selected_artifact_roots(
            metadata, root, strict=True,
            search_roots=private_search_roots(tools) if tools is not None else ())
    }
    namespaces = set()
    for module, groups in full_import_artifacts(metadata, root).items():
        if not groups[0]:
            continue
        relative = private_module_olean_path(module)
        path = fact_inventory_resolve(Path(groups[0][0]))
        if path.parts[-len(relative.parts):] != relative.parts:
            continue
        selected = path.parents[len(relative.parts) - 1]
        if str(selected) not in strict_roots:
            continue
        if library is None or selected != fact_inventory_resolve(library):
            namespaces.add(selected / private_module_components(module)[0])
    paths: set[str] = set()
    for namespace in namespaces:
        paths.update(namespace_artifact_paths(namespace, tools))
    return tuple(sorted(paths))


def namespace_artifact_paths(namespace: Path, tools: Tools | None = None) -> set[str]:
    paths: set[str] = set()
    if fact_is_dir(namespace):
        paths.update(standard_library_paths(namespace, tools))
    for suffix in (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".so", ".dylib"):
        path = Path(str(namespace) + suffix)
        if fact_is_file(path):
            paths.add(str(path))
    if tools is not None:
        output_parts = fact_inventory_resolve(tools.output).parts
        paths = {path for path in paths
                 if inventory_path_outside_output(Path(path), output_parts)}
    return paths


def selected_root_artifact_paths(metadata: dict[str, object], root: Path,
                                 tools: Tools | None = None) -> tuple[str, ...]:
    """Complete namespace inventories of Lake-selected artifact roots.

    The forced compile searches each selected root wholesale, including
    namespaces absent from the public `importArts` map, so private-only
    namespaces living in a selected (possibly noncanonical/external)
    root must be pinned before compilation too. `compilation_input_paths`
    itself only pins publicly represented namespaces; these complete
    inventories live in the fallback receipt to preserve resume isolation.
    Only strict module-path roots are inventoried wholesale: a flat
    fixture artifact's containing directory is not an artifact root
    (and is not exposed to the forced compile), and neither it nor
    the optimizer's mutable output tree is recursively inventoried.
    """
    paths: set[str] = set()
    output = fact_inventory_resolve(tools.output) if tools is not None else None
    output_parts = output.parts if output is not None else ()
    search_roots = private_search_roots(tools) if tools is not None else ()
    for selected in selected_artifact_roots(metadata, root, strict=True,
                                            search_roots=search_roots):
        root_path = Path(selected)
        if output is not None and root_path.parts[:len(output_parts)] == output_parts:
            continue
        try:
            children = fact_children(root_path)
        except OSError:
            continue
        root_paths: set[str] = set()
        for child in children:
            if fact_is_dir(child):
                namespace = child
            elif (fact_is_file(child) and child.name.endswith(".olean") and
                    not child.name.endswith((".olean.server", ".olean.private"))):
                namespace = Path(str(child).removesuffix(".olean"))
            else:
                continue
            if output is not None:
                resolved = fact_inventory_resolve(namespace)
                if resolved.parts[:len(output_parts)] == output_parts:
                    continue
            root_paths.update(namespace_artifact_paths(namespace, tools))
        if tools is not None and not root_paths and fact_is_dir(root_path):
            # A fileless selected root would otherwise cache no
            # directory at all, even though the forced compile still
            # searches it. Cache the root itself for custody without
            # changing nonempty roots' namespace-only custody.
            root_paths.update(standard_library_paths(fact_inventory_resolve(root_path), tools))
        paths.update(root_paths)
    return tuple(sorted(paths))


def canonical_namespace_artifact_paths(root: Path, library: Path | None,
                                       tools: Tools | None = None) -> tuple[str, ...]:
    """Artifacts under every namespace of the canonical artifact roots.

    Private-only dependencies can live in namespaces absent from the
    public `importArts` map; seeding their roots at snapshot time is not
    enough, because the snapshot verification requires every private
    artifact to have been pinned before compilation. Pin the canonical
    namespace inventories up front (publicly selected namespaces are
    already pinned by `selected_namespace_artifact_paths`).
    """
    if tools is not None:
        artifact_roots = canonical_artifact_roots(tools)
    else:
        # Without a captured Lake environment there is no selected
        # package graph, so never enumerate `.lake/packages`; only the
        # project's own build root belongs to the selected corpus.
        artifact_roots = []
        project_root = root / ".lake/build/lib/lean"
        if fact_is_dir(project_root):
            artifact_roots.append(fact_resolve(project_root))
    paths: set[str] = set()
    output = fact_inventory_resolve(tools.output) if tools is not None else None
    output_parts = output.parts if output is not None else ()
    for artifact_root in artifact_roots:
        if library is not None and artifact_root == fact_inventory_resolve(library):
            continue
        if output is not None and artifact_root.parts[:len(output_parts)] == output_parts:
            # The optimizer's mutable output tree must never become
            # fallback input, even when a canonical build root happens
            # to be beneath the configured --output directory. Ancestor
            # roots still scan normally below, skipping output children.
            continue
        try:
            children = fact_children(artifact_root)
        except OSError:
            continue
        root_paths: set[str] = set()
        for child in children:
            if fact_is_dir(child):
                resolved_child = fact_inventory_resolve(child)
                if output is not None and resolved_child == output:
                    continue
                # If this namespace contains the output directory,
                # `standard_library_paths`/`namespace_artifact_paths`
                # exclude that mutable subtree while retaining the
                # namespace's legitimate artifacts. Supported
                # compilation/discovery flows separately reject this
                # placement before trusting the inventory.
                namespace = child
            elif (fact_is_file(child) and child.name.endswith(".olean") and
                    not child.name.endswith((".olean.server", ".olean.private"))):
                namespace = Path(str(child).removesuffix(".olean"))
            else:
                continue
            root_paths.update(namespace_artifact_paths(namespace, tools))
        if output is not None:
            root_paths = {path for path in root_paths
                          if inventory_path_outside_output(Path(path), output_parts)}
        if tools is not None and not root_paths and fact_is_dir(artifact_root):
            # Namespace scans alone never name a completely fileless
            # canonical root, yet LEAN_PATH still searches it during
            # compilation. Cache that root itself for custody;
            # `standard_library_paths` excludes any optimizer-output
            # subtree from both files and directory custody.
            root_paths.update(standard_library_paths(artifact_root, tools))
        paths.update(root_paths)
    return tuple(sorted(paths))


def computation_paths_without_output(tools: Tools) -> Tools:
    """Tools view for explicit-file path composition outside live trust.

    Saved-fixture callers intentionally construct `Tools(root, root)`:
    their output directory is the project tree itself, so the usual
    mutable-output exclusions would make every project/toolchain file
    beneath it invisible. For path-set composition only, anchor the
    view at a nonexistent sibling output directory while preserving
    the real output for manifest writes (`pin_input_paths`). Actual
    compilation/fallback/discovery surfaces keep using the original
    `tools` and reject trusted roots beneath real output.
    """
    if fact_resolve(tools.output) != fact_resolve(tools.root):
        return tools
    placeholder = fact_resolve(tools.root).parent / (fact_resolve(tools.root).name + ".saved-fixture-no-output")
    return Tools(
        tools.root, placeholder, tools.lake, tools.lean, tools.helpers,
        tools.environment, tools.timeout, tools.time_binary, tools.lake_config,
        lean_threads=tools.lean_threads, lake_jobs=tools.lake_jobs,
        file_cache=tools.file_cache, input_manifests=tools.input_manifests,
        library_inventories=tools.library_inventories,
        validated_analysis_inputs=tools.validated_analysis_inputs,
        validated_snapshot_groups=tools.validated_snapshot_groups,
        prepared_inputs=tools.prepared_inputs, root_custody=tools.root_custody,
        lake_custody_failure=tools.lake_custody_failure, root_listing=tools.root_listing,
        lake_manifest_bytes=tools.lake_manifest_bytes)


def prepared_derivation(kind: str, metadata: dict[str, object], root: Path, library: Path | None,
                        tools: Tools | None, derivation: Callable[[], tuple[str, ...]]) -> tuple[str, ...]:
    prepared = active_prepared_inputs(tools)
    if prepared is None or tools is None:
        return derivation()
    # The key holds every in-memory input of the derivation (capture the
    # pinned manifest bytes first); everything else it reads is a recorded
    # filesystem fact.
    pinned_lake_manifest_bytes(tools)
    try:
        key = (kind, json.dumps(metadata, sort_keys=True, ensure_ascii=False), str(root),
               None if library is None else str(library), str(tools.root), str(tools.output),
               str(tools.lean), tuple(sorted(tools.environment.items())),
               tuple(sorted((str(path), raw) for path, raw in tools.lake_manifest_bytes.items())))
    except (TypeError, ValueError):
        return derivation()
    return prepared.derive(key, derivation)


def compilation_input_paths(metadata: dict[str, object], root: Path,
                            library: Path | None, tools: Tools | None = None) -> tuple[str, ...]:
    return prepared_derivation("compilation_inputs", metadata, root, library, tools,
                               lambda: derive_compilation_input_paths(metadata, root, library, tools))


def derive_compilation_input_paths(metadata: dict[str, object], root: Path,
                                   library: Path | None, tools: Tools | None = None) -> tuple[str, ...]:
    path_tools = tools
    if tools is not None:
        path_tools = computation_paths_without_output(tools)
        selected = selected_artifact_roots(
            metadata, root, strict=True, search_roots=private_search_roots(path_tools))
        # Explicit-file pinning and saved-fixture verification can
        # legitimately use Tools(root, root), where trusted roots are
        # necessarily beneath output. Only the direction that exposes
        # mutable output to Lean search (`output` under a trusted
        # root) is rejected on this path-composition surface. Actual
        # compilation/fallback/discovery call sites still reject both
        # directions before trusting a searched root.
        reject_output_nested_in_roots(
            path_tools, ordered_trusted_roots(path_tools, selected), _during_post_init=True)
    paths = set(setup_input_paths(metadata, root))
    paths.update(path for groups in full_import_artifacts(metadata, root).values()
                 for group in groups for path in group)
    if library is not None:
        paths.update(standard_library_paths(library, path_tools))
    paths.update(selected_namespace_artifact_paths(metadata, root, library, path_tools))
    if path_tools is not None:
        # The pinned Lake manifest authorizes canonical package
        # roots, so it is a compilation trust input itself: pinning
        # it in the input receipt and guarding its identity around
        # compilation binds those roots to the exact manifest bytes
        # parsed at environment capture.
        manifest_input = pinned_lake_manifest_input_path(path_tools)
        if manifest_input is not None:
            paths.add(manifest_input)
    return tuple(sorted(paths))


def verify_input_manifest(record: object, paths: tuple[str, ...], output: Path,
                          tools: Tools | None = None) -> list[dict[str, object]]:
    cache = tools.file_cache if tools is not None else None
    path = verify_file_pin(record, output, cache)
    grown = False
    cached = tools.input_manifests.get(paths) if tools is not None else None
    if cached is not None and cached[0] == record:
        files = cached[1]
    else:
        files = read_json(path).get("files")
        if (not isinstance(files, list) or
                any(not isinstance(row, dict) or not isinstance(row.get("path"), str) for row in files)):
            raise ValueError("Saved compilation input manifest has a different setup path set")
        saved_paths = tuple(row["path"] for row in files)
        if saved_paths != paths:
            verify_recorded_growth(tools, saved_paths, paths)
            grown = True
    prepared = active_prepared_inputs(tools)
    for receipt in files:
        if prepared is None:
            verify_file_pin(receipt, cache=cache)
        else:
            prepared.verify_pin(receipt)
    if tools is not None:
        record_root_custody(tools, files)
        for inventory_paths, directories in tools.library_inventories.values():
            if prepared is None:
                verify_library_directories(directories, inventory_paths)
            else:
                prepared.verify_directories(directories)
        if not grown:
            tools.input_manifests[paths] = (cast(dict[str, object], record), files)
    return files


def pin_input_paths(tools: Tools, paths: tuple[str, ...]) -> dict[str, object]:
    if str(tools.root / "lake-manifest.json") in paths:
        verify_pinned_lake_manifest(tools)
    cached = tools.input_manifests.get(paths)
    if cached is not None:
        verify_input_manifest(cached[0], paths, tools.output, tools)
        return cached[0]
    files = [file_pin(Path(path), tools.file_cache) for path in paths]
    record_root_custody(tools, files)
    for inventory_paths, directories in tools.library_inventories.values():
        verify_library_directories(directories, inventory_paths)
    value = {"files": files}
    content = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    digest = hashlib.sha256(content).hexdigest()
    path = tools.output / "inputs" / (digest + ".json")
    if not path.exists():
        write_json(path, value)
    receipt = {"path": str(path), "bytes": len(content), "sha256": digest}
    verify_file_pin(receipt, tools.output, tools.file_cache)
    tools.input_manifests[paths] = (receipt, files)
    return receipt


def pin_setup_inputs(tools: Tools, metadata: dict[str, object]) -> dict[str, object]:
    library = standard_library_root(tools)
    return pin_input_paths(tools, compilation_input_paths(metadata, tools.root, library, tools))


def private_fallback_artifact_paths(tools: Tools, metadata: dict[str, object]) -> tuple[str, ...]:
    return prepared_derivation("private_fallback", metadata, tools.root, None, tools,
                               lambda: derive_private_fallback_artifact_paths(tools, metadata))


def derive_private_fallback_artifact_paths(tools: Tools, metadata: dict[str, object]) -> tuple[str, ...]:
    """Exact pre-compilation fallback inventory for private resolution.

    Unions the canonical LEAN_PATH-selected namespace inventories with
    the *complete* namespace inventories of every Lake-selected explicit
    artifact root, so private-only namespaces in selected (possibly
    noncanonical/external) roots are pinned before compilation as well.
    Recomputing this exact set after compilation/snapshot verification
    proves no transient addition/removal entered the search space.
    Canonical roots in this inventory may be authorized by the pinned
    Lake manifest, so the manifest itself rides in the same receipt
    (when it could authorize roots) and is identity-guarded with the
    artifacts it made discoverable.
    """
    reject_output_nested_in_roots(tools, private_inventory_roots(tools, metadata))
    library = standard_library_root(tools)
    paths = set(canonical_namespace_artifact_paths(tools.root, library, tools))
    paths.update(selected_root_artifact_paths(metadata, tools.root, tools))
    manifest_input = pinned_lake_manifest_input_path(tools)
    if manifest_input is not None:
        paths.add(manifest_input)
    return tuple(sorted(paths))


def pin_private_fallback_inputs(tools: Tools, metadata: dict[str, object]) -> dict[str, object]:
    """Pin the fallback inventory in a separate receipt.

    Private-only dependencies may be discovered later in namespaces that
    no public artifact selected, so their artifacts must be pinned before
    compilation. Keeping that broad inventory out of the per-target
    `input_manifest` preserves resume isolation: rebuilding an unrelated
    fallback artifact does not invalidate this target's saved row, and
    snapshot verification only compares the discovered private closure
    against this receipt.
    """
    return pin_input_paths(tools, private_fallback_artifact_paths(tools, metadata))


def verify_private_fallback_inventory(tools: Tools, metadata: dict[str, object],
                                      expected: tuple[str, ...]) -> None:
    """Reject transient fallback-inventory membership changes.

    Identity and hash checks only compare files that existed at pinning
    time; an unpinned shadow transiently created ahead of the pinned
    copy during compilation (and removed after) slips through them.
    Recomputing the selected-root inventory and comparing it to the
    expected receipt's selected-root subset proves no create/delete/move
    changed that resolution search space. (Canonical inventories keep
    their own directory-stamp custody in `standard_library_paths`.)
    The recomputation drops any `tools.library_inventories` entries
    first scanned here: caching a transient namespace's directory
    stamps would make a later re-check after the transient file is
    removed fail on the poisoned cache instead of the restored exact
    inventory. Previously cached inventories keep their cached
    semantics (and directory custody) exactly as at pinning time.
    """
    roots = selected_artifact_roots(
        metadata, tools.root, strict=True, search_roots=private_search_roots(tools))
    cached_before = set(tools.library_inventories)
    try:
        current = selected_root_artifact_paths(metadata, tools.root, tools)
    finally:
        for key in set(tools.library_inventories) - cached_before:
            del tools.library_inventories[key]
    expected_selected = tuple(
        path for path in expected
        if any(Path(path).is_relative_to(Path(root)) for root in roots))
    if tuple(sorted(current)) != tuple(sorted(expected_selected)):
        raise ValueError("Private fallback inventory changed")


def verify_private_fallback_manifest_exact(tools: Tools, metadata: dict[str, object],
                                           record: object) -> list[dict[str, object]]:
    """Verify a fallback receipt against the exact current inventory.

    Used when several compilations share one context loop: each context's
    own targets may change the trivial selected set, so exact equality is
    checked per metadata while pin agreement is checked by the caller.
    """
    paths = private_fallback_artifact_paths(tools, metadata)
    return verify_input_manifest(record, paths, tools.output, tools)


def snapshot_input_paths(artifact_root: Path) -> tuple[str, ...]:
    if not artifact_root.is_absolute() or not artifact_root.is_dir() or artifact_root.is_symlink():
        raise ValueError("Shared snapshot artifacts need a regular directory")
    paths = []
    for path in artifact_root.rglob("*"):
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ValueError(f"Shared snapshot artifacts contain a nonregular path: {path}")
        if path.is_file():
            paths.append(str(path))
    return tuple(sorted(paths))


def verify_snapshot_inputs(record: object, artifact_root: Path, output: Path,
                           tools: Tools | None = None,
                           identities: dict[str, SourceIdentity] | None = None) -> None:
    cache = tools.file_cache if tools is not None else None
    manifest = verify_file_pin(record, output, cache)
    if (not artifact_root.resolve().is_relative_to(output.resolve()) or
            read_json(manifest).get("artifact_root") != str(artifact_root)):
        raise ValueError("Shared snapshot artifact root differs from its saved input manifest")
    paths = snapshot_input_paths(artifact_root)
    try:
        verify_input_manifest(record, paths, output, tools)
    except ValueError as error:
        raise ValueError(f"Shared snapshot artifacts changed: {error}") from error
    if (snapshot_input_paths(artifact_root) != paths or
            (identities is not None and (not set(paths).issubset(identities) or
             any(source_identity(Path(path)) != identity for path, identity in identities.items())))):
        raise ValueError("Shared snapshot artifacts changed during the snapshot")


def pin_snapshot_inputs(tools: Tools, artifact_root: Path) -> dict[str, object]:
    paths = snapshot_input_paths(artifact_root)
    value = {"artifact_root": str(artifact_root),
             "files": [file_pin(Path(path), tools.file_cache) for path in paths]}
    content = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    digest = hashlib.sha256(content).hexdigest()
    path = tools.output / "inputs" / ("snapshot-" + digest + ".json")
    if not path.exists():
        write_json(path, value)
    receipt = {"path": str(path), "bytes": len(content), "sha256": digest}
    verify_snapshot_inputs(receipt, artifact_root, tools.output, tools)
    return receipt


def private_module_components(module: str) -> tuple[str, ...]:
    """Parse a textual Lean module name into raw path components.

    Lean renders non-identifier name components escaped as `«...»`; such a
    component may itself contain dots or spaces and must stay a single path
    component (for example `A.«b.c».D` has components `A`, `b.c`, `D`).
    """
    if not module:
        raise ValueError("Private import has an invalid module name")
    components: list[str] = []
    index, length = 0, len(module)
    while index < length:
        if module[index] == "«":
            end = module.find("»", index + 1)
            if end < 0:
                raise ValueError("Private import has an invalid module name")
            component = module[index + 1:end]
            index = end + 1
        else:
            end = module.find(".", index)
            if end < 0:
                end = length
            component = module[index:end]
            if "«" in component or "»" in component or any(char.isspace() for char in component):
                raise ValueError("Private import has an invalid module name")
            index = end
        if (not component or component in (".", "..") or "/" in component or
                "\\" in component or "\0" in component):
            raise ValueError("Private import has an invalid module name")
        components.append(component)
        if index < length:
            if module[index] != ".":
                raise ValueError("Private import has an invalid module name")
            index += 1
            if index == length:
                raise ValueError("Private import has an invalid module name")
    return tuple(components)


def private_module_path(module: str) -> Path:
    return Path(*private_module_components(module))


def private_module_olean_path(module: str) -> Path:
    path = private_module_path(module)
    return path.with_name(path.name + ".olean")


def _lake_package_dir_name(name: object) -> str | None:
    if not isinstance(name, str) or not name:
        return None
    try:
        return ".".join(private_module_components(name))
    except ValueError:
        unescaped = name.replace("«", "").replace("»", "")
        return unescaped or None


def _manifest_path(root: Path, value: object) -> Path | None:
    if not isinstance(value, str) or not value:
        return None
    path = Path(value)
    return path if path.is_absolute() else root / path


def capture_lake_manifest_bytes(root: Path) -> bytes | None:
    """Identity-checked snapshot of `lake-manifest.json` under `root`.

    Production captures this *before* launching `lake env`: the
    captured `LEAN_PATH` is a function of the manifest Lake read, so
    the bytes that later authorize package roots must be pinned
    before that command runs, not at `Tools` construction after it.
    A file changing mid-read pins as missing rather than as a torn
    mixture.
    """
    manifest_path = root / "lake-manifest.json"
    try:
        before = source_identity(manifest_path)
        raw = manifest_path.read_bytes()
        return raw if source_identity(manifest_path) == before else None
    except OSError:
        return None


def verify_lake_manifest_bytes(root: Path, pinned: bytes | None) -> None:
    """Reject if the live manifest no longer matches `pinned` bytes."""
    if capture_lake_manifest_bytes(root) != pinned:
        raise ValueError(
            f"Lake manifest changed after environment capture: "
            f"{root / 'lake-manifest.json'}")


def pinned_lake_manifest_bytes(tools: Tools) -> bytes | None:
    """Lake-manifest bytes pinned for this `Tools` value.

    Production passes bytes captured before `lake env` launched
    (see `capture_lake_manifest_bytes`); other callers pin at first
    derivation in `Tools.__post_init__` (through
    `canonical_artifact_roots`). The pinned bytes are reused
    verbatim for every later trust decision on this `Tools` value.
    The live `lake-manifest.json` is never reread for authorization:
    rewriting it afterwards can neither add nor remove
    manifest-authorized artifact roots.
    """
    manifest_path = tools.root / "lake-manifest.json"
    if manifest_path in tools.lake_manifest_bytes:
        return tools.lake_manifest_bytes[manifest_path]
    pinned = capture_lake_manifest_bytes(tools.root)
    tools.lake_manifest_bytes[manifest_path] = pinned
    return pinned


def pinned_lake_manifest_input_path(tools: Tools) -> str | None:
    """Manifest path to guard as a compilation/fallback input, if any.

    Only a pinned manifest that parsed as a JSON object can have
    authorized package roots, so only then is the manifest itself a
    trust input worth pinning in input/fallback receipts and
    guarding by identity around compilation and snapshot discovery.
    Fixture roots without a (valid) manifest gain no extra input.
    """
    raw = pinned_lake_manifest_bytes(tools)
    if raw is None:
        return None
    try:
        data = json.loads(raw)
    except ValueError:
        return None
    if not isinstance(data, dict):
        return None
    return str(tools.root / "lake-manifest.json")


def verify_pinned_lake_manifest(tools: Tools) -> None:
    """Reject issuing a receipt for a manifest other than the pinned one.

    Root derivation itself stays fail-closed by parsing only pinned
    bytes, but a file receipt must never hash a post-capture rewrite
    as though it were the manifest those roots were parsed from.
    """
    verify_lake_manifest_bytes(tools.root, pinned_lake_manifest_bytes(tools))


def lake_package_artifact_roots(tools: Tools) -> set[Path]:
    """Default Lean artifact roots for packages in the Lake manifest.

    The workspace manifest is part of the pinned project inputs. Its
    package graph authorizes package directories that need not live
    under the project's default `.lake/packages`: `path` entries name
    their package directory directly (relative to the workspace
    root in the top-level manifest), while `git` entries live under
    the manifest's `packagesDir` by package directory name, with an
    optional package subdirectory. This helper only derives the
    authorized roots; `canonical_artifact_roots` still intersects
    them with the captured `LEAN_PATH`, so manifest presence alone
    never makes an unsearched directory trusted.

    The graph is parsed only from the manifest bytes pinned on
    `tools` at environment capture (`pinned_lake_manifest_bytes`),
    never from the live file. The `project_pins` hash in `run.json`
    is a run record, not the trust source; the pinned bytes are,
    and `compilation_input_paths`/`private_fallback_artifact_paths`
    additionally carry the manifest itself as a guarded receipt
    input whenever it could authorize roots.
    """
    raw = pinned_lake_manifest_bytes(tools)
    if raw is None:
        return set()
    try:
        data = json.loads(raw)
    except ValueError:
        return set()
    if not isinstance(data, dict):
        return set()
    packages_dir = _manifest_path(tools.root, data.get("packagesDir"))
    if packages_dir is None:
        packages_dir = tools.root / ".lake/packages"
    packages = data.get("packages")
    if not isinstance(packages, list):
        return set()
    roots: set[Path] = set()
    for entry in packages:
        if not isinstance(entry, dict):
            continue
        package_dir: Path | None = None
        entry_type = entry.get("type")
        if entry_type == "path":
            package_dir = _manifest_path(tools.root, entry.get("dir"))
        elif entry_type == "git":
            dir_name = _lake_package_dir_name(entry.get("name"))
            if dir_name is None:
                continue
            package_dir = packages_dir / dir_name
            sub_dir = entry.get("subDir")
            if isinstance(sub_dir, str) and sub_dir:
                package_dir = package_dir / Path(sub_dir)
        if package_dir is None:
            continue
        try:
            roots.add(fact_resolve(package_dir / ".lake/build/lib/lean"))
        except OSError:
            continue
    return roots


def canonical_artifact_roots(tools: Tools) -> list[Path]:
    """Canonical production/package artifact roots from the captured path.

    Only roots the captured Lake environment actually selected qualify:
    entries of `LEAN_PATH` that resolve to the project build root or
    to a default package artifact root authorized by the pinned Lake
    manifest/package graph. The project root is the only root accepted
    by path shape alone; every package root — including default-layout
    `.lake/packages/<name>/...` roots — must be named by the pinned
    manifest, so a stale checkout smuggled into `LEAN_PATH` is never
    trusted. The manifest arm covers Lake-selected local/path
    dependencies and custom `packagesDir` layouts whose package
    directories are not lexically under the project. If `LEAN_PATH`
    carries no
    canonical root at all (for example an offline fixture), fall back
    to the project build root alone — the project's own build output
    is always its own artifact home — and still no package enumeration.
    """
    project_root = tools.root / ".lake/build/lib/lean"
    manifest_roots = lake_package_artifact_roots(tools)
    result: list[Path] = []

    def add(path: Path) -> None:
        try:
            resolved = fact_resolve(path)
        except OSError:
            return
        if fact_is_dir(resolved) and resolved not in result:
            result.append(resolved)

    def is_canonical(path: Path) -> bool:
        try:
            resolved = fact_resolve(path)
        except OSError:
            return False
        if resolved in manifest_roots:
            return True
        try:
            parts = resolved.relative_to(tools.root).parts
        except ValueError:
            return False
        return parts == (".lake", "build", "lib", "lean")

    entries = [entry.strip() for entry in
               tools.environment.get("LEAN_PATH", "").split(os.pathsep) if entry.strip()]
    for entry in entries:
        path = Path(entry)
        if not path.is_absolute():
            path = tools.root / path
        if is_canonical(path):
            add(path)
    if not result:
        add(project_root)
    return result


def validate_captured_environment(tools: Tools) -> None:
    """Bind the captured `LEAN_PATH` to the pinned manifest graph.

    Byte checks before/after `lake env` cannot exclude a manifest
    rename/restore *during* capture: the original inode can be back
    in place while Lake read alternate bytes. The captured
    environment is therefore validated independently against the
    pinned graph. Every captured `LEAN_PATH` entry shaped like a
    default package artifact root (a `.../.lake/build/lib/lean`
    suffix, which is exactly the layout every Lake package search
    root has) must be the project root or a manifest-authorized
    root, and every manifest-authorized root that exists must
    appear in the captured `LEAN_PATH` — Lake folds every package's
    `leanLibDir` into it. Any mismatch means Lake did not read the
    pinned graph, whatever the bytes say now.
    """
    raw = pinned_lake_manifest_bytes(tools)
    if raw is None:
        return
    try:
        data = json.loads(raw)
    except ValueError:
        return
    if not isinstance(data, dict):
        return
    project_root = (tools.root / ".lake/build/lib/lean").resolve()
    authorized = lake_package_artifact_roots(tools)
    search_roots = private_search_roots(tools)
    suffix = (".lake", "build", "lib", "lean")
    for candidate in search_roots:
        if (len(candidate.parts) >= len(suffix)
                and candidate.parts[-len(suffix):] == suffix
                and candidate != project_root and candidate not in authorized):
            raise ValueError(
                "Captured LEAN_PATH names a package root outside the pinned "
                f"Lake package graph: {candidate}")
    for root_path in sorted(authorized, key=str):
        if root_path.is_dir() and root_path not in search_roots:
            raise ValueError(
                "Manifest-authorized package root missing from the captured "
                f"LEAN_PATH: {root_path}")


def private_search_roots(tools: Tools) -> list[Path]:
    """Resolved directories from the compiler's `LEAN_PATH`, in order."""
    result: list[Path] = []
    for entry in tools.environment.get("LEAN_PATH", "").split(os.pathsep):
        entry = entry.strip()
        if not entry:
            continue
        path = Path(entry)
        if not path.is_absolute():
            path = tools.root / path
        try:
            resolved = fact_resolve(path)
        except OSError:
            continue
        if resolved not in result:
            result.append(resolved)
    return result


def selected_artifact_roots(metadata: dict[str, object], root: Path,
                            targets: set[str] | None = None, *, strict: bool = False,
                            search_roots: Iterable[Path | str] = ()) -> list[str]:
    """Roots of the explicitly selected public artifacts, in setup order.

    With `strict=True`, an artifact identifies a root when its path
    ends in the module-relative `.olean` path. Multi-component paths
    do so unambiguously. A single-component (top-level) module does
    so only when its parent is an explicitly captured search root:
    without that evidence, a flat fixture artifact at the project
    root would otherwise promote an arbitrary containing directory
    to a wholesale namespace inventory. The tolerant mode retains
    flat-artifact containment only for legacy discovery callers.
    """
    explicit_search_roots = {str(fact_resolve(Path(candidate))) for candidate in search_roots}
    roots: list[str] = []
    for module, groups in cast(dict[str, list[list[str]]], metadata.get("importArts", {})).items():
        if targets is not None and module in targets:
            continue
        if not groups or not groups[0]:
            continue
        relative = private_module_olean_path(module)
        path = Path(groups[0][0])
        if not path.is_absolute():
            path = root / path
        path = fact_resolve(path)
        if (strict and len(relative.parts) <= 1 and
                str(path.parent) not in explicit_search_roots):
            continue
        parts = path.parts
        if len(parts) > len(relative.parts) and parts[-len(relative.parts):] == relative.parts:
            selected = str(path.parents[len(relative.parts) - 1])
        elif len(parts) == len(relative.parts) and parts == relative.parts:
            selected = str(path.parent)
        elif strict:
            continue
        elif targets is None:
            # Compilation-environment trust only: fixtures name flat
            # dependency files (`root/fixture-import-part`) that carry no
            # module path; trust their containing directory. Discovery
            # callers pass `targets`, and keep the strict check below.
            selected = str(path.parent)
        else:
            raise ValueError("Private import has no selected artifact root")
        if selected not in roots:
            roots.append(selected)
    return roots


def ordered_trusted_roots(tools: Tools, selected_roots: list[str]) -> list[str]:
    """The single trusted-root ordering shared by compile and discovery.

    Trusted roots named by the captured `LEAN_PATH` keep compiler
    search order. Trusted roots the search path did not name (an
    explicit offline selected root, the project-root fallback, or
    the standard library) follow in one deterministic order --
    selected roots, canonical roots, standard library -- strictly
    after the search path. `compilation_environment` and
    `private_dependency_roots` both consume this list, so compilation
    and private-closure discovery can never resolve the same module
    from different roots merely because an unlisted root's lexical
    order differs from its discovery order.
    """
    search = [str(path) for path in private_search_roots(tools)]
    rank = {str(fact_resolve(Path(root))) for root in search}
    canonical = canonical_artifact_roots(tools)
    library = standard_library_root(tools)
    trusted: set[str] = {str(fact_resolve(Path(root))) for root in selected_roots}
    for path in canonical:
        trusted.add(str(fact_resolve(path)))
    if library is not None:
        trusted.add(str(fact_resolve(library)))
    ordered: list[str] = []
    for root in search:
        if str(fact_resolve(Path(root))) in trusted and root not in ordered:
            ordered.append(root)
    extra = [root for root in selected_roots if str(fact_resolve(Path(root))) not in rank]
    extra += [str(path) for path in canonical
              if str(fact_resolve(path)) not in rank and str(path) not in extra]
    if library is not None and str(fact_resolve(library)) not in rank:
        extra.append(str(fact_resolve(library)))
    for root in extra:
        if root not in ordered:
            ordered.append(root)
    return ordered


def reject_output_nested_in_roots(tools: Tools, roots: Iterable[Path | str],
                                  *, _during_post_init: bool = False) -> None:
    """Reject any overlap between optimizer output and trusted roots.

    Lean searches each trusted root wholesale; there is no subtree
    exclusion in `LEAN_PATH`. If `--output` were nested under such a
    root, stale optimizer artifacts could be resolved by compilation
    even though inventory scans exclude them. Conversely, a trusted
    root nested beneath the output tree would be searched by
    compilation while inventory exclusion omitted its files, so
    consumed artifacts could never have been pinned. Reject both
    directions before compilation, fallback pinning, or discovery.
    """
    output = fact_resolve(tools.output)
    for root in roots:
        try:
            resolved = fact_resolve(Path(root))
        except OSError:
            continue
        if output == resolved or output.is_relative_to(resolved):
            raise ValueError(
                "Optimizer output must not be nested under a trusted artifact root: "
                f"{output} is under {resolved}")
        if resolved.is_relative_to(output):
            if _during_post_init:
                continue
            raise ValueError(
                "Trusted artifact root must not be nested under optimizer output: "
                f"{resolved} is under {output}")


def private_inventory_roots(tools: Tools, metadata: dict[str, object]) -> list[Path]:
    """Roots whose complete contents constitute a pinned inventory.

    These are the canonical/standard-library corpus plus every strict
    Lake-selected explicit artifact root. Path guards monitor all child
    changes at or under these roots; elsewhere they reject only events
    affecting a guarded path component.
    """
    roots: list[Path] = []

    def add(path: Path) -> None:
        try:
            resolved = fact_resolve(path)
        except OSError:
            return
        if resolved not in roots:
            roots.append(resolved)

    for path in canonical_artifact_roots(tools):
        add(path)
    library = standard_library_root(tools)
    if library is not None:
        add(library)
    for root in selected_artifact_roots(
            metadata, tools.root, strict=True, search_roots=private_search_roots(tools)):
        add(Path(root))
    return roots


def snapshot_private_inventory_roots(tools: Tools, value: dict[str, object]) -> list[Path]:
    """Inventory roots for every compilation context in a snapshot setup."""
    metadata_paths = {Path(str(record["path"])) for context in
                      cast(dict[str, dict[str, object]], value.get("snapshot_compilations", {})).values()
                      if isinstance(record := context.get("setup"), dict) and
                      isinstance(record.get("path"), str)}
    with guarded_inventory_components(metadata_paths, mutable_roots={tools.output}):
        roots = private_inventory_roots(tools, value)
        public_artifacts = {module: groups[0][0] for module, groups in
                            cast(dict[str, list[list[str]]], value.get("importArts", {})).items()
                            if groups and groups[0]}
        for context in cast(dict[str, dict[str, object]], value.get("snapshot_compilations", {})).values():
            setup = context.get("setup")
            if not isinstance(setup, dict) or not isinstance(setup.get("path"), str):
                continue
            path = verify_file_pin(setup, cache=tools.file_cache)
            try:
                metadata = read_json(path)
            except (OSError, ValueError):
                continue
            imports = cast(dict[str, list[list[str]]], metadata.get("importArts", {}))
            if all(not groups or not groups[0] or
                   (module in public_artifacts and public_artifacts[module] == groups[0][0])
                   for module, groups in imports.items()):
                continue
            for root in private_inventory_roots(tools, metadata):
                if root not in roots:
                    roots.append(root)
        return roots


def compilation_environment(tools: Tools, metadata: dict[str, object]) -> dict[str, str]:
    """LEAN_PATH for a forced compile: trusted pinned corpus only.

    The forced compile must not resolve a private import from an
    ambient (unpinned) root that private discovery refuses, so its
    search path is restricted to the same corpus discovery consults,
    in the shared `ordered_trusted_roots` order. Public `importArts`
    artifacts are named explicitly in the setup, so dropping ambient
    entries does not affect them.
    """
    selected = selected_artifact_roots(
        metadata, tools.root, strict=True, search_roots=private_search_roots(tools))
    ordered = ordered_trusted_roots(tools, selected)
    reject_output_nested_in_roots(tools, ordered)
    environment = dict(tools.environment)
    environment["LEAN_PATH"] = os.pathsep.join(ordered)
    return environment


def private_dependency_roots(tools: Tools, value: dict[str, object]) -> dict[str, list[str]]:
    """Candidate roots for each namespace, chunked by compiler time.

    A namespace's valid candidate set is every root pinned before the
    forced compile: the selected-namespace part of `compilation_input_paths`
    (the per-target `input_manifest`) plus the canonical fallback
    inventories (`private_fallback_manifest`). Roots outside that pinned
    corpus are ambient and are never candidates, even on `LEAN_PATH`.

    Per namespace, candidates follow `ordered_trusted_roots` -- the
    identical ordering `compilation_environment` hands the forced
    compile -- so roots named by `LEAN_PATH` keep compiler search
    order and unlisted trusted roots follow in the shared
    selected/canonical/standard-library order. Selected `importArts`
    roots are *not* promoted by being explicit; they participate only
    at their `LEAN_PATH` position, or after the whole search path
    when `LEAN_PATH` does not mention them (their compilation pin
    comes from `selected_namespace_artifact_paths`).
    Helper and verifier then choose the first candidate carrying the
    requested module's `.olean` — Lean's ordered search rule.
    """
    contexts = cast(dict[str, dict[str, object]], value["snapshot_compilations"])
    targets = {context["module"] for context in contexts.values()}
    selected_roots = selected_artifact_roots(
        value, tools.root, targets, strict=True,
        search_roots=private_search_roots(tools))
    ordered = ordered_trusted_roots(tools, selected_roots)
    reject_output_nested_in_roots(tools, ordered)
    return namespace_candidate_roots(ordered)


def namespace_candidate_roots(ordered: list[str]) -> dict[str, list[str]]:
    """Candidate artifact roots for each top-level namespace, in order."""
    roots: dict[str, list[str]] = {}
    for root in ordered:
        root_path = Path(root)
        try:
            children = sorted(root_path.iterdir())
        except OSError:
            continue
        for child in children:
            if child.is_dir():
                namespace = child.name
            elif (child.is_file() and child.name.endswith(".olean") and
                    not child.name.endswith((".olean.server", ".olean.private"))):
                namespace = child.name.removesuffix(".olean")
            else:
                continue
            if not namespace:
                continue
            candidates = roots.setdefault(namespace, [])
            if root not in candidates:
                candidates.append(root)
    return roots


def expected_private_artifacts(roots: dict[str, list[str]], module: str,
                               groups: list[list[str]]) -> list[list[str]]:
    """Artifacts `module` must use under an ordered candidate-root map."""
    relative = private_module_path(module)
    stem = Path(resolve_private_dependency_root(roots, module, relative)) / relative
    if len(groups[0]) not in (1, 3) or len(groups[1]) not in (0, 2):
        raise ValueError("Private import closure has incomplete artifact parts")
    return [[str(stem) + suffix for suffix in
             ((".olean", ".olean.server", ".olean.private") if len(groups[0]) == 3 else (".olean",))],
            [str(stem) + suffix for suffix in (".ir.sig", ".ir")] if groups[1] else []]


def resolve_private_dependency_root(roots: dict[str, list[str]], module: str,
                                    relative: Path) -> str:
    namespace = relative.parts[0]
    candidates = roots.get(namespace)
    if not candidates:
        raise ValueError("Private import has no selected artifact root")
    for root in candidates:
        if (Path(root) / private_module_olean_path(module)).is_file():
            return root
    raise ValueError("Private import has no selected artifact root")


def private_import_map(value: dict[str, object], rows: object,
                       roots: dict[str, list[str]]) -> dict[str, list[list[str]]]:
    if not isinstance(rows, list) or not rows:
        raise ValueError("Private import closure is empty or invalid")
    original = cast(dict[str, list[list[str]]], value["importArts"])
    result = deepcopy(original)
    seen: set[str] = set()
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("module"), str):
            raise ValueError("Private import closure has an invalid module row")
        module = row["module"]
        components = row.get("components")
        if components is None:
            relative = private_module_path(module)
        else:
            if (not isinstance(components, list) or not components or
                    any(not isinstance(component, str) or not component or
                        component in (".", "..") or "/" in component or
                        "\\" in component or "\0" in component
                        for component in components)):
                raise ValueError("Private import closure has an invalid module row")
            if tuple(components) != private_module_components(module):
                raise ValueError("Private import closure has inconsistent module components")
            relative = Path(*components)
        if module in seen:
            raise ValueError("Private import closure repeats a module")
        seen.add(module)
        groups = row.get("artifacts")
        if (not isinstance(groups, list) or len(groups) != 2 or
                any(not isinstance(group, list) or any(not isinstance(path, str) for path in group)
                    for group in groups)):
            raise ValueError("Private import closure has an invalid artifact map")
        if module in original:
            if groups != original[module]:
                raise ValueError("Private import closure changed an original artifact selection")
        else:
            expected = expected_private_artifacts(roots, module, cast(list[list[str]], groups))
            if groups != expected or any(Path(path).resolve() != Path(path)
                                          for group in groups for path in group):
                raise ValueError("Private import escaped its selected artifact root")
        result[module] = cast(list[list[str]], groups)
    targets = {context["module"] for context in
               cast(dict[str, dict[str, object]], value["snapshot_compilations"]).values()}
    if not targets.issubset(seen):
        raise ValueError("Private import closure omitted a requested module")
    return result


def pin_private_snapshot_data(tools: Tools, label: str, value: dict[str, object]) -> dict[str, object]:
    content = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    path = tools.output / "inputs" / (label + "-" + hashlib.sha256(content).hexdigest() + ".json")
    if not path.exists():
        write_json(path, value)
    return file_pin(path, tools.file_cache)


def missing_private_import(command: dict[str, object], value: dict[str, object]) -> bool:
    require_completion(command)
    if command["exit_code"] != 3:
        return False
    row = read_json(Path(str(command["stderr"])))
    if (row.get("kind") != "missing_private_import_artifacts" or
            not isinstance(row.get("module"), str) or
            row["module"] in cast(dict[str, object], value["importArts"]) or
            Path(str(command["stdout"])).read_text().strip()):
        raise ValueError("Snapshot returned an invalid missing-private-import receipt")
    private_module_path(row["module"])
    return True


def singleton_snapshot_value(tools: Tools, value: dict[str, object], relative: str,
                             context: dict[str, object]) -> dict[str, object]:
    """The one-context snapshot setup for a grouped context."""
    singleton_context = dict(context)
    if "artifact_root" not in singleton_context:
        module = str(context["module"])
        groups = cast(dict[str, list[list[str]]], value["importArts"])[module]
        path = Path(groups[0][0]).resolve()
        singleton_context["artifact_root"] = str(
            path.parents[len(private_module_olean_path(module).parts) - 1])
    return snapshot_setup_value(tools, Path(str(singleton_context["artifact_root"])),
                                {relative: singleton_context}, "single")


def compilation_context_pins(tools: Tools, context: dict[str, object], *,
                             exact: bool) -> dict[str, dict[str, object]]:
    """Compilation + fallback pins belonging to one snapshot context."""
    metadata = read_json(verify_file_pin(context["setup"], tools.output, tools.file_cache))
    pins: dict[str, dict[str, object]] = {}

    def add(pin: dict[str, object]) -> None:
        path = str(pin["path"])
        if path in pins and pins[path] != pin:
            raise ValueError("Snapshot private compilation inputs disagree on an artifact")
        pins[path] = pin

    for pin in verify_input_manifest(
            context["input_manifest"],
            compilation_input_paths(metadata, tools.root, standard_library_root(tools), tools),
            tools.output, tools):
        add(pin)
    fallback = context.get("private_fallback_manifest")
    if isinstance(fallback, dict):
        if exact:
            fallback_pins: object = verify_private_fallback_manifest_exact(tools, metadata, fallback)
        else:
            manifest = verify_file_pin(fallback, tools.output, tools.file_cache)
            fallback_pins = read_json(manifest).get("files")
            if (not isinstance(fallback_pins, list) or
                    any(not isinstance(pin, dict) or not isinstance(pin.get("path"), str)
                        for pin in fallback_pins)):
                raise ValueError("Snapshot private fallback inputs disagree on an artifact")
        for pin in cast(list[dict[str, object]], fallback_pins):
            add(pin)
    return pins


def verify_private_snapshot_dependencies(tools: Tools, value: dict[str, object], record: object, *,
                                         exact: bool = True) -> dict[str, list[list[str]]]:
    """Verify a private-closure receipt, fresh-exact or saved-recorded.

    With `exact=True` (fresh compile/snapshot validation) the current
    roots map and fallback inventory must still match exactly, proving
    no transient addition entered the search space after pinning.
    With `exact=False` (saved-row / resume validation) only the
    recorded roots and the discovered closure's pins are checked:
    recomputing broad fallback inventories there would let an
    unrelated new namespace or rebuilt fallback artifact invalidate a
    long-lived per-target row, contradicting resume isolation.
    """
    if not isinstance(record, dict):
        raise ValueError("Snapshot private dependency receipt is missing")
    original = verify_file_pin(record.get("original_setup"), tools.output, tools.file_cache)
    if read_json(original) != value:
        raise ValueError("Snapshot private dependencies changed the original compilation inputs")
    roots_path = verify_file_pin(record.get("roots"), tools.output, tools.file_cache)
    recorded_roots = read_json(roots_path)
    if exact:
        roots = private_dependency_roots(tools, value)
        if recorded_roots != roots:
            raise ValueError("Snapshot private dependencies changed the selected artifact roots")
    else:
        if (not isinstance(recorded_roots, dict) or
                any(not isinstance(namespace, str) or not isinstance(candidates, list) or
                    any(not isinstance(root, str) for root in candidates)
                    for namespace, candidates in recorded_roots.items())):
            raise ValueError("Snapshot private dependencies changed the selected artifact roots")
        roots = recorded_roots
    modules = [str(context["module"]) for context in
               cast(dict[str, dict[str, object]], value["snapshot_compilations"]).values()]
    helper = tools.helpers / "private_imports.lean"
    inputs = {"compiler": file_pin(tools.lean, tools.file_cache),
              "helper": file_pin(helper, tools.file_cache),
              "setup": record["original_setup"], "roots": record["roots"]}
    rows: object = None
    for phase in ("discovery", "verification"):
        evidence = record.get(phase)
        command, _ = read_analysis(tools, evidence)
        require_success(command)
        if (not isinstance(evidence, dict) or evidence.get("kind") != "private_imports" or
                evidence.get("inputs") != inputs or
                command.get("argv") != [str(tools.lean), tools.lean_thread_argument, "--run", str(helper),
                                        str(original), str(roots_path), *modules]):
            raise ValueError("Snapshot private closure command identity changed")
        output = json.loads(verify_file_pin(evidence["stdout"], tools.output, tools.file_cache).read_text())
        if phase == "verification" and output != rows:
            raise ValueError("Snapshot private import closure changed during verification")
        rows = output
    arts = private_import_map(value, rows, roots)
    context_entries = list(cast(dict[str, dict[str, object]], value["snapshot_compilations"]).items())
    context_pin_maps: list[dict[str, dict[str, object]]] = []
    all_pins: dict[str, dict[str, object]] = {}
    for _, context in context_entries:
        pins = compilation_context_pins(tools, context, exact=exact)
        context_pin_maps.append(pins)
        for path, pin in pins.items():
            if path in all_pins and all_pins[path] != pin:
                raise ValueError("Snapshot private compilation inputs disagree on an artifact")
            all_pins[path] = pin
    added_modules = arts.keys() - cast(dict[str, object], value["importArts"]).keys()
    if len(context_entries) == 1:
        for module in added_modules:
            for group in arts[module]:
                for path in group:
                    if all_pins.get(path) != file_pin(Path(path), tools.file_cache):
                        raise ValueError("Snapshot private artifact was not pinned before compilation")
    else:
        # Grouped snapshots must not pool pins across arms: each added
        # module is owned by the target whose helper traversal first
        # reached it, and that arm alone must both resolve it to the
        # merged artifacts (under its own one-context roots) and have
        # pinned those exact artifacts before its compilation.
        target_index = {module: index for index, module in enumerate(modules)}
        owner_by_module: dict[str, int] = {}
        owner: int | None = None
        for row in cast(list[dict[str, object]], rows):
            module = str(row["module"])
            if module in target_index:
                owner = target_index[module]
            if owner is not None:
                owner_by_module.setdefault(module, owner)
        singleton_roots: list[dict[str, list[str]]] = []
        singleton_originals: list[dict[str, list[list[str]]]] = []
        for relative, context in context_entries:
            singleton = singleton_snapshot_value(tools, value, relative, context)
            singleton_roots.append(private_dependency_roots(tools, singleton))
            singleton_originals.append(cast(dict[str, list[list[str]]], singleton["importArts"]))
        for module in added_modules:
            index = owner_by_module.get(module)
            if index is None:
                raise ValueError("Snapshot private artifact was not pinned before compilation")
            groups = arts[module]
            expected = singleton_originals[index].get(module) or expected_private_artifacts(
                singleton_roots[index], module, groups)
            if expected != groups:
                raise ValueError("Snapshot private dependencies changed the selected artifact roots")
            for group in groups:
                for path in group:
                    if context_pin_maps[index].get(path) != file_pin(Path(path), tools.file_cache):
                        raise ValueError("Snapshot private artifact was not pinned before compilation")
    paths = setup_input_paths({**value, "importArts": arts}, tools.root)
    verify_input_manifest(record.get("input_manifest"), paths, tools.output, tools)
    request = record.get("request")
    command, _ = read_analysis(tools, request)
    snapshot_helper = tools.helpers / ("declarations_batch.lean" if value["snapshot_kind"] == "batch"
                                      else "declarations.lean")
    if (not isinstance(request, dict) or request.get("kind") != "snapshot_unpinned" or
            request.get("inputs") != {"compiler": inputs["compiler"],
                                      "helper": file_pin(snapshot_helper, tools.file_cache),
                                      "setup": record["original_setup"]} or
            command.get("argv") != [str(tools.lean), tools.lean_thread_argument, "--run", str(snapshot_helper),
                                    str(original), *modules] or not missing_private_import(command, value)):
        raise ValueError("Snapshot private import request identity changed")
    return arts


def complete_private_snapshot_setup(tools: Tools, artifact_root: Path,
                                    setup_pin: dict[str, object], evidence: Path
                                    ) -> dict[str, object]:
    setup = verify_file_pin(setup_pin, tools.output, tools.file_cache)
    with guarded_inventory_components({setup}, mutable_roots={tools.output}):
        if verify_file_pin(setup_pin, tools.output, tools.file_cache) != setup:
            raise ValueError("Snapshot original setup receipt names a different path")
        value = read_json(setup)
        roots = private_dependency_roots(tools, value)
    roots_pin = pin_private_snapshot_data(tools, "private-roots", cast(dict[str, object], roots))
    roots_path = Path(str(roots_pin["path"]))
    helper = tools.helpers / "private_imports.lean"
    modules = [str(context["module"]) for context in
               cast(dict[str, dict[str, object]], value["snapshot_compilations"]).values()]
    inputs = {"compiler": file_pin(tools.lean, tools.file_cache),
              "helper": file_pin(helper, tools.file_cache), "setup": setup_pin, "roots": roots_pin}
    directory = evidence.parent / "private-imports"
    directory.mkdir(exist_ok=True)
    contexts = list(cast(dict[str, dict[str, object]], value["snapshot_compilations"]).items())
    context_closures: list[dict[str, object]] = []
    if len(contexts) > 1:
        # A grouped snapshot may only share one private closure when
        # every arm's own one-context closure resolves the modules it
        # reaches to the identical artifacts. Discover those closures
        # per context (under each arm's own roots) before the merged
        # discovery; a mismatch fails here and the batch caller retries
        # the arms as singletons.
        for index, (relative, context) in enumerate(contexts):
            singleton_value = singleton_snapshot_value(tools, value, relative, context)
            singleton_roots = private_dependency_roots(tools, singleton_value)
            singleton_setup_pin = pin_private_snapshot_data(
                tools, f"private-context-{index}-setup", singleton_value)
            singleton_roots_pin = pin_private_snapshot_data(
                tools, f"private-context-{index}-roots", cast(dict[str, object], singleton_roots))
            context_closures.append({
                "context": context, "value": singleton_value, "roots": singleton_roots,
                "setup": Path(str(singleton_setup_pin["path"])),
                "roots_path": Path(str(singleton_roots_pin["path"])),
                "label": directory / f"context-{index}"})
    identities = snapshot_dependency_identities(setup, tools, setup_pin=setup_pin)
    identities.update(path_component_identities(
        {helper, tools.lean, roots_path,
         *(Path(root) for candidates in roots.values() for root in candidates),
         *(cast(Path, closure["setup"]) for closure in context_closures),
         *(cast(Path, closure["roots_path"]) for closure in context_closures),
         *(Path(root) for closure in context_closures
           for candidates in cast(dict[str, list[str]], closure["roots"]).values()
           for root in candidates)},
        mutable_roots={tools.output, directory}))
    context_maps: list[dict[str, list[list[str]]]] = []
    for closure in context_closures:
        singleton_value = cast(dict[str, object], closure["value"])
        singleton_roots = cast(dict[str, list[str]], closure["roots"])
        context = cast(dict[str, object], closure["context"])
        context_argv = [str(tools.lean), tools.lean_thread_argument, "--run", str(helper),
                        str(closure["setup"]), str(closure["roots_path"]), str(context["module"])]
        with guard_path_component_moves(identities, mutable_roots={tools.output, directory},
                                        inventory_roots=snapshot_private_inventory_roots(
                                            tools, singleton_value)):
            context_discovery = tools.run(context_argv, cast(Path, closure["label"]),
                                          {**tools.environment, "LEAN_PATH": ""})
        require_success(context_discovery)
        verify_snapshot_dependencies(tools, artifact_root, setup, identities)
        context_rows = json.loads(Path(str(closure["label"]) + ".stdout").read_text())
        context_arts = private_import_map(singleton_value, context_rows, singleton_roots)
        context_pins = compilation_context_pins(tools, context, exact=True)
        for module in context_arts.keys() - cast(dict[str, object], singleton_value["importArts"]).keys():
            for group in context_arts[module]:
                for path in group:
                    if context_pins.get(path) != file_pin(Path(path), tools.file_cache):
                        raise ValueError("Snapshot private artifact was not pinned before compilation")
        context_maps.append(context_arts)
    argv = [str(tools.lean), tools.lean_thread_argument, "--run", str(helper), str(setup), str(roots_path), *modules]
    with guard_path_component_moves(identities, mutable_roots={tools.output, directory},
                                    inventory_roots=snapshot_private_inventory_roots(tools, value)):
        discovery = tools.run(argv, directory / "discovery", {**tools.environment, "LEAN_PATH": ""})
    require_success(discovery)
    verify_snapshot_dependencies(tools, artifact_root, setup, identities)
    rows = json.loads(Path(str(directory / "discovery") + ".stdout").read_text())
    arts = private_import_map(value, rows, roots)
    for context_arts in context_maps:
        for module, groups in context_arts.items():
            if arts.get(module) != groups:
                raise ValueError("Grouped private snapshot contexts resolve different private artifacts")
    paths = setup_input_paths({**value, "importArts": arts}, tools.root)
    manifest = pin_private_snapshot_data(tools, "private-inputs",
                                        {"files": [file_pin(Path(path), tools.file_cache) for path in paths]})
    identities.update(path_component_identities(
        {*(Path(path) for path in paths), Path(str(manifest["path"]))},
        mutable_roots={tools.output, directory}))
    with guard_path_component_moves(identities, mutable_roots={tools.output, directory},
                                    inventory_roots=snapshot_private_inventory_roots(tools, value)):
        verification = tools.run(argv, directory / "verification", {**tools.environment, "LEAN_PATH": ""})
    require_success(verification)
    for path, identity in identities.items():
        try:
            resolved = path.resolve()
        except OSError:
            resolved = path
        mutable = any(resolved == root.resolve() or resolved.is_relative_to(root.resolve())
                      for root in (tools.output, directory))
        actual = path_component_identity(path, mutable=mutable)
        changed = (any(actual[index] != identity[index] for index in (0, 1, 5))
                   if mutable and stat.S_ISDIR(identity[5]) else actual != identity)
        if changed:
            raise ValueError(f"Private snapshot input identity changed during verification: {path}")
    verify_input_manifest(manifest, paths, tools.output, tools)
    record = {"original_setup": setup_pin, "roots": roots_pin, "input_manifest": manifest,
              "discovery": analysis_evidence(tools, directory / "discovery", "private_imports", inputs),
              "verification": analysis_evidence(tools, directory / "verification", "private_imports", inputs),
              "request": analysis_evidence(tools, evidence, "snapshot_unpinned",
                  {"compiler": inputs["compiler"], "helper": file_pin(tools.helpers /
                    ("declarations_batch.lean" if value["snapshot_kind"] == "batch" else "declarations.lean"),
                    tools.file_cache), "setup": setup_pin})}
    verify_private_snapshot_dependencies(tools, value, record, exact=True)
    return pin_private_snapshot_data(tools, "snapshot-setup", {
        **value, "importArts": arts, "snapshot_private_dependencies": record})


def snapshot_setup_value(tools: Tools, artifact_root: Path,
                         contexts: dict[str, dict[str, object]], kind: str,
                         private_dependencies: object = None, *,
                         exact_private: bool = False) -> dict[str, object]:
    # Saved-row reconstruction (the default) validates private
    # dependencies against the recorded closure only; fresh snapshot
    # validation passes `exact_private=True`.
    if not contexts or kind not in ("single", "batch") or (kind == "single" and len(contexts) != 1):
        raise ValueError("Snapshot input has an invalid target scope")
    metadata_paths = {Path(str(record["path"])) for context in contexts.values()
                      for field in ("setup", "input_manifest", "private_fallback_manifest")
                      if isinstance(record := context.get(field), dict) and
                      isinstance(record.get("path"), str)}
    with guarded_inventory_components(metadata_paths, mutable_roots={tools.output}):
        arts: dict[str, list[list[str]]] = {}
        dynlibs: list[str] = []
        plugins: list[object] = []
        for relative, context in contexts.items():
            metadata = read_json(verify_file_pin(context.get("setup"), tools.output, tools.file_cache))
            if metadata.get("name") != context.get("module"):
                raise ValueError("Snapshot input setup has a different module")
            library = standard_library_root(tools)
            if context.get("standard_library_root") != (str(library) if library else None):
                raise ValueError("Snapshot input has a different standard library")
            files = verify_input_manifest(context.get("input_manifest"),
                compilation_input_paths(metadata, tools.root, library, tools), tools.output, tools)
            if not files:
                raise ValueError("Snapshot compilation input manifest is empty")
            for module, parts in full_import_artifacts(metadata, tools.root).items():
                canonical = [[str(fact_inventory_resolve(Path(path))) for path in group] for group in parts]
                if module in arts and arts[module] != canonical:
                    raise ValueError("Snapshot compilation inputs disagree on a dependency")
                arts[module] = canonical
            dynlibs.extend(str((Path(path) if Path(path).is_absolute() else tools.root / path).resolve())
                           for path in cast(list[str], metadata.get("dynlibs", [])))
            for original in cast(list[object], metadata.get("plugins", [])):
                path = Path(str(original["path"] if isinstance(original, dict) else original))
                canonical_path = str((path if path.is_absolute() else tools.root / path).resolve())
                plugin = {**original, "path": canonical_path} if isinstance(original, dict) else canonical_path
                if plugin not in plugins:
                    plugins.append(plugin)
        for relative, context in contexts.items():
            requested = Path(relative)
            if requested.is_absolute() or ".." in requested.parts or requested.suffix != ".lean":
                raise ValueError("Snapshot input has an invalid target path")
            metadata = read_json(verify_file_pin(context.get("setup"), tools.output, tools.file_cache))
            mode = effective_module_mode(metadata, context.get("header_is_module"))
            prefix = Path(str(context.get("artifact_root", artifact_root))) / requested.with_suffix("")
            arts[str(context["module"])] = [[str(prefix) + suffix for suffix in
                                            ((".olean", ".olean.server", ".olean.private") if mode else (".olean",))],
                                           [str(prefix) + suffix for suffix in (".ir.sig", ".ir")] if mode else []]
        value = {"name": str(next(iter(contexts.values()))["module"]), "isModule": False,
                 "importArts": arts, "dynlibs": list(dict.fromkeys(dynlibs)), "plugins": plugins, "options": {},
                 "snapshot_compilations": contexts, "snapshot_kind": kind}
        if private_dependencies is not None:
            value["importArts"] = verify_private_snapshot_dependencies(
                tools, value, private_dependencies, exact=exact_private)
            value["snapshot_private_dependencies"] = private_dependencies
        return value


def pin_snapshot_setup(tools: Tools, artifact_root: Path, rows: list[dict[str, object]],
                       compilations: dict[str, dict[str, object]], *, kind: str = "batch",
                       roots: dict[str, Path] | None = None) -> dict[str, object]:
    fields = ("setup", "header_is_module", "standard_library_root", "input_manifest",
              "private_fallback_manifest")
    contexts = {str(row["path"]): {"module": row["module"],
                **{field: compilations[str(row["path"])].get(field) for field in fields}}
                for row in rows}
    if roots is not None:
        for name, context in contexts.items():
            context["artifact_root"] = str(roots[name])
    value = snapshot_setup_value(tools, artifact_root, contexts, kind)
    content = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    path = tools.output / "inputs" / ("snapshot-setup-" + hashlib.sha256(content).hexdigest() + ".json")
    if not path.exists():
        write_json(path, value)
    receipt = {"path": str(path), "bytes": len(content), "sha256": hashlib.sha256(content).hexdigest()}
    verify_file_pin(receipt, tools.output, tools.file_cache)
    return receipt


def compatible_snapshot_group(tools: Tools, rows: list[dict[str, object]],
                              compilations: dict[str, dict[str, object]]) -> bool:
    modules = {str(row["module"]) for row in rows}
    if len(modules) != len(rows):
        return False
    arts: dict[str, list[list[str]]] = {}
    settings = None
    for row in rows:
        arm = compilations[str(row["path"])]
        setup = read_json(verify_file_pin(arm.get("setup"), tools.output, tools.file_cache))
        mode = compilation_module_mode(tools, arm)
        current = (mode, arm.get("standard_library_root"), setup.get("options", {}),
                   setup.get("dynlibs", []), setup.get("plugins", []))
        if settings is not None and settings != current:
            return False
        settings = current
        for module, parts in full_import_artifacts(setup, tools.root).items():
            canonical = [[str(Path(path).resolve()) for path in group] for group in parts]
            if module in modules or (module in arts and arts[module] != canonical):
                return False
            arts[module] = canonical
    return True


def verify_snapshot_group_member(tools: Tools, member: dict[str, object]) -> None:
    relative = Path(str(member["path"]))
    validate_manifest_row({"path": str(relative), "module": member["module"],
                           "source_sha256": cast(dict[str, object], member["source"])["sha256"],
                           "analysis_status": "pending"})
    if verify_file_pin(member["source"], cache=tools.file_cache) != source_path(tools.root, str(relative)):
        raise ValueError("Snapshot group source belongs to a different project")
    arm = cast(dict[str, object], member["compilation"])
    directory = Path(str(arm.get("source_root"))).parent
    if (not directory.resolve().is_relative_to(tools.output.resolve()) or
            arm.get("source_root") != str(directory / "source") or
            arm.get("source_path") != str(directory / "source" / relative) or
            sha256(Path(str(arm["source_path"]))) != arm.get("source_sha256")):
        raise ValueError("Snapshot group compilation source or receipt changed")
    setup = verify_file_pin(arm.get("setup"), tools.output, tools.file_cache)
    production = verify_file_pin(arm.get("setup_source"), cache=tools.file_cache)
    if (setup != directory / "setup.json" or
            production != tools.root / ".lake/build/ir" / relative.with_suffix(".setup.json") or
            arm.get("setup_root") != str(tools.root) or
            sha256(setup) != arm.get("setup_sha256") or sha256(production) != arm.get("setup_sha256")):
        raise ValueError("Snapshot group original compilation setup changed")
    metadata = read_json(setup)
    if metadata.get("name") != member["module"] or metadata.get("imports") is not None:
        raise ValueError("Snapshot group compilation module changed")
    mode = compilation_module_mode(tools, arm)
    library = standard_library_root(tools)
    if arm.get("standard_library_root") != (str(library) if library else None):
        raise ValueError("Snapshot group standard library changed")
    if not verify_input_manifest(arm.get("input_manifest"),
            compilation_input_paths(metadata, tools.root, library, tools), tools.output, tools):
        raise ValueError("Snapshot group compilation input manifest is empty")
    root = Path(str(arm["artifact_root"]))
    verify_compilation_command(tools, relative, directory, root, arm)
    if artifact_receipt(root, relative, require_c=True, is_module=mode) != arm.get("artifacts"):
        raise ValueError("Snapshot group compilation artifacts changed")
    verify_snapshot_inputs(member["snapshot_inputs"], root, tools.output, tools)


def pin_snapshot_group(tools: Tools, rows: list[dict[str, object]],
                       compilations: dict[str, dict[str, object]],
                       inputs: dict[str, dict[str, object]], directory: Path) -> dict[str, object]:
    members = []
    for row in rows:
        name = str(row["path"])
        arm = {key: deepcopy(value) for key, value in compilations[name].items()
               if not key.startswith("snapshot_")}
        source = file_pin(source_path(tools.root, name), tools.file_cache)
        if source["sha256"] != row["source_sha256"]:
            raise ValueError("Snapshot group frozen source changed")
        member = {"path": name, "module": row["module"], "source": source,
                  "compilation": arm, "snapshot_inputs": inputs[name]}
        verify_snapshot_group_member(tools, member)
        members.append(member)
    value = {"members": members, "root": str(tools.root),
             "optimizer": file_pin(Path(__file__), tools.file_cache),
             "helper": file_pin(tools.helpers / "declarations_batch.lean", tools.file_cache),
             "compiler": file_pin(tools.lean, tools.file_cache),
             "time_binary": file_pin(tools.time_binary, tools.file_cache),
             "run": file_pin(tools.output / "run.json", tools.file_cache)
                    if (tools.output / "run.json").exists() else None}
    path = directory / "snapshot-group.json"
    write_json(path, value)
    return file_pin(path, tools.file_cache)


def verify_batch_loaded_modules(snapshot: dict[str, object], modules: list[str],
                                expected_loaded: object) -> None:
    loaded = snapshot.get("loaded_modules")
    if (not isinstance(loaded, list) or any(not isinstance(module, str) for module in loaded) or
            snapshot.get("loaded_module_count") != len(loaded) or
            not set(modules).issubset(loaded) or loaded != expected_loaded):
        raise ValueError("Batch snapshot has an incomplete loaded-module receipt")


def check_saved_snapshot_group(tools: Tools, evidence: dict[str, object]) -> ValidatedSnapshotGroup:
    pin = evidence.get("snapshot_group")
    group = read_json(verify_file_pin(pin, tools.output, tools.file_cache))
    setup = verify_file_pin(evidence.get("snapshot_setup"), tools.output, tools.file_cache)
    value = read_json(setup)
    contexts = value.get("snapshot_compilations")
    if not isinstance(contexts, dict) or value.get("snapshot_kind") != "batch":
        raise ValueError("Saved snapshot compilation inputs changed")
    for field, expected in (("optimizer", Path(__file__)),
                            ("helper", tools.helpers / "declarations_batch.lean"),
                            ("compiler", tools.lean), ("time_binary", tools.time_binary)):
        if verify_file_pin(group.get(field), cache=tools.file_cache) != expected:
            raise ValueError("Saved snapshot group tool identity changed")
    if group.get("root") != str(tools.root):
        raise ValueError("Saved snapshot group belongs to a different project")
    members = group.get("members")
    if (not isinstance(members, list) or len(members) < 2 or
            any(not isinstance(member, dict) for member in members)):
        raise ValueError("Saved snapshot group member inventory is invalid")
    names = [member["path"] for member in members]
    modules = [member["module"] for member in members]
    if len(set(names)) != len(names) or len(set(modules)) != len(modules) or list(contexts) != names:
        raise ValueError("Saved snapshot group order or context inventory changed")
    run = group.get("run")
    if run is not None:
        path = verify_file_pin(run, tools.output, tools.file_cache)
        if path != tools.output / "run.json":
            raise ValueError("Saved snapshot group run identity changed")
        sources = read_json(path).get("sources")
        if not isinstance(sources, dict) or any(sources.get(member["path"]) != member["source"]["sha256"]
                                               for member in members):
            raise ValueError("Saved snapshot group differs from its frozen run")
    for member in members:
        verify_snapshot_group_member(tools, member)
        compilation = member["compilation"]
        expected = {"module": member["module"], **{field: compilation.get(field) for field in
                    ("setup", "header_is_module", "standard_library_root", "input_manifest",
                    "private_fallback_manifest", "artifact_root")}}
        if contexts[member["path"]] != expected:
            raise ValueError("Saved snapshot group compilation inputs changed")
    if not compatible_snapshot_group(tools, members,
                                    {member["path"]: member["compilation"] for member in members}):
        raise ValueError("Saved snapshot group original inputs conflict")
    if snapshot_setup_value(tools, Path(members[0]["compilation"]["artifact_root"]),
                            contexts, "batch", value.get("snapshot_private_dependencies")) != value:
        raise ValueError("Saved snapshot compilation inputs changed")
    dependencies = evidence.get("snapshot_dependencies")
    if not isinstance(dependencies, list) or len(dependencies) != len(members):
        raise ValueError("Saved snapshot group dependency receipts are incomplete")
    directory = Path(str(cast(dict[str, object], pin)["path"])).parent
    for index, (member, dependency) in enumerate(zip(members, dependencies)):
        command, _ = read_analysis(tools, dependency)
        require_success(command)
        scratch = directory / f"resolve-{index}.lean"
        if (dependency.get("kind") != "deps" or
                command.get("argv") != [str(tools.lean), tools.lean_thread_argument, "--deps", str(scratch)] or
                scratch.read_text() != f"import all {member['module']}\n" or
                str(Path(member["compilation"]["artifact_root"]) / Path(member["path"]).with_suffix(".olean"))
                not in Path(command["stdout"]).read_text().splitlines()):
            raise ValueError("Saved snapshot group dependency resolution changed")
    snapshot_evidence = evidence.get("snapshot_command_evidence")
    command, _ = read_analysis(tools, snapshot_evidence)
    require_success(command)
    if (not isinstance(snapshot_evidence, dict) or snapshot_evidence.get("kind") != "snapshot" or
            command.get("argv") != [str(tools.lean), tools.lean_thread_argument, "--run",
                                    str(tools.helpers / "declarations_batch.lean"), str(setup), *modules]):
        raise ValueError("Saved shared snapshot command identity changed")
    records = [json.loads(line) for line in Path(command["stdout"]).read_text().splitlines() if line]
    if (len(records) != len(modules) or any(not isinstance(record, dict) for record in records) or
            [record.get("module") for record in records] != modules or
            any(record.get("loaded_modules_scope") != "whole_batch" or
                record.get("batch_modules") != modules or record.get("batch_module_count") != len(modules)
                for record in records)):
        raise ValueError("Saved shared snapshot output differs from its command")
    for record in records:
        verify_batch_loaded_modules(record, modules, records[0].get("loaded_modules"))
        verify_private_loaded_modules(record, value)
    return ValidatedSnapshotGroup(deepcopy(evidence), {member["path"]: member for member in members},
                                  {record["module"]: record for record in records})


def verify_saved_snapshot_group(tools: Tools, arm: dict[str, object], relative: Path,
                                snapshot: dict[str, object]) -> None:
    evidence = {field: arm.get(field) for field in ("snapshot_group", "snapshot_setup",
                                                  "snapshot_dependencies", "snapshot_command_evidence")}
    path = verify_file_pin(evidence["snapshot_group"], tools.output, tools.file_cache)
    verify_file_pin(evidence["snapshot_setup"], tools.output, tools.file_cache)
    cached = tools.validated_snapshot_groups.get("phase")
    checked = next((record for record in cached.get(str(path), []) if record.evidence == evidence),
                   None) if cached is not None else None
    if checked is None:
        checked = check_saved_snapshot_group(tools, evidence)
        if cached is not None:
            cached.setdefault(str(path), []).append(checked)
    member = checked.members.get(str(relative))
    if (member is None or
            {key: value for key, value in arm.items() if not key.startswith("snapshot_")} != member["compilation"] or
            arm.get("snapshot_input_manifest") != member["snapshot_inputs"]):
        raise ValueError("Saved snapshot group lost its original compilation")
    if checked.snapshots[member["module"]] != snapshot:
        raise ValueError("Saved shared snapshot output differs from its command")


def path_component_identity(path: Path, *, strict: bool = False,
                            mutable: bool = False) -> SourceIdentity:
    info = path.lstat()
    if stat.S_ISDIR(info.st_mode) and not strict and (sys.platform == "linux" or mutable):
        # Linux guards directory children with inotify, and mutable
        # optimizer-output directories necessarily receive receipt
        # writes during guarded commands. For those directories the
        # component identity is the directory node, not its child-list
        # timestamps. Immutable inventory directories retain strict
        # `source_identity` custody separately.
        return (info.st_dev, info.st_ino, 0, 0, 0, info.st_mode)
    return (info.st_dev, info.st_ino, info.st_ctime_ns, info.st_mtime_ns, info.st_size, info.st_mode)


def path_component_identities(paths: set[Path],
                              mutable_roots: Iterable[Path] = ()) -> dict[Path, SourceIdentity]:
    mutable = tuple(resolve_inventory_path(root) for root in mutable_roots)
    for path in tuple(paths):
        paths.add(resolve_inventory_path(path))
    for path in tuple(paths):
        paths.update(path.parents)

    if sys.platform == "linux":
        return {path: path_component_identity(path) for path in paths}

    def is_mutable(path: Path) -> bool:
        try:
            resolved = resolve_inventory_path(path)
        except OSError:
            resolved = path
        return any(resolved == root or resolved.is_relative_to(root) for root in mutable)

    return {path: path_component_identity(path, mutable=is_mutable(path)) for path in paths}


@contextmanager
def guard_path_component_moves(identities: dict[Path, SourceIdentity],
                               mutable_roots: Iterable[Path] = (),
                               inventory_roots: Iterable[Path] = (),
                               child_names: dict[Path, set[str]] | None = None) -> Iterator[None]:
    """Reject transient directory changes, using strict stamps for unreadable directories.

    Child create/delete/move events are monitored only for immutable
    input directories. Directories at or under `mutable_roots` (the
    optimizer's own output/evidence tree, where `Tools.run`
    necessarily creates command receipts, stdout/stderr, timing and
    snapshot evidence during the guarded command) keep the
    self-move/attribute guards but not child monitoring, so the
    guard never rejects the optimizer's own writes. Outside
    `inventory_roots` -- directories whose complete contents
    constitute a pinned inventory and where every child event
    rejects -- a child event rejects only when its name is the next
    component of a guarded path, or one `child_names` lists for that
    directory (a path that must stay absent), so unrelated sibling
    activity beside the project or input tree does not abort
    compilation/snapshots.
    """
    if sys.platform != "linux":
        yield
        return
    mutable = tuple(root.resolve() for root in mutable_roots)
    inventory = tuple(root.resolve() for root in inventory_roots)

    def is_mutable(path: Path) -> bool:
        if not mutable:
            return False
        try:
            resolved = path.resolve()
        except OSError:
            resolved = path
        return any(resolved == root or resolved.is_relative_to(root) for root in mutable)

    def is_inventory(path: Path) -> bool:
        if not inventory:
            return False
        try:
            resolved = path.resolve()
        except OSError:
            resolved = path
        return any(resolved == root or resolved.is_relative_to(root) for root in inventory)

    relevant_children: dict[Path, set[str]] = {}
    visited: set[Path] = set()
    for guarded in identities:
        child = guarded
        while child not in visited:
            visited.add(child)
            parent = child.parent
            if parent == child:
                break
            if parent in identities:
                relevant_children.setdefault(parent, set()).add(child.name)
            child = parent
    for directory, names in (child_names or {}).items():
        relevant_children.setdefault(directory, set()).update(names)
    libc = ctypes.CDLL(None, use_errno=True)
    try:
        initialize, add_watch = libc.inotify_init1, libc.inotify_add_watch
    except AttributeError as error:
        raise ValueError("Compiler input path guards require Linux inotify") from error
    initialize.argtypes, initialize.restype = [ctypes.c_int], ctypes.c_int
    add_watch.argtypes, add_watch.restype = [ctypes.c_int, ctypes.c_char_p, ctypes.c_uint32], ctypes.c_int
    attribute, delete_self, move_self, unmount, overflow, ignored = 0x4, 0x400, 0x800, 0x2000, 0x4000, 0x8000
    child_create, child_delete, child_moved_from, child_moved_to = 0x100, 0x200, 0x40, 0x80
    only_directory, dont_follow = 0x01000000, 0x02000000
    descriptor = initialize(os.O_CLOEXEC | os.O_NONBLOCK)
    if descriptor < 0:
        raise OSError(ctypes.get_errno(), "Cannot monitor compiler input directories")
    try:
        watched = {}
        child_watched = set()
        strict_identities = {}
        for path, identity in identities.items():
            if stat.S_ISDIR(identity[5]):
                child_mask = (0 if is_mutable(path) else
                              child_create | child_delete | child_moved_from | child_moved_to)
                watch = add_watch(descriptor, os.fsencode(path),
                                  attribute | delete_self | move_self | child_mask |
                                  only_directory | dont_follow)
                if watch < 0:
                    error = ctypes.get_errno()
                    if error != errno.EACCES:
                        raise OSError(error, "Cannot monitor compiler input directory", str(path))
                    strict_identities[path] = path_component_identity(path, strict=True)
                    continue
                watched[watch] = path
                if child_mask:
                    child_watched.add(watch)
        for path, expected in identities.items():
            if path_component_identity(path) != expected:
                raise ValueError(f"Compiler input path identity changed: {path}")
        for path, expected in strict_identities.items():
            if path_component_identity(path, strict=True) != expected:
                raise ValueError(f"Compiler input path identity changed: {path}")
        yield
        for path, expected in strict_identities.items():
            if path_component_identity(path, strict=True) != expected:
                raise ValueError(f"Compilation input path identity changed: {path}")
        while True:
            try:
                events = os.read(descriptor, 65536)
            except BlockingIOError:
                break
            if not events:
                raise ValueError("Compiler input directory event stream closed")
            offset = 0
            while offset < len(events):
                watch, mask, _, length = struct.unpack_from("iIII", events, offset)
                raw_name = events[offset + 16:offset + 16 + length].split(b"\0", 1)[0]
                name = os.fsdecode(raw_name) if raw_name else ""
                offset += 16 + length
                if mask & overflow:
                    raise ValueError("Compiler input directory event stream overflowed")
                watched_path = watched.get(watch)
                child_relevant = False
                if watch in child_watched and mask & (
                        child_create | child_delete | child_moved_from | child_moved_to):
                    child_relevant = (watched_path is None or not name or
                                      is_inventory(watched_path) or
                                      name in relevant_children.get(watched_path, set()))
                if (mask & (delete_self | move_self | unmount | ignored) or child_relevant or
                        (mask & attribute and length == 0)):
                    raise ValueError(f"Compilation input path identity changed: {watched_path} "
                                     "(directory attributes changed, moved or disappeared)")
    finally:
        os.close(descriptor)


@contextmanager
def guard_ancestor_moves(identities: dict[Path, SourceIdentity]) -> Iterator[set[Path]]:
    """Watch ancestor nodes without treating unrelated child writes as changes."""
    if not hasattr(select, "kqueue"):
        yield set()
        return
    try:
        queue = select.kqueue()
    except OSError as error:
        if error.errno not in {errno.EMFILE, errno.ENFILE}:
            raise
        yield set()
        return
    descriptors: dict[int, Path] = {}
    watched: set[Path] = set()
    notes = select.KQ_NOTE_RENAME | select.KQ_NOTE_DELETE | select.KQ_NOTE_ATTRIB | select.KQ_NOTE_REVOKE
    try:
        changes = []
        for path, identity in identities.items():
            if not stat.S_ISDIR(identity[5]):
                continue
            try:
                descriptor = os.open(path, getattr(os, "O_EVTONLY", os.O_RDONLY) |
                                     os.O_CLOEXEC | os.O_NOFOLLOW)
            except OSError as error:
                if error.errno not in {errno.EACCES, errno.EPERM, errno.EMFILE, errno.ENFILE}:
                    raise
                if error.errno in {errno.EMFILE, errno.ENFILE}:
                    for opened_descriptor in descriptors:
                        os.close(opened_descriptor)
                    descriptors.clear()
                    watched.clear()
                    changes.clear()
                    queue.close()
                    queue = None
                    break
                continue
            descriptors[descriptor] = path
            opened = os.fstat(descriptor)
            if (opened.st_dev, opened.st_ino, opened.st_mode) != (identity[0], identity[1], identity[5]):
                raise ValueError(f"Snapshot collection input path identity changed: {path}")
            changes.append(select.kevent(descriptor, filter=select.KQ_FILTER_VNODE,
                                         flags=select.KQ_EV_ADD | select.KQ_EV_CLEAR, fflags=notes))
            watched.add(path)
        if queue is not None and changes:
            queue.control(changes, 0, 0)
        for path, expected in identities.items():
            if path_component_identity(path, strict=True) != expected:
                raise ValueError(f"Snapshot collection input path identity changed: {path}")
        yield watched
        while descriptors:
            events = queue.control(None, len(descriptors), 0)
            if not events:
                break
            for event in events:
                if event.flags & (select.KQ_EV_ERROR | select.KQ_EV_EOF) or event.fflags & notes:
                    raise ValueError("Snapshot collection input path identity changed: "
                                     f"{descriptors.get(event.ident)} (ancestor moved or changed)")
    finally:
        if queue is not None:
            queue.close()
        for descriptor in descriptors:
            os.close(descriptor)


def resolution_component_identities(path: Path) -> tuple[Path, dict[Path, SourceIdentity]]:
    """Resolve a path while retaining every traversed component and symlink."""
    pending = list(path.absolute().parts[1:])
    current = Path(path.absolute().anchor)
    identities = {current: path_component_identity(current, strict=True)}
    links = 0
    while pending:
        part = pending.pop(0)
        if part in {"", "."}:
            continue
        if part == "..":
            current = current.parent
            continue
        component = current / part
        identity = path_component_identity(component, strict=True)
        if identities.setdefault(component, identity) != identity:
            raise ValueError(f"Snapshot collection input path identity changed: {component}")
        if stat.S_ISLNK(identity[5]):
            links += 1
            if links > 40:
                raise ValueError(f"Snapshot collection input path has too many symlinks: {path}")
            target = Path(os.readlink(component))
            if path_component_identity(component, strict=True) != identity:
                raise ValueError(f"Snapshot collection input path identity changed: {component}")
            if target.is_absolute():
                current = Path(target.anchor)
                pending = list(target.parts[1:]) + pending
            else:
                pending = list(target.parts) + pending
        else:
            current = component
    return current, identities


@contextmanager
def guarded_inventory_components(paths: set[Path], mutable_roots: Iterable[Path] = (),
                                 inventory_roots: Iterable[Path] = ()) -> Iterator[None]:
    if sys.platform != "linux":
        # Metadata reads still require path custody on platforms without
        # inotify. File stamps detect replaced-and-restored setup/manifest
        # bytes. Input and inventory directories retain strict stamps. Native
        # ancestor watches allow unrelated sibling writes while rejecting moves.
        lexical_inventories = set(inventory_roots)
        lexical_mutable = {path for path in mutable_roots if path.exists() or path.is_symlink()}
        lexical_inputs = set(paths) | lexical_inventories
        lexical_components = lexical_inputs | lexical_mutable
        for path in tuple(lexical_components):
            lexical_components.update(path.parents)
        lexical = {path: path_component_identity(path) for path in lexical_components}
        with guard_ancestor_moves(lexical) as lexical_watched:
            lexical_relaxed = lexical_watched - lexical_inputs
            lexical_guarded = {
                path: path_component_identity(path, mutable=path in lexical_relaxed)
                for path in lexical_components}
            resolved = {}
            traversed: dict[Path, SourceIdentity] = {}
            for path in lexical_inputs | lexical_mutable:
                target, identities = resolution_component_identities(path)
                resolved[path] = target
                for component, identity in identities.items():
                    if traversed.setdefault(component, identity) != identity:
                        raise ValueError(f"Snapshot collection input path identity changed: {component}")
            for path, expected in lexical_guarded.items():
                if path_component_identity(path, mutable=path in lexical_relaxed) != expected:
                    raise ValueError(f"Snapshot collection input path identity changed: {path}")
            inventories = lexical_inventories | {resolved[path] for path in lexical_inventories}
            inputs = lexical_inputs | {resolved[path] for path in lexical_inputs}
            mutable = tuple(resolved[path] for path in lexical_mutable)
            components = set(inputs) | traversed.keys()
            for path in inputs:
                components.update(path.parents)
            node_only = {path for path in inputs if path not in inventories and
                         any(resolved.get(path, path).is_relative_to(root) for root in mutable)}
            ancestors = {path: path_component_identity(path)
                         for path in components - inputs | node_only}
            with guard_ancestor_moves(ancestors) as watched:
                relaxed = (lexical_watched | watched) & (components - inputs | node_only)
                for path in node_only & lexical_watched:
                    lexical_relaxed.add(path)
                    lexical_guarded[path] = path_component_identity(path, mutable=True)
                guarded = {path: path_component_identity(path, mutable=path in relaxed)
                           for path in components}
                for path, expected in traversed.items():
                    identity = guarded[path]
                    if path in relaxed and stat.S_ISDIR(expected[5]):
                        expected = (expected[0], expected[1], 0, 0, 0, expected[5])
                    if identity != expected:
                        raise ValueError(f"Snapshot collection input path identity changed: {path}")

                def verify_components() -> None:
                    for path, expected in guarded.items():
                        if path_component_identity(path, mutable=path in relaxed) != expected:
                            raise ValueError(f"Snapshot collection input path identity changed: {path}")

                def verify_resolution() -> None:
                    for path, target in resolved.items():
                        if path.resolve() != target:
                            raise ValueError(f"Snapshot collection input path identity changed: {path}")

                # Both lexical and canonical ancestors are now watched. Reject
                # a target selected before those watches were armed, and check
                # that resolving it did not mutate any guarded component.
                verify_resolution()
                verify_components()
                yield
                verify_resolution()
                verify_components()
            for path, expected in lexical_guarded.items():
                if path_component_identity(path, mutable=path in lexical_relaxed) != expected:
                    raise ValueError(f"Snapshot collection input path identity changed: {path}")
        return
    mutable, inventory = tuple(mutable_roots), tuple(inventory_roots)
    components: set[Path] = set()
    for path in paths | set(inventory):
        while path not in components:
            components.add(path)
            parent = path.parent
            if parent == path:
                break
            path = parent
    identities = {path: path_component_identity(path) for path in components}
    with guard_path_component_moves(identities, mutable_roots=mutable, inventory_roots=inventory):
        canonical: set[Path] = set()
        for path in sorted(identities, key=lambda path: len(path.parts)):
            if (path.anchor == "/" and ".." not in path.parts and
                    not stat.S_ISLNK(identities[path][5]) and
                    (path.parent == path or path.parent in canonical)):
                canonical.add(path)
        # Enclosing guards stay armed until this one exits, so their
        # canonical paths remain proven here as well.
        token = _guarded_inventory_canonical_paths.set(
            frozenset(canonical) | _guarded_inventory_canonical_paths.get())
        try:
            yield
            for path, expected in identities.items():
                if path_component_identity(path) != expected:
                    raise ValueError(f"Snapshot collection input path identity changed: {path}")
        finally:
            _guarded_inventory_canonical_paths.reset(token)


def snapshot_dependency_identities(setup: Path, tools: Tools | None = None, *,
                                  setup_pin: dict[str, object]) -> dict[Path, SourceIdentity]:
    with guarded_inventory_components({setup}, mutable_roots={tools.output} if tools is not None else ()):
        if verify_file_pin(setup_pin, cache=tools.file_cache if tools is not None else None) != setup:
            raise ValueError("Snapshot setup receipt names a different path")
        value = read_json(setup)
        metadata_paths = {Path(str(record["path"])) for context in
                          cast(dict[str, dict[str, object]], value["snapshot_compilations"]).values()
                          for field in ("setup", "input_manifest", "private_fallback_manifest")
                          if isinstance(record := context.get(field), dict) and
                          isinstance(record.get("path"), str)}
        with guarded_inventory_components(metadata_paths,
                                          mutable_roots={tools.output} if tools is not None else ()):
            paths = {setup, *(Path(path) for path in setup_input_paths(value, setup.parent))}
            for context in cast(dict[str, dict[str, object]], value["snapshot_compilations"]).values():
                for field in ("setup", "input_manifest", "private_fallback_manifest"):
                    if not isinstance(context.get(field), dict):
                        continue
                    record = cast(dict[str, object], context[field])
                    path = verify_file_pin(record, cache=tools.file_cache if tools is not None else None)
                    paths.add(path)
                    if field in ("input_manifest", "private_fallback_manifest"):
                        # Fresh snapshot guards cover every artifact the fallback
                        # receipt makes discoverable. These identities are transient
                        # (never saved as per-target resume inputs), so unrelated
                        # fallback rebuilds still cannot invalidate a saved row.
                        paths.update(Path(str(row["path"])) for row in cast(list[dict[str, object]], read_json(path)["files"]))
            private = value.get("snapshot_private_dependencies")
            if isinstance(private, dict):
                paths.update(Path(str(private[field]["path"])) for field in
                             ("original_setup", "roots", "input_manifest"))
                for phase in ("discovery", "verification", "request"):
                    record = private[phase]
                    paths.update(Path(str(record[suffix]["path"])) for suffix in ("json", "stdout", "stderr"))
                    paths.update(Path(str(pin["path"])) for pin in record["inputs"].values())
            if tools is None:
                return path_component_identities(paths)
            inventory_roots = snapshot_private_inventory_roots(tools, value)
            with guarded_inventory_components(paths, mutable_roots={tools.output}, inventory_roots=inventory_roots):
                # Scan each context's fallback inventory so empty namespace
                # directories and trusted inventory roots are cached and can
                # join the guarded components; manifest file rows alone never
                # name fileless directories or fileless roots.
                for context in cast(dict[str, dict[str, object]], value["snapshot_compilations"]).values():
                    record = context.get("setup")
                    if isinstance(record, dict):
                        metadata = read_json(verify_file_pin(record, cache=tools.file_cache))
                        private_fallback_artifact_paths(tools, metadata)
                paths.update(cached_empty_inventory_directories(tools))
                paths.update(inventory_roots)
                return path_component_identities(paths, mutable_roots={tools.output})


@contextmanager
def guarded_snapshot_metadata(tools: Tools, setup: Path,
                              identities: dict[Path, SourceIdentity]) -> Iterator[dict[str, object]]:
    with guarded_inventory_components({setup}, mutable_roots={tools.output}):
        if setup not in identities or path_component_identity(setup) != identities[setup]:
            raise ValueError(f"Snapshot input identity changed: {setup}")
        value = read_json(setup)
        contexts = cast(dict[str, dict[str, object]], value["snapshot_compilations"])
        paths = {Path(str(record["path"])) for context in contexts.values()
                 if isinstance(record := context.get("setup"), dict) and
                 isinstance(record.get("path"), str)}
        with guarded_inventory_components(paths, mutable_roots={tools.output}):
            yield value


def verify_snapshot_dependencies(tools: Tools, artifact_root: Path, setup: Path,
                                 identities: dict[Path, SourceIdentity]) -> None:
    # A post-command check: inside a phase it reuses recorded derivations
    # only after re-reading their facts in a new window; the identity sweep
    # below stays whole.
    new_prepared_window(tools)
    with using_prepared_inputs(tools), guarded_snapshot_metadata(tools, setup, identities) as value:
        inventory_roots = snapshot_private_inventory_roots(tools, value)
        with guarded_inventory_components(set(identities), mutable_roots={tools.output}, inventory_roots=inventory_roots):
            output = resolve_inventory_path(tools.output)
            for path, expected in identities.items():
                if sys.platform == "linux" and (
                        not stat.S_ISDIR(expected[5]) or expected[2:5] == (0, 0, 0)):
                    changed = path_component_identity(path) != expected
                else:
                    try:
                        resolved = resolve_inventory_path(path)
                    except OSError:
                        resolved = path
                    mutable = resolved == output or resolved.is_relative_to(output)
                    actual = path_component_identity(path, mutable=mutable)
                    if mutable and stat.S_ISDIR(expected[5]):
                        changed = any(actual[index] != expected[index] for index in (0, 1, 5))
                    else:
                        changed = actual != expected
                if changed:
                    raise ValueError(f"Snapshot input identity changed: {path}")
            value = read_json(setup)
            if snapshot_setup_value(tools, artifact_root, cast(dict[str, dict[str, object]], value["snapshot_compilations"]),
                                    str(value.get("snapshot_kind")), value.get("snapshot_private_dependencies"),
                                    exact_private=True) != value:
                raise ValueError("Snapshot input setup changed")


def verify_private_loaded_modules(snapshot: dict[str, object], value: dict[str, object]) -> None:
    if value.get("snapshot_private_dependencies") is None:
        return
    loaded = snapshot.get("loaded_modules")
    if (not isinstance(loaded, list) or any(not isinstance(module, str) for module in loaded) or
            snapshot.get("loaded_module_count") != len(loaded) or
            not set(loaded).issubset(cast(dict[str, object], value["importArts"]))):
        raise ValueError("Snapshot loaded a module outside its pinned private dependency map")
    targets = {str(context["module"]) for context in
               cast(dict[str, dict[str, object]], value["snapshot_compilations"]).values()}
    if not targets.issubset(loaded):
        raise ValueError("Snapshot omitted a requested module from its loaded-module receipt")


def compilation_argv(tools: Tools, relative: Path, directory: Path,
                     artifact_root: Path) -> list[str]:
    prefix = artifact_root / relative.with_suffix("")
    source_root = directory / "source"
    return [str(tools.time_binary), "-f",
            '{"wall_seconds":%e,"user_seconds":%U,"system_seconds":%S,"max_rss_kib":%M}',
            "-o", str(directory / "time.json"), str(tools.lean), tools.lean_thread_argument, "-R", str(source_root),
            str(source_root / relative), "--setup", str(directory / "setup.json"),
            "-o", str(prefix) + ".olean", "-i", str(prefix) + ".ilean", "-c", str(prefix) + ".c"]


def verify_compilation_command(tools: Tools, relative: Path, directory: Path,
                               artifact_root: Path, compilation: dict[str, object]) -> None:
    evidence = compilation.get("command_evidence")
    if not isinstance(evidence, dict) or evidence.get("kind") != "compile":
        raise ValueError("Saved compilation command evidence is missing")
    inputs = evidence.get("inputs")
    executables = {"compiler": tools.lean, "time_binary": tools.time_binary}
    if not isinstance(inputs, dict) or inputs.keys() != executables.keys():
        raise ValueError("Saved compilation executable identities are missing")
    for key, executable in executables.items():
        if verify_file_pin(inputs[key], cache=tools.file_cache) != executable:
            raise ValueError("Saved compilation resolved a different executable")
    for suffix in ("json", "stdout", "stderr"):
        path = verify_file_pin(evidence.get(suffix), tools.output, tools.file_cache)
        if path != directory / ("compile." + suffix):
            raise ValueError("Saved compilation command evidence belongs to a different arm")
    command = read_json(directory / "compile.json")
    require_success(command)
    if (command != compilation.get("command") or
            command.get("argv") != compilation_argv(tools, relative, directory, artifact_root) or
            command.get("cwd") != str(tools.root) or
            any(command.get(suffix) != str(directory / ("compile." + suffix))
                for suffix in ("stdout", "stderr"))):
        raise ValueError("Saved compilation command invocation changed")


def compile_arm(tools: Tools, relative: Path, setup: Path, directory: Path,
                artifact_root: Path | None = None,
                source_bytes: bytes | None = None, *,
                header_is_module: bool = True) -> dict[str, object]:
    artifacts = directory / "artifacts" if artifact_root is None else artifact_root
    prefix = artifacts / relative.with_suffix("")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    source_root = directory / "source"
    source = source_root / relative
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(source_path(tools.root, str(relative)).read_bytes()
                       if source_bytes is None else source_bytes)
    source_hash = sha256(source)
    setup_receipt = file_pin(setup, tools.file_cache)
    saved_setup = directory / "setup.json"
    saved_setup.write_bytes(setup.read_bytes())
    setup_copy = file_pin(saved_setup, tools.file_cache)
    if setup_copy["sha256"] != setup_receipt["sha256"]:
        raise ValueError("Production setup changed while saving its compilation copy")
    metadata = read_json(saved_setup)
    is_module = effective_module_mode(metadata, header_is_module)
    library = standard_library_root(tools)
    # Capture fallback identities before pinning writes any receipt under
    # the output tree, so receipt creation cannot trip its own guard.
    fallback_paths = private_fallback_artifact_paths(tools, metadata)
    fallback_identities = {path: source_identity(Path(path)) for path in fallback_paths}
    input_manifest = pin_setup_inputs(tools, metadata)
    fallback_manifest = pin_private_fallback_inputs(tools, metadata)
    input_paths = compilation_input_paths(metadata, tools.root, library, tools)
    # The fallback inventory is not a per-target resume input, but its
    # artifacts are loadable through LEAN_PATH by this compilation, so
    # they still need pre/post identity and path-component guarding: a
    # transient rewrite+restore during compilation must not let the
    # snapshot consume different bytes from compilation.
    input_identities = {path: source_identity(Path(path)) for path in input_paths}
    source_identities = {path: source_identity(path) for path in (source, setup, saved_setup)}
    executables = {"compiler": file_pin(tools.lean, tools.file_cache),
                   "time_binary": file_pin(tools.time_binary, tools.file_cache)}
    timing = directory / "time.json"
    for suffix in ARTIFACT_SUFFIXES:
        Path(str(prefix) + suffix).unlink(missing_ok=True)
    timing.unlink(missing_ok=True)
    (directory / "compile-receipt.json").unlink(missing_ok=True)
    component_paths = {*(Path(path) for path in input_paths),
                       *(Path(path) for path in fallback_paths), source, setup, saved_setup,
                       Path(str(input_manifest["path"])), Path(str(fallback_manifest["path"])),
                       tools.lean, tools.time_binary}
    if library is not None:
        component_paths.add(library)
    component_paths.update(cached_empty_inventory_directories(tools))
    # `inventory_roots=` below only classifies already-watched paths;
    # add every trusted root itself so even a fileless root receives a
    # child-event watch / guarded identity.
    component_paths.update(private_inventory_roots(tools, metadata))
    component_identities = path_component_identities(
        component_paths, mutable_roots={tools.output, directory, artifacts})
    mutable_roots = tuple(root.resolve() for root in (tools.output, directory, artifacts))
    with guard_path_component_moves(component_identities,
                                    mutable_roots={tools.output, directory, artifacts},
                                    inventory_roots=private_inventory_roots(tools, metadata)):
        command = tools.run(compilation_argv(tools, relative, directory, artifacts),
                            directory / "compile", compilation_environment(tools, metadata))
    require_success(command)
    if (sha256(source) != source_hash or file_pin(setup, tools.file_cache) != setup_receipt or
            file_pin(saved_setup, tools.file_cache) != setup_copy or
            any(source_identity(path) != identity for path, identity in source_identities.items())):
        raise ValueError("Isolated source or production setup changed during compilation")
    if any(source_identity(Path(path)) != identity for path, identity in input_identities.items()):
        raise ValueError("Compilation input changed during compilation")
    if any(source_identity(Path(path)) != identity for path, identity in fallback_identities.items()):
        raise ValueError("Private fallback input changed during compilation")
    for path, expected in component_identities.items():
        try:
            resolved = path.resolve()
        except OSError:
            resolved = path
        mutable = any(resolved == root or resolved.is_relative_to(root)
                      for root in mutable_roots)
        actual = path_component_identity(path, mutable=mutable)
        fields = (0, 1, 5) if mutable and stat.S_ISDIR(expected[5]) else range(6)
        if any(actual[index] != expected[index] for index in fields):
            raise ValueError(f"Compilation input path identity changed: {path}")
    verify_input_manifest(input_manifest, input_paths, tools.output, tools)
    verify_input_manifest(fallback_manifest, fallback_paths, tools.output, tools)
    verify_private_fallback_inventory(tools, metadata, fallback_paths)
    for receipt in executables.values():
        verify_file_pin(receipt, cache=tools.file_cache)
    result: dict[str, object] = {
        "command": command,
        "time": json.loads(timing.read_text().splitlines()[-1]),
        "artifacts": artifact_receipt(artifacts, relative, require_c=True, is_module=is_module),
        "artifact_root": str(artifacts),
        "source_root": str(source_root), "source_path": str(source),
        "header_is_module": header_is_module,
        "source_sha256": source_hash, "setup_sha256": setup_receipt["sha256"],
        "setup": setup_copy, "setup_source": setup_receipt, "setup_root": str(tools.root),
        "standard_library_root": str(library) if library is not None else None,
        "input_manifest": input_manifest,
        "private_fallback_manifest": fallback_manifest,
    }
    result["command_evidence"] = analysis_evidence(tools, directory / "compile", "compile", executables)
    write_json(directory / "compile-receipt.json", result)
    return result


def snapshot_arm(tools: Tools, module: str, relative: Path,
                 directory: Path, compilation: dict[str, object]) -> dict[str, object]:
    artifacts = directory / "artifacts"
    evidence = directory / "snapshot-evidence"
    evidence.mkdir(exist_ok=True)
    if evidence.is_symlink():
        raise ValueError("Snapshot evidence needs a regular directory")
    scratch = directory / "resolve.lean"
    scratch.write_text(f"import all {module}\n", encoding="utf-8")
    is_module = compilation_module_mode(tools, compilation)
    expected = artifacts / relative.with_suffix(".olean")
    environment = dict(tools.environment)
    environment["LEAN_PATH"] = str(artifacts)
    before_parts = artifact_receipt(artifacts, relative, require_c=True, is_module=is_module)
    snapshot_inputs = pin_snapshot_inputs(tools, artifacts)
    input_identities = {str(path): source_identity(path)
                        for path in (artifacts, *artifacts.rglob("*"))}
    snapshot_setup = pin_snapshot_setup(tools, artifacts, [{"path": str(relative), "module": module}],
                                        {str(relative): compilation}, kind="single")
    setup = Path(str(snapshot_setup["path"]))
    dependency_identities = snapshot_dependency_identities(setup, tools, setup_pin=snapshot_setup)
    with guarded_snapshot_metadata(tools, setup, dependency_identities) as value:
        inventory_roots = snapshot_private_inventory_roots(tools, value)
    with guard_path_component_moves(dependency_identities,
                                    mutable_roots={tools.output, evidence},
                                    inventory_roots=inventory_roots):
        dependencies = tools.run([str(tools.lean), tools.lean_thread_argument, "--deps", str(scratch)],
                                 evidence / "deps", environment)
    require_success(dependencies)
    verify_snapshot_inputs(snapshot_inputs, artifacts, tools.output, tools, input_identities)
    verify_snapshot_dependencies(tools, artifacts, setup, dependency_identities)
    resolved = Path(str(evidence / "deps") + ".stdout").read_text().splitlines()
    if str(expected) not in resolved:
        raise ValueError("Dependency receipt did not resolve the expected compilation arm")
    environment["LEAN_PATH"] = ""
    snapshot_label = evidence / "snapshot"
    with guard_path_component_moves(dependency_identities,
                                    mutable_roots={tools.output, evidence},
                                    inventory_roots=inventory_roots):
        command = tools.run(
            [str(tools.lean), tools.lean_thread_argument, "--run", str(tools.helpers / "declarations.lean"), str(setup), module],
            snapshot_label, environment,
        )
    if missing_private_import(command, read_json(verify_file_pin(
            snapshot_setup, tools.output, tools.file_cache))):
        verify_snapshot_inputs(snapshot_inputs, artifacts, tools.output, tools, input_identities)
        verify_snapshot_dependencies(tools, artifacts, setup, dependency_identities)
        snapshot_setup = complete_private_snapshot_setup(tools, artifacts, snapshot_setup, snapshot_label)
        setup = Path(str(snapshot_setup["path"]))
        dependency_identities = {**dependency_identities, **snapshot_dependency_identities(
            setup, tools, setup_pin=snapshot_setup)}
        with guarded_snapshot_metadata(tools, setup, dependency_identities) as value:
            inventory_roots = snapshot_private_inventory_roots(tools, value)
        snapshot_label = evidence / "snapshot-private"
        with guard_path_component_moves(dependency_identities,
                                        mutable_roots={tools.output, evidence},
                                        inventory_roots=inventory_roots):
            command = tools.run([str(tools.lean), tools.lean_thread_argument, "--run", str(tools.helpers / "declarations.lean"),
                                 str(setup), module], snapshot_label, environment)
    require_success(command)
    verify_snapshot_inputs(snapshot_inputs, artifacts, tools.output, tools, input_identities)
    verify_snapshot_dependencies(tools, artifacts, setup, dependency_identities)
    snapshot = read_json(Path(str(snapshot_label) + ".stdout"))
    verify_private_loaded_modules(snapshot, read_json(verify_file_pin(
        snapshot_setup, tools.output, tools.file_cache)))
    if snapshot.get("module") != module:
        raise ValueError("Snapshot reported a different module")
    if snapshot.get("uses_module_system") is not is_module:
        raise ValueError("Snapshot module mode differs from the pinned compilation setup")
    if Path(str(snapshot.get("resolved_olean"))).resolve() != expected.resolve():
        raise ValueError("Snapshot loaded an artifact outside its compilation arm")
    declarations = snapshot.get("declarations")
    if not isinstance(declarations, list) or snapshot.get("declaration_count") != len(declarations):
        raise ValueError("Snapshot declaration count does not match the populated result")
    required = {"name", "level_params", "kind", "type", "value", "is_unsafe",
                "is_partial", "is_exported", "is_private_name", "axioms"}
    if any(not isinstance(row, dict) or not required.issubset(row) for row in declarations):
        raise ValueError("Incomplete declaration snapshot")
    after_parts = artifact_receipt(artifacts, relative, require_c=True, is_module=is_module)
    if after_parts != before_parts:
        raise ValueError("Compilation arm artifacts changed during the snapshot")
    compilation["snapshot_input_manifest"] = snapshot_inputs
    compilation["snapshot_setup"] = snapshot_setup
    if read_json(verify_file_pin(snapshot_setup, tools.output, tools.file_cache)).get(
            "snapshot_private_dependencies") is not None:
        compilation["snapshot_command_evidence"] = analysis_evidence(tools, snapshot_label, "snapshot")
    return snapshot


def snapshot_batch(tools: Tools, rows: list[dict[str, object]], artifact_root: Path | dict[str, Path],
                   directory: Path, compilations: dict[str, dict[str, object]]
                   ) -> dict[str, dict[str, object]]:
    names = [str(row["path"]) for row in rows]
    modules = [str(row["module"]) for row in rows]
    if not rows or len(set(names)) != len(names) or set(compilations) != set(names):
        raise ValueError("Batch compilation setup inventory is incomplete or different")
    roots = ({name: artifact_root for name in names} if isinstance(artifact_root, Path) else artifact_root)
    grouped = len(rows) > 1
    if set(roots) != set(names) or (grouped and
            any(str(roots[name]) != compilations[name].get("artifact_root") for name in names)):
        raise ValueError("Batch artifact roots differ from their original compilations")
    if grouped and not compatible_snapshot_group(tools, rows, compilations):
        raise ValueError("Batch original compilation inputs conflict")
    directory.mkdir(parents=True, exist_ok=True)
    evidence = directory / "snapshot-evidence"
    evidence.mkdir(exist_ok=True)
    if evidence.is_symlink():
        raise ValueError("Snapshot evidence needs a regular directory")
    probes = []
    for index, row in enumerate(rows):
        scratch = directory / (f"resolve-{index}.lean" if grouped else "resolve.lean")
        scratch.write_text(f"import all {row['module']}\n", encoding="utf-8")
        probes.append((str(row["path"]), scratch, evidence / (f"deps-{index}" if grouped else "deps")))
    for label in [*(probe[2] for probe in probes), evidence / "snapshot"]:
        for suffix in ("json", "stdout", "stderr"):
            Path(str(label) + "." + suffix).touch()
    modes = {name: compilation_module_mode(tools, compilations[name]) for name in names}
    before_parts = {name: artifact_receipt(roots[name], Path(name), require_c=True, is_module=modes[name])
                    for name in names}
    snapshot_inputs = {name: pin_snapshot_inputs(tools, roots[name]) for name in names}
    snapshot_setup = pin_snapshot_setup(tools, roots[names[0]], rows, compilations,
                                        roots=roots if grouped else None)
    setup = Path(str(snapshot_setup["path"]))
    group = pin_snapshot_group(tools, rows, compilations, snapshot_inputs, directory) if grouped else None
    input_identities = {name: {str(path): source_identity(path)
                        for path in (roots[name], *roots[name].rglob("*"))} for name in names}
    dependency_identities = snapshot_dependency_identities(setup, tools, setup_pin=snapshot_setup)
    if group is not None:
        with guarded_inventory_components({Path(str(group["path"]))}, mutable_roots={tools.output}):
            value = read_json(verify_file_pin(group, tools.output, tools.file_cache))
            paths = {Path(str(group["path"])), Path(__file__), tools.helpers / "declarations_batch.lean", tools.lean,
                     *(probe[1] for probe in probes)}
            for member in value["members"]:
                arm = member["compilation"]
                paths.update((Path(member["source"]["path"]), Path(arm["source_path"])))
                paths.update(Path(arm["command_evidence"][suffix]["path"]) for suffix in ("json", "stdout", "stderr"))
            dependency_identities.update(path_component_identities(
                paths, mutable_roots={tools.output, evidence}))
    with guarded_snapshot_metadata(tools, setup, dependency_identities) as value:
        inventory_roots = snapshot_private_inventory_roots(tools, value)

    def verify_inputs() -> None:
        with using_prepared_inputs(tools):
            for name in names:
                verify_snapshot_inputs(snapshot_inputs[name], roots[name], tools.output, tools,
                                       input_identities[name])
            verify_snapshot_dependencies(tools, roots[names[0]], setup, dependency_identities)
            if group is not None:
                for member in read_json(verify_file_pin(group, tools.output, tools.file_cache))["members"]:
                    # Each member check re-reads facts, so a change after
                    # an earlier check is seen exactly where it was before.
                    new_prepared_window(tools)
                    verify_snapshot_group_member(tools, member)

    dependencies_evidence = []
    for name, scratch, label in probes:
        environment = {**tools.environment, "LEAN_PATH": str(roots[name])}
        with guard_path_component_moves(dependency_identities,
                                        mutable_roots={tools.output, evidence},
                                        inventory_roots=inventory_roots):
            dependencies = tools.run([str(tools.lean), tools.lean_thread_argument, "--deps", str(scratch)], label, environment)
        require_success(dependencies)
        verify_inputs()
        resolved = Path(str(label) + ".stdout").read_text().splitlines()
        expected = roots[name] / Path(name).with_suffix(".olean")
        if str(expected) not in resolved:
            raise ValueError(f"Dependency receipt did not resolve the batch arm for {name}")
        dependencies_evidence.append(analysis_evidence(tools, label, "deps"))
    snapshot_label = evidence / "snapshot"
    with guard_path_component_moves(dependency_identities,
                                    mutable_roots={tools.output, evidence},
                                    inventory_roots=inventory_roots):
        command = tools.run([str(tools.lean), tools.lean_thread_argument, "--run",
                             str(tools.helpers / "declarations_batch.lean"), str(setup), *modules],
                            snapshot_label, {**tools.environment, "LEAN_PATH": ""})
    if missing_private_import(command, read_json(verify_file_pin(
            snapshot_setup, tools.output, tools.file_cache))):
        verify_inputs()
        snapshot_setup = complete_private_snapshot_setup(tools, roots[names[0]], snapshot_setup, snapshot_label)
        setup = Path(str(snapshot_setup["path"]))
        dependency_identities = {**dependency_identities, **snapshot_dependency_identities(
            setup, tools, setup_pin=snapshot_setup)}
        with guarded_snapshot_metadata(tools, setup, dependency_identities) as value:
            inventory_roots = snapshot_private_inventory_roots(tools, value)
        snapshot_label = evidence / "snapshot-private"
        with guard_path_component_moves(dependency_identities,
                                        mutable_roots={tools.output, evidence},
                                        inventory_roots=inventory_roots):
            command = tools.run([str(tools.lean), tools.lean_thread_argument, "--run",
                                 str(tools.helpers / "declarations_batch.lean"), str(setup), *modules],
                                snapshot_label, {**tools.environment, "LEAN_PATH": ""})
    require_success(command)
    verify_inputs()
    snapshots = [json.loads(line) for line in
                 Path(str(snapshot_label) + ".stdout").read_text().splitlines() if line]
    if len(snapshots) != len(rows):
        raise ValueError("Batch snapshot returned an incomplete target set")
    if any(not isinstance(snapshot, dict) for snapshot in snapshots):
        raise ValueError("Batch snapshot returned a nonobject target")
    required = {"name", "level_params", "kind", "type", "value", "is_unsafe",
                "is_partial", "is_exported", "is_private_name", "axioms"}
    result = {}
    for row, snapshot in zip(rows, snapshots):
        module, relative = str(row["module"]), Path(str(row["path"]))
        expected = roots[str(relative)] / relative.with_suffix(".olean")
        if snapshot.get("module") != module:
            raise ValueError("Batch snapshot target order or module identity changed")
        if snapshot.get("uses_module_system") is not modes[str(relative)]:
            raise ValueError("Batch snapshot module mode differs from the pinned compilation setup")
        if Path(str(snapshot.get("resolved_olean"))).resolve() != expected.resolve():
            raise ValueError("Batch snapshot loaded an artifact outside its arm")
        if (snapshot.get("batch_modules") != modules or
                snapshot.get("batch_module_count") != len(modules) or
                snapshot.get("loaded_modules_scope") != "whole_batch"):
            raise ValueError("Batch snapshot did not describe its shared loaded environment")
        verify_batch_loaded_modules(snapshot, modules, snapshots[0].get("loaded_modules"))
        verify_private_loaded_modules(snapshot, read_json(verify_file_pin(
            snapshot_setup, tools.output, tools.file_cache)))
        declarations = snapshot.get("declarations")
        if not isinstance(declarations, list) or snapshot.get("declaration_count") != len(declarations):
            raise ValueError("Batch snapshot declaration count differs from its result")
        if any(not isinstance(record, dict) or not required.issubset(record) for record in declarations):
            raise ValueError("Batch snapshot has incomplete owned declaration records")
        if artifact_receipt(roots[str(relative)], relative, require_c=True,
                            is_module=modes[str(relative)]) != before_parts[str(relative)]:
            raise ValueError("Batch arm artifacts changed while taking its snapshot")
        result[module] = snapshot
    for name in names:
        compilations[name]["snapshot_input_manifest"] = dict(snapshot_inputs[name])
        compilations[name]["snapshot_setup"] = dict(snapshot_setup)
        if group is not None or read_json(verify_file_pin(
                snapshot_setup, tools.output, tools.file_cache)).get("snapshot_private_dependencies") is not None:
            compilations[name]["snapshot_command_evidence"] = analysis_evidence(tools, snapshot_label, "snapshot")
        if group is not None:
            compilations[name]["snapshot_group"] = dict(group)
            compilations[name]["snapshot_dependencies"] = dependencies_evidence
    return result


def verify_saved_candidate(result: dict[str, object], output: Path,
                           tools: Tools | None = None) -> None:
    # Both arms and the snapshot evidence re-derive the inputs of the
    # bundle's own setup; inside a phase they share its derivations.
    if tools is None:
        _verify_saved_candidate(result, output, tools)
        return
    with using_prepared_inputs(tools):
        _verify_saved_candidate(result, output, tools)


def _verify_saved_candidate(result: dict[str, object], output: Path,
                            tools: Tools | None = None) -> None:
    if tools is None or tools.output != output:
        raise ValueError("Saved candidates require their complete validation tools")
    directory = Path(str(result["attempt_directory"])).resolve()
    if not directory.is_relative_to(output.resolve()):
        raise ValueError("Saved candidate evidence is outside its run directory")
    if (sha256(directory / "original.lean") != result["source_sha256"] or
            sha256(directory / "candidate.lean") != result["candidate_sha256"] or
            sha256(directory / "proposal.patch") != result["proposal_patch_sha256"]):
        raise ValueError("Saved candidate source or patch evidence changed")
    if (sha256(directory / "owned-before.json") != result.get("owned_before_sha256") or
            sha256(directory / "owned-after.json") != result.get("owned_after_sha256")):
        raise ValueError("Saved candidate snapshot bytes changed")
    before, after = read_json(directory / "owned-before.json"), read_json(directory / "owned-after.json")
    native_header = verify_file_pin(result.get("native_header"), output,
                                  tools.file_cache if tools is not None else None)
    header = decode_header(read_json(native_header), (directory / "original.lean").read_bytes())
    original, saved_header, proposal = verify_saved_proposal(result, tools)
    verify_shared_snapshot_failure(result, tools)
    if (read_json(native_header) != saved_header or
            original != (directory / "original.lean").read_bytes() or
            rewrite_imports(original, header, proposal.remove, proposal.add) !=
            (directory / "candidate.lean").read_bytes()):
        raise ValueError("Saved analysis does not establish the candidate source")
    relative = Path(str(result["path"]))
    patch = b"".join(difflib.diff_bytes(
        difflib.unified_diff, original.splitlines(keepends=True),
        (directory / "candidate.lean").read_bytes().splitlines(keepends=True),
        fromfile=("a/" + str(relative)).encode(), tofile=("b/" + str(relative)).encode(),
    ))
    if (result.get("proposal_patch") != str(directory / "proposal.patch") or
            (directory / "proposal.patch").read_bytes() != patch):
        raise ValueError("Saved analysis does not establish the candidate patch")
    required = {"name", "level_params", "kind", "type", "value", "is_unsafe",
                "is_partial", "is_exported", "is_private_name", "axioms"}
    for snapshot in (before, after):
        declarations = snapshot.get("declarations")
        count = snapshot.get("declaration_count")
        if (snapshot.get("module") != result["module"] or
                not isinstance(declarations, list) or type(count) is not int or
                count != len(declarations) or count != result["declaration_count"]):
            raise ValueError("Saved candidate declaration count or module identity changed")
        if any(not isinstance(record, dict) or not required.issubset(record)
               for record in declarations):
            raise ValueError("Saved candidate has incomplete owned declaration records")
    if compare_snapshots(before, after):
        raise ValueError("Saved candidate declaration evidence changed")
    relative = Path(str(result["path"]))
    for name, snapshot in (("baseline", before), ("candidate", after)):
        arm = cast(dict[str, object], result[name])
        command = arm.get("command")
        if not isinstance(command, dict):
            raise ValueError("Saved compilation command completion receipt is missing")
        require_success(command)
        cache = tools.file_cache if tools is not None else None
        source_root, source = arm.get("source_root"), arm.get("source_path")
        source_hash = result["source_sha256" if name == "baseline" else "candidate_sha256"]
        if (not isinstance(source_root, str) or not isinstance(source, str) or
                Path(source_root) != directory / name / "source" or
                Path(source) != Path(source_root) / relative or
                not Path(source_root).resolve().is_relative_to(directory) or
                arm.get("source_sha256") != source_hash):
            raise ValueError("Saved compilation source identity is missing or changed")
        if file_pin(Path(source), cache)["sha256"] != source_hash:
            raise ValueError("Saved compilation source bytes differ from the saved source")
        if (not isinstance(result.get("setup_path"), str) or
                not isinstance(result.get("setup_root"), str) or
                arm.get("setup_root") != result["setup_root"] or
                arm.get("setup_sha256") != result.get("setup_sha256")):
            raise ValueError("Saved compilation setup identity is missing or changed")
        setup = verify_file_pin(arm.get("setup"), output, cache)
        production = verify_file_pin(arm.get("setup_source"), cache=cache)
        if (setup != directory / name / "setup.json" or str(production) != result["setup_path"] or
                cast(dict[str, object], arm["setup"])["sha256"] != result["setup_sha256"] or
                cast(dict[str, object], arm["setup_source"])["sha256"] != result["setup_sha256"]):
            raise ValueError("Saved compilation setup bytes differ from the original pin")
        root = Path(result["setup_root"])
        if not root.is_absolute() or (tools is not None and root != tools.root):
            raise ValueError("Saved compilation setup belongs to a different project")
        metadata = read_json(setup)
        if arm.get("header_is_module") is not header.is_module:
            raise ValueError("Saved compilation source module mode differs from its native header")
        is_module = effective_module_mode(metadata, header.is_module)
        if metadata.get("name") != result["module"] or metadata.get("imports") is not None:
            raise ValueError("Saved compilation setup changes the module or source imports")
        if "standard_library_root" not in arm:
            raise ValueError("Saved compilation has no standard-library input identity")
        library = arm["standard_library_root"]
        if library is not None and not isinstance(library, str):
            raise ValueError("Invalid saved compiler standard-library root")
        library = Path(library) if library is not None else None
        if tools is not None and library != standard_library_root(tools):
            raise ValueError("Saved compilation resolved a different compiler standard library")
        files = verify_input_manifest(arm.get("input_manifest"),
                                      compilation_input_paths(metadata, root, library, tools), output, tools)
        if not files:
            raise ValueError("Saved snapshot compilation input manifest is empty")
        artifact_root = Path(str(arm["artifact_root"])).resolve()
        if not artifact_root.is_relative_to(output.resolve()):
            raise ValueError("Saved compilation arm is outside its run directory")
        verify_compilation_command(tools, relative, directory / name, artifact_root, arm)
        if artifact_receipt(artifact_root, relative, require_c=True, is_module=is_module) != arm["artifacts"]:
            raise ValueError("Saved compilation artifacts are missing or changed")
        expected = artifact_root / relative.with_suffix(".olean")
        if Path(str(snapshot.get("resolved_olean"))).resolve() != expected:
            raise ValueError("Saved declaration snapshot resolved a different compilation arm")
        if snapshot.get("uses_module_system") is not is_module:
            raise ValueError("Saved snapshot module mode differs from the pinned compilation setup")
        verify_snapshot_inputs(arm.get("snapshot_input_manifest"), artifact_root, output, tools)
        if arm.get("snapshot_group") is not None:
            verify_saved_snapshot_group(tools, arm, relative, snapshot)
            continue
        setup = verify_file_pin(arm.get("snapshot_setup"), output, cache)
        value = read_json(setup)
        contexts = value.get("snapshot_compilations")
        expected = {"module": result["module"], **{field: arm.get(field) for field in
                    ("setup", "header_is_module", "standard_library_root", "input_manifest",
                     "private_fallback_manifest")}}
        if not isinstance(contexts, dict):
            raise ValueError("Saved snapshot compilation inputs changed")
        if list(contexts) != [str(relative)] or contexts[str(relative)] != expected:
            raise ValueError("Saved snapshot compilation inputs changed")
        modules = [result["module"]]
        if snapshot_setup_value(tools, artifact_root, contexts, str(value.get("snapshot_kind")),
                                value.get("snapshot_private_dependencies")) != value:
            raise ValueError("Saved snapshot compilation inputs changed")
        verify_private_loaded_modules(snapshot, value)
        if value.get("snapshot_private_dependencies") is not None:
            evidence = arm.get("snapshot_command_evidence")
            command, _ = read_analysis(tools, evidence)
            require_success(command)
            helper = tools.helpers / ("declarations_batch.lean" if value["snapshot_kind"] == "batch"
                                      else "declarations.lean")
            if (not isinstance(evidence, dict) or evidence.get("kind") != "snapshot" or
                    command.get("argv") != [str(tools.lean), tools.lean_thread_argument, "--run", str(helper), str(setup), *modules] or
                    read_json(verify_file_pin(evidence["stdout"], output, cache)) != snapshot):
                raise ValueError("Saved private snapshot output differs from its command")
        if value["snapshot_kind"] == "batch":
            if (snapshot.get("loaded_modules_scope") != "whole_batch" or
                    snapshot.get("batch_modules") != modules or snapshot.get("batch_module_count") != len(modules)):
                raise ValueError("Saved shared snapshot lost its loaded-module scope")
            verify_batch_loaded_modules(snapshot, modules, snapshot.get("loaded_modules"))
        elif any(field in snapshot for field in ("batch_modules", "batch_module_count", "loaded_modules_scope")):
            raise ValueError("Saved single snapshot has a shared loaded-module scope")


def analysis_inputs(tools: Tools, rows: list[dict[str, object]],
                    recorded: object = None) -> dict[str, object]:
    """Current Shake inputs; on resume, a recorded input manifest is checked, not repinned."""
    run = tools.output / "run.json"
    compiled_inputs = {}
    for row in rows:
        relative = Path(str(row["path"]))
        setup = tools.root / ".lake/build/ir" / relative.with_suffix(".setup.json")
        setup_receipt = file_pin(setup, tools.file_cache)
        metadata = read_json(setup)
        if metadata.get("name") != row["module"] or metadata.get("imports") is not None:
            raise ValueError("Shake compilation setup changes the module or source imports")
        library = standard_library_root(tools)
        saved_manifest = (cast(dict[str, dict[str, object]], recorded["compiled_inputs"]).get(str(relative), {})
                          .get("input_manifest") if isinstance(recorded, dict) and
                          isinstance(recorded.get("compiled_inputs"), dict) else None)
        if _recorded_lake_growth.get() is not None and isinstance(saved_manifest, dict):
            verify_input_manifest(saved_manifest,
                                  compilation_input_paths(metadata, tools.root, library, tools),
                                  tools.output, tools)
            input_manifest = saved_manifest
        else:
            input_manifest = pin_setup_inputs(tools, metadata)
        artifacts = artifact_receipt(tools.root / ".lake/build/lib/lean", relative, cache=tools.file_cache)
        record_root_custody(tools, artifacts)
        compiled_inputs[str(relative)] = {
            "setup": setup_receipt,
            "artifacts": artifacts,
            "standard_library_root": str(library) if library is not None else None,
            "input_manifest": input_manifest,
        }
        if file_pin(setup, tools.file_cache) != setup_receipt:
            raise ValueError("Shake compilation setup changed while capturing inputs")
    return {"sources": {str(row["path"]): row["source_sha256"] for row in rows},
            "compiled_inputs": compiled_inputs,
            "manifest_sha256": read_json(run)["manifest_sha256"] if run.exists() else None,
            "compiler_sha256": sha256(tools.lean),
            "lean_threads": tools.lean_threads, "lake_jobs": tools.lake_jobs,
            "effective_config_sha256": sha256(tools.lake_config) if tools.lake_config else None}


def analysis_evidence(tools: Tools, label: Path, kind: str,
                      inputs: dict[str, object] | None = None) -> dict[str, object]:
    return {"kind": kind, "inputs": inputs,
            **{suffix: file_pin(Path(str(label) + "." + suffix), tools.file_cache)
               for suffix in ("json", "stdout", "stderr")}}


def read_analysis(tools: Tools, evidence: object) -> tuple[dict[str, object], str]:
    if not isinstance(evidence, dict):
        raise ValueError("Missing immutable proposal analysis evidence")
    paths = {suffix: verify_file_pin(evidence.get(suffix), tools.output, tools.file_cache)
             for suffix in ("json", "stdout", "stderr")}
    command = read_json(paths["json"])
    if (command.get("cwd") != str(tools.root) or command.get("timed_out") is not False or
            command.get("remaining_group_killed") is not False or
            command.get("remaining_group_members") or type(command.get("exit_code")) is not int or
            any(command.get(suffix) != str(paths[suffix]) for suffix in ("stdout", "stderr"))):
        raise ValueError("Saved analysis command identity or completion changed")
    return command, paths["stdout"].read_text() + "\n" + paths["stderr"].read_text()


def check_shake_inputs(tools: Tools, inputs: object) -> list[dict[str, object]]:
    if (not isinstance(inputs, dict) or not isinstance(inputs.get("sources"), dict) or
            not isinstance(inputs.get("compiled_inputs"), dict) or
            inputs["sources"].keys() != inputs["compiled_inputs"].keys()):
        raise ValueError("Saved Shake proposal has incomplete input identities")
    rows = []
    for path, digest in inputs["sources"].items():
        if not isinstance(path, str) or not isinstance(digest, str):
            raise ValueError("Saved Shake source identity is invalid")
        compiled = inputs["compiled_inputs"][path]
        if not isinstance(compiled, dict):
            raise ValueError("Saved Shake compiled input identity is invalid")
        setup = verify_file_pin(compiled.get("setup"), cache=tools.file_cache)
        verify_file_pin(compiled.get("input_manifest"), tools.output, tools.file_cache)
        name = read_json(setup).get("name")
        if not isinstance(name, str):
            raise ValueError("Saved Shake setup has no module identity")
        row = {"path": path, "module": name, "source_sha256": digest, "analysis_status": "pending"}
        validate_manifest_row(row)
        rows.append(row)
    if len({row["module"] for row in rows}) != len(rows):
        raise ValueError("Saved Shake inputs contain duplicate module identities")
    validate_inventory_sources(tools.root, rows, tools.file_cache)
    with using_prepared_inputs(tools):
        current = analysis_inputs(tools, rows, inputs)
    if current != inputs:
        raise ValueError("Saved Shake proposal inputs changed")
    return rows


def verify_shake_inputs(tools: Tools, inputs: object) -> list[dict[str, object]]:
    cached = tools.validated_analysis_inputs.get("phase")
    if cached is not None:
        for saved, rows in cached:
            if inputs == saved:
                return rows
    rows = check_shake_inputs(tools, inputs)
    if cached is not None:
        cached.append((deepcopy(cast(dict[str, object], inputs)), rows))
    return rows


def revalidate_analysis_inputs(tools: Tools) -> None:
    with using_prepared_inputs(tools):
        _revalidate_analysis_inputs(tools)


def _revalidate_analysis_inputs(tools: Tools) -> None:
    cached = tools.validated_analysis_inputs.get("phase")
    if cached is not None:
        tools.validated_analysis_inputs["phase"] = []
        for inputs, _ in cached:
            check_shake_inputs(tools, inputs)
    groups = tools.validated_snapshot_groups.get("phase")
    if groups is not None:
        tools.validated_snapshot_groups["phase"] = {}
        for records in groups.values():
            for checked in records:
                check_saved_snapshot_group(tools, checked.evidence)


@contextmanager
def analysis_validation_phase(tools: Tools) -> Iterator[None]:
    if "phase" in tools.validated_analysis_inputs:
        raise ValueError("Analysis validation phases may not nest")
    tools.validated_analysis_inputs["phase"] = []
    tools.validated_snapshot_groups["phase"] = {}
    tools.prepared_inputs["phase"] = PreparedInputs(tools)
    try:
        yield
    finally:
        try:
            tools.prepared_inputs["phase"].new_window()
            revalidate_analysis_inputs(tools)
        finally:
            tools.validated_analysis_inputs.pop("phase", None)
            tools.validated_snapshot_groups.pop("phase", None)
            tools.prepared_inputs.pop("phase", None)


def derive_snapshot_failure_error(tools: Tools, arms: dict[str, object]) -> str | None:
    """Re-derive the failure text from pinned command evidence.

    `require_success` failures are fully determined by the recorded
    command receipts: the first deps/snapshot command (baseline arm
    first) with a nonzero exit code yields exactly
    `Command exited <code>; see <stderr path>`. Other failure modes
    (input-identity and target validation) are not command failures
    and derive `None`; those keep the manifest/journal equality
    checks."""
    for arm in ("baseline", "candidate"):
        entry = arms.get(arm)
        if not isinstance(entry, dict):
            continue
        records = [*entry.get("deps", []), entry.get("snapshot")]
        for record in records:
            if not isinstance(record, dict):
                continue
            command, _ = read_analysis(tools, record)
            if command.get("exit_code") == 0:
                continue
            if command.get("exit_code") == 3:
                # Exit 3 may be the successful control-flow receipt that
                # requests private-closure completion. It is not itself
                # the grouped failure: private completion (or the final
                # `snapshot-private` command) must be the error source.
                # A malformed stderr receipt is not that signal and
                # remains an ordinary command failure.
                try:
                    missing_row = read_json(Path(str(record["stderr"]["path"])))
                except (OSError, ValueError):
                    missing_row = {}
                if missing_row.get("kind") == "missing_private_import_artifacts":
                    continue
            return f"Command exited {command.get('exit_code')}; see {record['stderr']['path']}"
    return None


def snapshot_failure_receipt(tools: Tools, batch_directory: Path, index: int,
                             rows: list[dict[str, object]], error: BaseException
                             ) -> dict[str, object]:
    """Immutable receipts for a failed grouped snapshot (per review).

    The grouped-snapshot fallback previously recorded only a free-form
    error and a directory, so resume accepted a deleted
    `snapshot.stdout` or a forged failure reason. Pin every evidence
    file the failed joint attempt produced, plus the deps/snapshot
    command evidence of each attempted arm, analogously to
    `shared_analysis_failure`. The pinned `snapshot-failure.json`
    manifest anchors the complete receipt/arm inventory, so a journal
    cannot discard command evidence and still resume;
    `verify_shared_snapshot_failure` revalidates all of it."""
    group_directory = batch_directory / "snapshots" / str(index)
    group_directory.mkdir(parents=True, exist_ok=True)
    arms: dict[str, object] = {}
    arms_inventory: dict[str, object] = {}
    for arm in ("baseline", "candidate"):
        evidence = group_directory / arm / "snapshot-evidence"
        entry: dict[str, object] = {}
        inventory: dict[str, object] = {"deps": [], "snapshot": False}
        if evidence.is_dir():
            deps = []
            for label in sorted(evidence.glob("deps*.json")):
                # snapshot_batch pre-creates empty placeholder files for
                # every deps label; only completed, nonempty command
                # records are command evidence (raw pins below still
                # cover the incomplete placeholders).
                if label.stat().st_size:
                    deps.append(analysis_evidence(tools, evidence / label.name[:-len(".json")], "deps"))
                    inventory["deps"].append(label.name[:-len(".json")])
            if deps:
                entry["deps"] = deps
            # `snapshot.json` may be only the exit-3 missing-private
            # control receipt. When private completion got far enough
            # to run `snapshot-private`, that later completed attempt
            # is the represented snapshot command for failure
            # derivation/verification; the exit-3 receipt remains in
            # the raw receipt inventory above.
            if ((evidence / "snapshot-private.json").is_file() and
                    (evidence / "snapshot-private.json").stat().st_size):
                entry["snapshot"] = analysis_evidence(
                    tools, evidence / "snapshot-private", "snapshot")
                inventory["snapshot"] = True
            else:
                snap_json = evidence / "snapshot.json"
                if snap_json.is_file() and snap_json.stat().st_size:
                    entry["snapshot"] = analysis_evidence(tools, evidence / "snapshot", "snapshot")
                    inventory["snapshot"] = True
        if entry:
            arms[arm] = entry
            arms_inventory[arm] = inventory
    receipt_paths = sorted(
        [str(path.relative_to(group_directory)) for path in group_directory.rglob("*")
         if path.is_file() and not path.is_symlink()] + ["snapshot-failure.json"])
    failure_record = {"error": str(error),
                      "derived_error": derive_snapshot_failure_error(tools, arms),
                      "index": index,
                      "paths": [str(row["path"]) for row in rows],
                      "modules": [str(row["module"]) for row in rows],
                      "batch_directory": str(batch_directory),
                      "receipt_paths": receipt_paths,
                      "arms": arms_inventory}
    write_json(group_directory / "snapshot-failure.json", failure_record)
    receipts: dict[str, object] = {}
    for path in sorted(group_directory.rglob("*")):
        if path.is_file() and not path.is_symlink():
            receipts[str(path.relative_to(group_directory))] = file_pin(path, tools.file_cache)
    return {"error": str(error), "directory": str(group_directory), "index": index,
            "paths": [str(row["path"]) for row in rows],
            "modules": [str(row["module"]) for row in rows],
            "batch_directory": str(batch_directory),
            "receipts": receipts, "arms": arms}


def verify_shared_snapshot_failure(result: dict[str, object], tools: Tools) -> None:
    failure = result.get("shared_snapshot_failure")
    if failure is None:
        return
    if (not isinstance(failure, dict) or not isinstance(failure.get("error"), str) or
            not failure["error"]):
        raise ValueError("Saved shared snapshot failure is invalid")
    index, paths, modules = failure.get("index"), failure.get("paths"), failure.get("modules")
    if (type(index) is not int or index < 0 or not isinstance(paths, list) or
            not isinstance(modules, list) or len(paths) != len(modules) or len(paths) < 2 or
            result.get("path") not in paths or result.get("module") not in modules):
        raise ValueError("Saved shared snapshot failure belongs to different inputs")
    directory = failure.get("directory")
    batch_directory = failure.get("batch_directory")
    if (not isinstance(directory, str) or not isinstance(batch_directory, str) or
            Path(directory) != Path(batch_directory) / "snapshots" / str(index) or
            Path(batch_directory).parent.name != "attempts" or
            Path(batch_directory).parent.parent.parent.name != "batches" or
            not Path(batch_directory).resolve().is_relative_to(tools.output.resolve())):
        raise ValueError("Saved shared snapshot failure directory changed")
    expected = Path(directory)
    receipts = failure.get("receipts")
    if not isinstance(receipts, dict) or not receipts:
        raise ValueError("Saved shared snapshot failure has no immutable receipts")
    for relative, pin in receipts.items():
        path = verify_file_pin(pin, tools.output, tools.file_cache)
        if not isinstance(relative, str) or path != expected / relative:
            raise ValueError("Saved shared snapshot failure receipt path changed")
    failure_file = expected / "snapshot-failure.json"
    if "snapshot-failure.json" not in receipts:
        raise ValueError("Saved shared snapshot failure has no failure receipt")
    recorded = read_json(failure_file)
    if (recorded.get("error") != failure["error"] or recorded.get("index") != index or
            recorded.get("paths") != paths or recorded.get("modules") != modules or
            recorded.get("batch_directory") != batch_directory):
        raise ValueError("Saved shared snapshot failure differs from its failure receipt")
    if recorded.get("receipt_paths") != sorted(receipts):
        raise ValueError("Saved shared snapshot failure receipt inventory changed")
    arms = failure.get("arms")
    if not isinstance(arms, dict):
        raise ValueError("Saved shared snapshot failure command evidence is invalid")
    inventory: dict[str, object] = {}
    for arm, entry in arms.items():
        if arm not in ("baseline", "candidate") or not isinstance(entry, dict):
            raise ValueError("Saved shared snapshot failure arm is invalid")
        labels = []
        for dep in entry.get("deps", []):
            if not isinstance(dep, dict) or dep.get("kind") != "deps":
                raise ValueError("Saved shared snapshot failure has no deps evidence")
            read_analysis(tools, dep)
            labels.append(Path(str(dep["json"]["path"])).name[:-len(".json")])
        snap = entry.get("snapshot")
        if snap is not None:
            if not isinstance(snap, dict) or snap.get("kind") != "snapshot":
                raise ValueError("Saved shared snapshot failure has no snapshot evidence")
            command, _ = read_analysis(tools, snap)
            argv = command.get("argv")
            if (not isinstance(argv, list) or
                    not any("declarations_batch" in str(word) for word in argv) or
                    argv[-len(modules):] != modules):
                raise ValueError("Saved shared snapshot failure command belongs to different inputs")
        inventory[arm] = {"deps": sorted(labels), "snapshot": snap is not None}
    if recorded.get("arms") != inventory:
        raise ValueError("Saved shared snapshot failure arm inventory changed")
    derived = derive_snapshot_failure_error(tools, arms)
    if recorded.get("derived_error") != derived:
        raise ValueError("Saved shared snapshot failure derivation changed")
    if derived is not None and failure["error"] != derived:
        raise ValueError("Saved shared snapshot failure differs from its command evidence")


def verify_saved_proposal(result: dict[str, object], tools: Tools
                          ) -> tuple[bytes, dict[str, object], Proposal]:
    receipt = verify_file_pin(result.get("proposal_receipt"), tools.output, tools.file_cache)
    if receipt != Path(str(result["attempt_directory"])) / "proposal.json":
        raise ValueError("Saved proposal receipt belongs to a different attempt")
    saved = read_json(receipt)
    if any(saved.get(key) != result.get(key) for key in ("path", "module", "source_sha256")):
        raise ValueError("Saved proposal belongs to a different source")
    source = source_path(tools.root, str(result["path"]))
    original = source.read_bytes()
    if hashlib.sha256(original).hexdigest() != result["source_sha256"]:
        raise ValueError("Saved proposal source changed")
    native = saved.get("native_header")
    if (not isinstance(native, dict) or native.get("source_sha256") != result["source_sha256"] or
            native.get("relative_path") != result["path"]):
        raise ValueError("Saved proposal native header identity changed")
    verify_header(native, original, Counter())
    header = decode_header(native, original)
    evidence = saved.get("analysis")
    if not isinstance(evidence, dict):
        raise ValueError("Missing saved proposal analysis")
    shared_failure = evidence.get("shared_analysis_failure")
    if result.get("shared_analysis_failure") != shared_failure:
        raise ValueError("Saved joint analysis failure differs from its proposal")
    if shared_failure is not None:
        if (not isinstance(shared_failure, dict) or
                not isinstance(shared_failure.get("error"), str)):
            raise ValueError("Saved joint analysis failure is invalid")
        failed_evidence = shared_failure.get("evidence")
        command, failed_output = read_analysis(tools, failed_evidence)
        if not isinstance(failed_evidence, dict) or failed_evidence.get("kind") != "shake":
            raise ValueError("Saved joint analysis failure has no Shake evidence")
        failed_rows = verify_shake_inputs(tools, failed_evidence.get("inputs"))
        argv = command.get("argv")
        prefix = tools.lake_command("shake", "--force", "--explain", "--add-public")
        if not isinstance(argv, list) or any(not isinstance(word, str) for word in argv):
            raise ValueError("Saved joint analysis command has no argument list")
        selected = []
        index = len(prefix)
        while index + 1 < len(argv) and argv[index] == "--only":
            selected.append(argv[index + 1])
            index += 2
        if (not header.is_module or len(failed_rows) < 2 or
                argv[:len(prefix)] != prefix or argv[index:] != selected or
                len(selected) != len(failed_rows) or len(selected) != len(set(selected)) or
                set(selected) != {row["module"] for row in failed_rows} or
                not any(row["path"] == result["path"] and row["module"] == result["module"]
                        for row in failed_rows)):
            raise ValueError("Saved joint analysis failure belongs to different inputs")
        try:
            for row in failed_rows:
                parse_shake_output(failed_output, cast(int, command["exit_code"]),
                                   source_path(tools.root, str(row["path"])), tools.root)
        except ValueError as error:
            if str(error) != shared_failure["error"]:
                raise ValueError("Saved joint analysis failure changed") from error
        else:
            raise ValueError("Saved joint analysis did not fail")
    kind = evidence.get("kind")
    if kind == "source_keep":
        if header.is_module or b"shake: keep" not in original[:header.body_boundary]:
            raise ValueError("Saved keep decision has no source directive")
        proposal = Proposal()
    else:
        command, output = read_analysis(tools, evidence)
        argv = command.get("argv")
        if not isinstance(argv, list) or any(not isinstance(word, str) for word in argv):
            raise ValueError("Saved analysis command has no argument list")
        module = str(result["module"])
        if kind == "shake":
            inputs = evidence.get("inputs")
            if (not header.is_module or not isinstance(inputs, dict) or
                    not isinstance(inputs.get("sources"), dict) or
                    inputs["sources"].get(result["path"]) != result["source_sha256"] or
                    not isinstance(inputs.get("compiled_inputs"), dict) or
                    inputs["sources"].keys() != inputs["compiled_inputs"].keys()):
                raise ValueError("Saved Shake proposal inputs or requested module changed")
            rows = verify_shake_inputs(tools, inputs)
            prefix = tools.lake_command("shake", "--force", "--explain", "--add-public")
            selected = []
            index = len(prefix)
            while index + 1 < len(argv) and argv[index] == "--only":
                selected.append(argv[index + 1])
                index += 2
            if (argv[:len(prefix)] != prefix or argv[index:] != selected or
                    len(selected) != len(rows) or len(selected) != len(set(selected)) or
                    set(selected) != {row["module"] for row in rows} or
                    not any(row["path"] == result["path"] and row["module"] == module for row in rows)):
                raise ValueError("Saved Shake proposal inputs or requested module changed")
            proposal = parse_shake_output(output, cast(int, command["exit_code"]), source, tools.root)
        elif kind == "legacy":
            require_success(command)
            if header.is_module or argv != [str(tools.lean), tools.lean_thread_argument, "--run", str(tools.helpers / "legacy.lean"), module]:
                raise ValueError("Saved legacy proposal command changed")
            backend = read_json(Path(str(cast(dict[str, object], evidence["stdout"])["path"])))
            modules = backend.get("required_modules")
            if (backend.get("module") != module or not isinstance(modules, list) or
                    any(not isinstance(name, str) for name in modules)):
                raise ValueError("Saved legacy proposal result changed")
            proposal = Proposal()
        else:
            raise ValueError("Unknown saved proposal analysis backend")
    if (saved.get("removed_imports") != [spec.render() for spec in proposal.remove] or
            saved.get("added_imports") != [spec.render() for spec in proposal.add] or
            result.get("removed_imports") != saved["removed_imports"] or
            result.get("added_imports") != saved["added_imports"] or
            result.get("old_imports") != [spec.render() for spec in header.specs()]):
        raise ValueError("Saved imports differ from the official analysis")
    return original, native, proposal


def verify_saved_no_change(result: dict[str, object], tools: Tools) -> None:
    original, native, proposal = verify_saved_proposal(result, tools)
    if rewrite_imports(original, decode_header(native, original), proposal.remove, proposal.add) != original:
        raise ValueError("Saved analysis does not establish the no-change result")


def legacy_proposal(tools: Tools, module: str, header: Header,
                    source: bytes, directory: Path) -> Proposal:
    if b"shake: keep" in source[:header.body_boundary]:
        return Proposal(evidence={"kind": "source_keep"})
    helper = tools.helpers / "legacy.lean"
    if not helper.is_file():
        raise ValueError("Legacy ImportGraph backend is unavailable")
    command = tools.run([str(tools.lean), tools.lean_thread_argument, "--run", str(helper), module],
                        directory / "legacy")
    require_success(command)
    result = read_json(Path(str(directory / "legacy") + ".stdout"))
    if result.get("module") != module:
        raise ValueError("Legacy backend reported a different module")
    modules = result.get("required_modules")
    if not isinstance(modules, list) or any(not isinstance(name, str) for name in modules):
        raise ValueError("Legacy backend has no required-module list")
    return Proposal(evidence=analysis_evidence(tools, directory / "legacy", "legacy"))


def optimize_one(tools: Tools, row: dict[str, object], native: dict[str, object],
                 proposal: Proposal | None = None,
                 prepared_build: dict[str, object] | None = None, *,
                 defer_snapshots: bool = False,
                 artifact_roots: tuple[Path, Path] | None = None) -> dict[str, object]:
    relative = Path(str(row["path"]))
    source = source_path(tools.root, str(relative))
    module = str(row["module"])
    directory = tools.output / "attempts" / relative.with_suffix("") / str(time.time_ns())
    directory.mkdir(parents=True)
    original = source.read_bytes()
    source_hash = hashlib.sha256(original).hexdigest()
    result: dict[str, object] = {
        "path": str(relative), "module": module, "source_sha256": source_hash,
        "attempt_directory": str(directory), "status": "pending",
        "consumer_validation": "not_run", "global_optimality": "not_claimed",
    }
    if source_hash != row["source_sha256"]:
        raise ValueError(f"Frozen source changed: {source}")
    try:
        recover_source_edit(tools.root, tools.output / "transaction.json")
        header = decode_header(native, original)
        # Without the batch's frozen dependency graph, only the target's own
        # artifacts may be added.
        build = prepared_build or run_lake_preparation(
            tools, tools.lake_command("build", "+" + module), directory / "baseline-build",
            frozenset({module}))
        result["baseline_build"] = build
        require_success(build)
        artifact_receipt(tools.root / ".lake/build/lib/lean", relative)
        setup = tools.root / ".lake/build/ir" / relative.with_suffix(".setup.json")
        metadata = read_json(setup)
        if metadata.get("name") != module or setup_module_mode(metadata) != header.is_module:
            raise ValueError("Lake setup belongs to a different module or module mode")
        if metadata.get("imports") is not None:
            raise ValueError("Lake setup overrides source imports")
        result["setup_sha256"] = sha256(setup)
        result["setup_path"], result["setup_root"] = str(setup), str(tools.root)
        if proposal is None:
            if header.is_module:
                inputs = analysis_inputs(tools, [row])
                shake = tools.run(
                    tools.lake_command("shake", "--force", "--explain", "--add-public",
                                       "--only", module, module), directory / "shake",
                )
                require_completion(shake)
                result["analysis"] = shake
                output = Path(str(directory / "shake") + ".stdout").read_text()
                output += "\n" + Path(str(directory / "shake") + ".stderr").read_text()
                if analysis_inputs(tools, [row]) != inputs:
                    raise ValueError("Compiled inputs changed during Shake analysis")
                parsed = parse_shake_output(output, cast(int, shake["exit_code"]), source, tools.root)
                proposal = Proposal(parsed.remove, parsed.add, analysis_evidence(
                    tools, directory / "shake", "shake", inputs))
            else:
                proposal = legacy_proposal(tools, module, header, original, directory)
        if proposal.evidence is not None and "shared_analysis_failure" in proposal.evidence:
            result["shared_analysis_failure"] = proposal.evidence["shared_analysis_failure"]
        result["old_imports"] = [spec.render() for spec in header.specs()]
        if not header.is_module and proposal.remove:
            raise ValueError("Removing legacy imports requires downstream consumer validation")
        result["removed_imports"] = [spec.render() for spec in proposal.remove]
        result["added_imports"] = [spec.render() for spec in proposal.add]
        write_json(directory / "proposal.json", {
            "path": str(relative), "module": module, "source_sha256": source_hash,
            "native_header": native, "analysis": proposal.evidence,
            "removed_imports": result["removed_imports"], "added_imports": result["added_imports"],
        })
        result["proposal_receipt"] = file_pin(directory / "proposal.json", tools.file_cache)
        verify_saved_proposal(result, tools)
        changed = rewrite_imports(original, header, proposal.remove, proposal.add)
        if changed == original:
            if sha256(source) != source_hash:
                raise ValueError("Tracked source changed during import analysis")
            result["status"] = "no_change"
            if not header.is_module:
                result["retained_imports_reason"] = "Legacy imports re-export transitive dependencies"
            return result
        additions = {spec.module for spec in proposal.add}
        arts = metadata.get("importArts")
        if not isinstance(arts, dict):
            raise ValueError("Lake setup has no import artifact map")
        if any(module != "Init" and module not in arts for module in additions):
            raise ValueError("Proposed imports require new setup metadata")
        (directory / "original.lean").write_bytes(original)
        (directory / "candidate.lean").write_bytes(changed)
        write_json(directory / "native-header.json", native)
        result["native_header"] = file_pin(directory / "native-header.json", tools.file_cache)
        patch = b"".join(difflib.diff_bytes(
            difflib.unified_diff, original.splitlines(keepends=True),
            changed.splitlines(keepends=True), fromfile=("a/" + str(relative)).encode(),
            tofile=("b/" + str(relative)).encode(),
        ))
        (directory / "proposal.patch").write_bytes(patch)
        result["proposal_patch"] = str(directory / "proposal.patch")
        result["proposal_patch_sha256"] = sha256(directory / "proposal.patch")
        if sha256(setup) != result["setup_sha256"]:
            raise ValueError("Production setup changed during import analysis")
        result["baseline"] = compile_arm(tools, relative, setup, directory / "baseline",
                                         artifact_roots[0] if artifact_roots else None, original,
                                         header_is_module=header.is_module)
        before = (None if defer_snapshots else
                  snapshot_arm(tools, module, relative, directory / "baseline",
                               cast(dict[str, object], result["baseline"])))
        if (tools.output / "transaction.json").exists():
            raise ValueError("Legacy source recovery is incomplete")
        if sha256(source) != source_hash:
            raise ValueError("Tracked source changed during baseline compilation")
        result["candidate"] = compile_arm(tools, relative, setup, directory / "candidate",
                                          artifact_roots[1] if artifact_roots else None, changed,
                                          header_is_module=header.is_module)
        result["candidate_sha256"] = hashlib.sha256(changed).hexdigest()
        if sha256(source) != source_hash:
            raise ValueError("Tracked source changed during candidate compilation")
        if sha256(setup) != result["setup_sha256"]:
            raise ValueError("Production setup changed between compile arms")
        if defer_snapshots:
            result["status"] = "compiled"
            return result
        after = snapshot_arm(tools, module, relative, directory / "candidate",
                             cast(dict[str, object], result["candidate"]))
        if before is None:
            raise ValueError("Missing baseline declaration snapshot")
        differences = compare_snapshots(before, after)
        result["declaration_differences"] = differences
        if differences:
            raise ValueError("Candidate changed owned declarations or axiom dependencies")
        if sha256(source) != source_hash:
            raise ValueError("Tracked source changed during declaration verification")
        result["declaration_count"] = before["declaration_count"]
        result["probe_private_loaded_modules_before"] = before["loaded_module_count"]
        result["probe_private_loaded_modules_after"] = after["loaded_module_count"]
        write_json(directory / "owned-before.json", before)
        write_json(directory / "owned-after.json", after)
        result["owned_before_sha256"] = sha256(directory / "owned-before.json")
        result["owned_after_sha256"] = sha256(directory / "owned-after.json")
        verify_saved_candidate(result, tools.output, tools)
        result["status"] = "verified"
    except (ValueError, OSError) as error:
        result["status"] = "blocked"
        result["error"] = str(error)
    finally:
        write_json(directory / "result.json", result)
    return result


def optimize_batch(tools: Tools, rows: list[dict[str, object]],
                   headers: dict[str, dict[str, object]], proposals: dict[str, Proposal],
                   prepared: dict[str, dict[str, object]], directory: Path
                   ) -> dict[str, dict[str, object]]:
    directory = directory / "attempts" / str(time.time_ns())
    directory.mkdir(parents=True, exist_ok=False)
    results = {}
    for row in rows:
        name = str(row["path"])
        target = directory / Path(name).with_suffix("")
        roots = (target / "baseline/artifacts", target / "candidate/artifacts")
        result = optimize_one(tools, row, headers[name], proposals[name], prepared[name],
                              defer_snapshots=True, artifact_roots=roots)
        results[name] = result
        if (tools.output / "transaction.json").exists():
            for deferred in results.values():
                if deferred["status"] == "compiled":
                    deferred["status"] = "blocked"
                    deferred["error"] = "Deferred snapshots stopped for an unrecovered source transaction"
                    write_json(Path(str(deferred["attempt_directory"])) / "result.json", deferred)
            return results
    ready = [row for row in rows if results[str(row["path"])]["status"] == "compiled"]
    groups: list[list[dict[str, object]]] = []
    for row in ready:
        for group in groups:
            proposed = [*group, row]
            if all(compatible_snapshot_group(tools, proposed,
                   {str(member["path"]): cast(dict[str, object], results[str(member["path"])][arm])
                    for member in proposed}) for arm in ("baseline", "candidate")):
                group.append(row)
                break
        else:
            groups.append([row])
    for index, group in enumerate(groups):
        snapshots = {}
        try:
            for arm in ("baseline", "candidate"):
                compilations = {str(row["path"]): cast(dict[str, object], results[str(row["path"])][arm])
                                for row in group}
                roots = {name: Path(str(compilation["artifact_root"])) for name, compilation in compilations.items()}
                first_root = next(iter(roots.values()))
                target = directory / "snapshots" / str(index) / arm if len(group) > 1 else first_root.parent
                snapshots[arm] = snapshot_batch(tools, group, roots if len(group) > 1 else first_root,
                                                target, compilations)
        except (ValueError, OSError) as error:
            if len(group) > 1:
                failure_receipt = snapshot_failure_receipt(
                    tools, directory, index, group, error)
                for row in group:
                    result = results[str(row["path"])]
                    result["shared_snapshot_failure"] = failure_receipt
                    for arm in ("baseline", "candidate"):
                        compilation = cast(dict[str, object], result[arm])
                        for field in tuple(compilation):
                            if field.startswith("snapshot_"):
                                del compilation[field]
                groups.extend([row] for row in group)
                continue
            for row in group:
                result = results[str(row["path"])]
                result.update(status="blocked", error=str(error))
                write_json(Path(str(result["attempt_directory"])) / "result.json", result)
            continue
        for row in group:
            module, name = str(row["module"]), str(row["path"])
            result = results[name]
            try:
                before, after = snapshots["baseline"][module], snapshots["candidate"][module]
                differences = compare_snapshots(before, after)
                result["declaration_differences"] = differences
                if differences:
                    raise ValueError("Candidate changed owned declarations or axiom dependencies")
                target = Path(str(result["attempt_directory"]))
                write_json(target / "owned-before.json", before)
                write_json(target / "owned-after.json", after)
                result["owned_before_sha256"] = sha256(target / "owned-before.json")
                result["owned_after_sha256"] = sha256(target / "owned-after.json")
                result["declaration_count"] = before["declaration_count"]
                result["probe_private_loaded_modules_before"] = before["loaded_module_count"]
                result["probe_private_loaded_modules_after"] = after["loaded_module_count"]
                result["probe_private_loaded_modules_scope"] = "whole_batch"
                verify_saved_candidate(result, tools.output, tools)
                result["status"] = "verified"
            except (ValueError, OSError) as error:
                result["status"] = "blocked"
                result["error"] = str(error)
            finally:
                write_json(Path(str(result["attempt_directory"])) / "result.json", result)

    return results


SourceIdentity = tuple[int, int, int, int, int, int]
SourceCache = dict[str, tuple[str, SourceIdentity]]
# A path's own `lstat` identity and that of the file it resolves to (see `path_state`).
PathState = tuple[SourceIdentity, SourceIdentity | None]


def source_identity(path: Path) -> SourceIdentity:
    metadata = path.stat()
    return (metadata.st_dev, metadata.st_ino, metadata.st_ctime_ns,
            metadata.st_mtime_ns, metadata.st_size, metadata.st_mode)


def validate_inventory_sources(root: Path, rows: list[dict[str, object]],
                               cache: SourceCache | None = None) -> None:
    for row in rows:
        name = str(row["path"])
        source = source_path(root, name)
        expected = cast(str, row["source_sha256"])
        before = source_identity(source)
        if cache is not None and cache.get(name) == (expected, before):
            continue
        if sha256(source) != row["source_sha256"]:
            raise ValueError(f"Inventory source hash changed: {source}")
        if source_identity(source) != before:
            raise ValueError(f"Inventory source changed while hashing: {source}")
        if cache is not None:
            cache[name] = (expected, before)


def select_inventory(rows: list[dict[str, object]], requested: list[str]
                     ) -> list[dict[str, object]]:
    if not requested:
        return rows
    selected = set(requested)
    rows = [row for row in rows if row["path"] in selected]
    if {row["path"] for row in rows} != selected:
        raise ValueError("Some requested files are absent from the frozen inventory")
    return rows


def load_inventory(root: Path, manifest: Path | None,
                   requested: list[str], cache: SourceCache | None = None
                   ) -> list[dict[str, object]]:
    if manifest is None:
        raise ValueError("A frozen manifest with source hashes and read-only scopes is required")
    rows = [json.loads(line) for line in manifest.read_text().splitlines() if line]
    for row in rows:
        validate_manifest_row(row)
    if not rows or len({row["path"] for row in rows}) != len(rows):
        raise ValueError("Empty inventory or duplicate source paths")
    if {row["path"] for row in rows} != set(tracked_sources(root)):
        raise ValueError("Frozen inventory must cover all Git-tracked Lean sources")
    validate_inventory_sources(root, rows, cache)
    for row in rows:
        source = source_path(root, str(row["path"]))
        with source.open("rb") as stream:
            generated = is_generated_source(stream.readline() + stream.readline())
        if generated:
            row["analysis_status"] = "generated_readonly"
    rows.sort(key=lambda row: (cast(int, row.get("topological_index", 0)), str(row["path"])))
    return select_inventory(rows, requested)


def native_headers(tools: Tools, rows: list[dict[str, object]]) -> dict[str, dict[str, object]]:
    headers: dict[str, dict[str, object]] = {}
    with (tools.output / "native-headers.jsonl").open("w", encoding="utf-8") as journal:
        for offset in range(0, len(rows), 256):
            batch = rows[offset:offset + 256]
            identities = {str(row["path"]): source_identity(source_path(tools.root, str(row["path"])))
                          for row in batch}
            label = tools.output / "headers" / str(offset)
            command = tools.run(
                [str(tools.lean), tools.lean_thread_argument, "--run", str(tools.helpers / "header.lean"),
                 *(str(source_path(tools.root, str(row["path"]))) for row in batch)], label,
            )
            require_completion(command)
            if command["exit_code"] not in (0, 1):
                require_success(command)
            parsed = [json.loads(line) for line in
                      Path(str(label) + ".stdout").read_text().splitlines() if line]
            if len(parsed) != len(batch):
                raise ValueError(f"Header batch returned {len(parsed)} of {len(batch)} records")
            for row, header in zip(batch, parsed):
                relative = str(row["path"])
                if Path(str(header.get("path"))).resolve() != source_path(tools.root, relative):
                    raise ValueError("Native header output order or source identity changed")
                if header.get("status") == "parsed":
                    verify_header(header, source_path(tools.root, relative).read_bytes(), Counter())
                if source_identity(source_path(tools.root, relative)) != identities[relative]:
                    raise ValueError(f"Native header source changed during parsing: {relative}")
                header["relative_path"] = relative
                header["source_sha256"] = row["source_sha256"]
                headers[relative] = header
                journal.write(json.dumps(header, ensure_ascii=False) + "\n")
            journal.flush()
    return headers


def cached_headers(root: Path, path: Path, rows: list[dict[str, object]]
                   ) -> dict[str, dict[str, object]]:
    requested = {str(row["path"]): row for row in rows}
    headers: dict[str, dict[str, object]] = {}
    with path.open(encoding="utf-8") as stream:
        for line in stream:
            header = json.loads(line)
            name = header.get("relative_path")
            if name not in requested:
                continue
            if name in headers or header.get("source_sha256") != requested[name]["source_sha256"]:
                raise ValueError("Cached header identity changed or was duplicated")
            source = source_path(root, name).read_bytes()
            if header.get("status") == "parsed":
                verify_header(header, source, Counter())
            elif header.get("status") not in ("parse_error", "invalid_header_syntax", "io_error"):
                raise ValueError("Unknown cached native header status")
            elif (header.get("status") != "io_error" and
                  header.get("source_utf8_bytes") != len(source)):
                raise ValueError("Cached failed header byte count changed")
            headers[name] = header
    if headers.keys() != requested.keys():
        raise ValueError("Cached header inventory is incomplete")
    return headers


def verify_resume_executables(run: Path, lake: Path, lean: Path, time_binary: Path) -> None:
    if not run.exists():
        return
    saved = read_json(run)
    message = "Resume inputs, compiler, or backend bytes changed"
    try:
        configured = {"compiler": lean, "lake_launcher": lake.resolve(), "time_binary": time_binary}
        for key, path in configured.items():
            if saved.get(key) != str(path) or saved.get(key + "_sha256") != sha256(path):
                raise ValueError(message)
        if (saved.get("compiler_launcher") != str(lean.resolve()) or
                saved.get("time_binary_resolved") != str(time_binary.resolve())):
            raise ValueError(message)
        for key in ("compiler_binary", "lake_binary"):
            value = saved.get(key)
            if not isinstance(value, str):
                raise ValueError(message)
            path = Path(value)
            if (not path.is_absolute() or path.resolve() != path or
                    saved.get(key + "_sha256") != sha256(path)):
                raise ValueError(message)
    except (OSError, RuntimeError) as error:
        raise ValueError(message) from error


def verify_resume_thread_settings(run: Path, lean_threads: int, lake_jobs: int) -> None:
    """Reject changed concurrency before any child runs or Lake config is written."""
    if not run.exists():
        return
    saved = read_json(run)
    requested = {"lean_threads": lean_threads, "lake_scheduler_threads": lake_jobs}
    if any(type(saved.get(key)) is not int or saved.get(key) != value
           for key, value in requested.items()):
        raise ValueError(
            "Resume thread settings differ from the saved run: saved --lean-threads "
            f"{saved.get('lean_threads')!r} and --lake-jobs {saved.get('lake_scheduler_threads')!r}, "
            f"requested {lean_threads} and {lake_jobs}")


def run_headers(tools: Tools, rows: list[dict[str, object]], supplied: Path | None,
                identity: dict[str, object]) -> dict[str, dict[str, object]]:
    run = tools.output / "run.json"
    generated = tools.output / "native-headers.jsonl"
    saved = read_json(run) if run.exists() else None
    if saved is not None:
        if supplied is None:
            expected = saved.get("generated_headers_sha256")
            if (not isinstance(expected, str) or not generated.is_file() or
                    sha256(generated) != expected):
                raise ValueError("Generated native header cache is missing or changed")
            identity["generated_headers_sha256"] = expected
        if saved != identity:
            raise ValueError("Resume inputs, compiler, or backend bytes changed")
    else:
        write_json(run, identity)
    headers = (cached_headers(tools.root, supplied, rows) if supplied is not None else
               cached_headers(tools.root, generated, rows) if saved is not None else
               native_headers(tools, rows))
    if supplied is None:
        digest = sha256(generated)
        if saved is not None and digest != saved["generated_headers_sha256"]:
            raise ValueError("Generated native header cache changed during validation")
        identity["generated_headers_sha256"] = digest
    elif sha256(supplied) != identity["headers_input_sha256"]:
        raise ValueError("Supplied native header cache changed during validation")
    return headers


def analyze_batch(tools: Tools, rows: list[dict[str, object]],
                  headers: dict[str, dict[str, object]], directory: Path
                  ) -> dict[str, Proposal]:
    modules = [str(row["module"]) for row in rows]
    inputs = analysis_inputs(tools, rows)
    saved = directory / "analysis.json"
    evidence = None
    if saved.exists():
        cached = read_json(saved)
        old_inputs = cached.get("inputs")
        if (not isinstance(old_inputs, dict) or not isinstance(old_inputs.get("sources"), dict) or
                not isinstance(old_inputs.get("compiled_inputs"), dict)):
            raise ValueError("Saved dependency analysis has no input identity")
        old_sources = old_inputs["sources"]
        command, output = read_analysis(tools, cached.get("evidence"))
        if (any(str(row["path"]) in old_sources and
                old_sources[str(row["path"])] != row["source_sha256"] for row in rows) or
                any(old_inputs.get(key) != value for key, value in inputs.items()
                    if key not in ("sources", "compiled_inputs")) or
                cached.get("command") != command or
                cast(dict[str, object], cached["evidence"]).get("inputs") != old_inputs):
            raise ValueError("Saved dependency analysis inputs or output bytes changed")
        reusable = False
        try:
            verify_shake_inputs(tools, old_inputs)
            reusable = True
        except (ValueError, OSError):
            pass
        if (reusable and (cached.get("error") is None or len(old_sources) > 1) and
               all(str(row["path"]) in old_sources and
               old_inputs["compiled_inputs"].get(str(row["path"])) == inputs["compiled_inputs"][str(row["path"])]
               for row in rows)):
            evidence = cast(dict[str, object], cached["evidence"])
    fresh = evidence is None
    if fresh:
        argv = tools.lake_command("shake", "--force", "--explain", "--add-public")
        for module in modules:
            argv.extend(("--only", module))
        label = directory / "analyses" / str(time.time_ns()) / "shake"
        label.parent.mkdir(parents=True)
        tools.run([*argv, *modules], label)
        if analysis_inputs(tools, rows) != inputs:
            raise ValueError("Compiled inputs changed during Shake analysis")
        evidence = analysis_evidence(tools, label, "shake", inputs)
        command, output = read_analysis(tools, evidence)
    proposals = {}
    for row in rows:
        source = source_path(tools.root, str(row["path"]))
        decode_header(headers[str(row["path"])], source.read_bytes())
        try:
            parsed = parse_shake_output(output, cast(int, command["exit_code"]), source, tools.root)
        except ValueError as error:
            if fresh:
                write_json(saved, {
                    "command": command, "module_count": len(rows),
                    "inputs": inputs, "evidence": evidence,
                    "proposal_count": 0, "error": str(error),
                })
            raise ShakeAnalysisError(str(error), cast(dict[str, object], evidence)) from error
        proposals[str(row["path"])] = Proposal(parsed.remove, parsed.add, evidence)
    if fresh:
        write_json(saved, {
            "command": command, "module_count": len(rows),
            "inputs": inputs, "evidence": evidence,
            "proposal_count": sum(bool(proposal.remove or proposal.add)
                                  for proposal in proposals.values()),
        })
    return proposals


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", help="Tracked Lean paths; defaults to the full inventory")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path,
                        help="Frozen JSONL inventory, including read-only scopes")
    parser.add_argument("--headers", type=Path,
                        help="Previously checked header JSONL with relative_path/source_sha256")
    parser.add_argument("--lake", type=Path, default=shutil.which("lake"))
    parser.add_argument("--time", type=Path, default=shutil.which("gtime") or "/usr/bin/time",
                        help="GNU time executable used for compile measurements")
    parser.add_argument("--timeout", type=int, default=840, help="Maximum seconds per child command")
    parser.add_argument("--batch-size", type=int, default=128,
                        help="Share one official shake pass across this many prepared targets; compatible members of a batch also share one snapshot process per arm (group loaded-module counts), with singleton snapshot fallback after a joint failure")
    parser.add_argument("--max-batches", type=int,
                        help="Stop at a saved batch checkpoint for bounded worker invocations")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--retry-blocked", action="store_true",
                        help="Retry failed files when resuming the same frozen inputs")
    parser.add_argument("--lean-threads", type=thread_count_argument, default=DEFAULT_LEAN_THREADS,
                        help="Threads for each Lean compiler or helper process, including "
                             "root-package modules Lake builds (default: %(default)s)")
    parser.add_argument("--lake-jobs", type=thread_count_argument, default=DEFAULT_LAKE_JOBS,
                        help="Concurrent Lake build jobs, set through LEAN_NUM_THREADS "
                             "(default: %(default)s)")
    options = parser.parse_args()
    root, output = options.root.resolve(), options.output.resolve()
    if (options.lake is None or options.timeout <= 0 or options.batch_size <= 0 or
            (options.max_batches is not None and options.max_batches <= 0)):
        parser.error("A pinned Lake executable and a positive timeout are required")
    output.mkdir(parents=True, exist_ok=True)
    if (any((output / name).exists() for name in ("run.json", "results.jsonl", "inputs", LAKE_GROWTH_DIRECTORY,
                                                   LAKE_CUSTODY_DIRECTORY)) and not options.resume):
        parser.error("Output already contains a run; use --resume or a new directory")
    def interrupted(signum: int, frame: object) -> None:
        raise KeyboardInterrupt(f"Received signal {signum}")
    signal.signal(signal.SIGTERM, interrupted)
    lock_path = root / ".lake/import-optimizer.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        recover_source_edit(root, output / "transaction.json")
        if (output / "results.jsonl").exists() and not (output / "run.json").exists():
            raise ValueError("Refusing a result journal without its original run identity")
        # Before any child process: an interrupted preparation's effects were never checked.
        refuse_interrupted_preparation(output)
        source_cache: SourceCache = {}
        inventory = load_inventory(root, options.manifest, [], source_cache)
        rows = select_inventory(inventory, options.files)
        lake = options.lake.absolute()
        lean = lake.with_name("lean")
        time_binary = options.time.absolute()
        verify_resume_executables(output / "run.json", lake, lean, time_binary)
        verify_resume_thread_settings(output / "run.json", options.lean_threads, options.lake_jobs)
        # Before any child process, and whatever the journal holds: every root-package artifact an
        # earlier invocation recorded as Lake growth or pinned as a compilation input must still have
        # its receipt. The identities hashed here become this process's custody below.
        recorded_growth = read_lake_growth(output)
        saved_receipts = saved_root_receipts(root, output, recorded_growth, read_lake_growth(output, "rewritten"))
        if saved_receipts and not (output / "run.json").exists():
            raise ValueError("Refusing saved artifact receipts without their original run identity")
        verify_saved_root_receipts(saved_receipts, source_cache)
        try:
            version = subprocess.check_output([str(time_binary), "--version"], stderr=subprocess.STDOUT)
        except (OSError, subprocess.CalledProcessError) as error:
            raise ValueError("GNU time is required before starting dependency analysis") from error
        if b"GNU" not in version:
            raise ValueError("The measurement executable is not GNU time")
        helpers = Path(__file__).resolve().parent / "import_optimizer"
        lake_config = bounded_lake_config(root, options.lean_threads)
        environment = dict(os.environ)
        environment["PATH"] = str(lake.parent) + os.pathsep + environment.get("PATH", "")
        environment["LEAN_NUM_THREADS"] = str(options.lake_jobs)
        # Pin the Lake manifest before `lake env` runs: the captured
        # LEAN_PATH is derived from the manifest Lake reads, so the
        # bytes authorizing package roots must be the pre-capture
        # bytes. A rewrite during/after environment capture is
        # rejected below instead of being parsed at Tools time.
        lake_manifest_pinned = capture_lake_manifest_bytes(root)
        env_command = run_command(
            [str(lake), "--no-cache", "-f", str(lake_config), "env", sys.executable, "-c",
             "import json,os; keys=('LAKE','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','PATH'); "
             "print(json.dumps({k:os.environ[k] for k in keys if k in os.environ}))"],
            root, output / "environment", environment, options.timeout,
        )
        require_success(env_command)
        augmented = read_json(output / "environment.stdout")
        if any(not isinstance(value, str) for value in augmented.values()):
            raise ValueError("Lake returned an invalid process environment")
        if not augmented.get("LAKE"):
            raise ValueError("Lake did not report its native executable")
        environment.update(cast(dict[str, str], augmented))
        verify_lake_manifest_bytes(root, lake_manifest_pinned)
        tools = Tools(root, output, lake, lean, helpers, environment, options.timeout,
                      time_binary, lake_config, lean_threads=options.lean_threads,
                      lake_jobs=options.lake_jobs, file_cache=source_cache,
                      lake_manifest_bytes={
                          root / "lake-manifest.json": lake_manifest_pinned})
        # Independently bind the captured environment to the pinned
        # graph (covers a manifest rename/restore during `lake env`,
        # which before/after byte checks cannot observe).
        validate_captured_environment(tools)
        record_root_custody(tools, saved_receipts.values())
        unheld = sorted(set(saved_receipts) - set(tools.root_custody))
        if unheld:
            raise ValueError(f"Saved root-package artifact changed before custody was taken: {unheld[0]}")
        verify_root_custody(tools, {path: tools.root_custody[path] for path in saved_receipts})
        compiler_binary = (Path(environment.get("LEAN_SYSROOT", str(lean.parent.parent))) /
                           "bin/lean").resolve()
        lake_launcher = lake.resolve()
        lake_binary = Path(cast(str, augmented["LAKE"])).resolve()
        identity: dict[str, object] = {
            "root": str(root), "optimizer_sha256": sha256(Path(__file__)),
            "manifest_validator_sha256": sha256(Path(__file__).with_name("generate_import_inventory.py")),
            "sources": {str(row["path"]): row["source_sha256"] for row in rows},
            "manifest_sha256": sha256(options.manifest),
            "backend_sha256": {name: sha256(helpers / name) for name in
                               ("header.lean", "declarations.lean", "declarations_batch.lean", "private_imports.lean", "legacy.lean")
                               if (helpers / name).is_file()},
            "project_pins": {name: sha256(root / name) for name in
                             ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "atlas.lock.json")
                             if name != "atlas.lock.json" or (root / name).is_file()},
            "compiler": str(lean), "compiler_sha256": sha256(lean), "lean_threads": tools.lean_threads,
            "compiler_launcher": str(lean.resolve()),
            "compiler_binary": str(compiler_binary), "compiler_binary_sha256": sha256(compiler_binary),
            "lake_launcher": str(lake_launcher), "lake_launcher_sha256": sha256(lake_launcher),
            "lake_binary": str(lake_binary), "lake_binary_sha256": sha256(lake_binary),
            "lake_scheduler_threads": tools.lake_jobs, "effective_lake_config_sha256": sha256(lake_config),
            "time_binary": str(time_binary), "time_binary_sha256": sha256(time_binary),
            "time_binary_resolved": str(time_binary.resolve()),
            "headers_input_sha256": sha256(options.headers) if options.headers else None,
            "generated_headers_sha256": None,
            "consumer_validation": "not_run", "global_optimality": "not_claimed",
        }
        headers = run_headers(tools, rows, options.headers, identity)
        validate_inventory_sources(root, inventory, source_cache)
        write_json(output / "run.json", identity)
        broad = [row for row in rows
                 if headers[str(row["path"])].get("status") == "parsed"
                 and not row.get("direct_local_dependencies")
                 and any(spec.spec.module == "Mathlib" for spec in
                         decode_header(headers[str(row["path"])],
                                       source_path(root, str(row["path"])).read_bytes()).imports)]
        broad.sort(key=lambda row: (cast(int, row.get("bytes", 0)), str(row["path"])))
        broad_paths = {row["path"] for row in broad}
        rows = [*broad, *(row for row in rows if row["path"] not in broad_paths)]
        completed: dict[str, dict[str, object]] = {}
        journal_path = output / "results.jsonl"
        if options.resume and journal_path.exists():
            completed = read_journal(journal_path, cast(dict[str, object], identity["sources"]))
            modules_by_path = {str(row["path"]): row["module"] for row in rows}
            growth = _recorded_lake_growth.set(recorded_growth)
            try:
                with analysis_validation_phase(tools):
                    for name, result in completed.items():
                        if result.get("module") != modules_by_path[name]:
                            raise ValueError("Result journal module identity differs from the frozen manifest")
                        if result["status"] == "verified":
                            verify_saved_candidate(result, output, tools)
                        elif result["status"] == "no_change":
                            verify_saved_no_change(result, tools)
            finally:
                _recorded_lake_growth.reset(growth)
        readonly = READONLY_STATUSES
        with journal_path.open("a", encoding="utf-8") as journal:
            processed_batches = 0
            skipped = {"verified", "no_change", "readonly"}
            if not options.retry_blocked:
                skipped.add("blocked")
            for offset in range(0, len(rows), options.batch_size):
                if options.max_batches is not None and processed_batches >= options.max_batches:
                    break
                batch = [row for row in rows[offset:offset + options.batch_size]
                         if completed.get(str(row["path"]), {}).get("status")
                         not in skipped]
                if not batch:
                    continue
                validate_inventory_sources(root, inventory, source_cache)
                processed_batches += 1
                directory = output / "batches" / str(offset)
                prepared: dict[str, dict[str, object]] = {}
                failures: dict[str, str] = {}
                modern = []
                eligible = []
                for row in batch:
                    name = str(row["path"])
                    if row.get("analysis_status") in readonly:
                        continue
                    if headers[name].get("status") != "parsed":
                        failures[name] = "Lean could not parse the original header"
                        continue
                    eligible.append(row)
                if eligible:
                    preparation = directory / "preparations" / str(time.time_ns())
                    preparation.mkdir(parents=True, exist_ok=False)
                    try:
                        build = run_lake_preparation(tools, tools.lake_command(
                            "build", *("+" + str(row["module"]) for row in eligible)), preparation / "prepare",
                            local_dependency_closure(inventory, {str(row["module"]) for row in eligible}))
                    except ValueError as error:
                        for row in eligible:
                            failures[str(row["path"])] = str(error)
                        eligible = []
                    for row in eligible:
                        name = str(row["path"])
                        try:
                            require_completion(build)
                            gate = build if build["exit_code"] == 0 else tools.run(
                                tools.lake_command("--no-build", "build", "+" + str(row["module"])),
                                preparation / "prepare-gates" / Path(name).with_suffix(""))
                            require_success(gate)
                            artifact_receipt(root / ".lake/build/lib/lean", Path(name))
                        except ValueError as error:
                            failures[name] = str(error)
                            continue
                        prepared[name] = gate
                        if headers[name].get("is_module"):
                            modern.append(row)
                proposals: dict[str, Proposal] = {}
                shared_analysis_failure = None
                shared_analysis_paths: set[str] = set()
                if modern:
                    try:
                        proposals = analyze_batch(tools, modern, headers, directory)
                    except ShakeAnalysisError as error:
                        analyzed_sources = cast(dict[str, object], error.evidence["inputs"])["sources"]
                        if len(cast(dict[str, object], analyzed_sources)) == 1:
                            failures[str(modern[0]["path"])] = str(error)
                        else:
                            shared_analysis_failure = {"error": str(error), "evidence": error.evidence}
                            shared_analysis_paths = {str(row["path"]) for row in modern}
                            for row in modern:
                                name = str(row["path"])
                                try:
                                    individual = analyze_batch(
                                        tools, [row], headers,
                                        directory / "individual-analyses" / Path(name).with_suffix(""))
                                    for path, proposal in individual.items():
                                        proposals[path] = Proposal(proposal.remove, proposal.add, {
                                            **cast(dict[str, object], proposal.evidence),
                                            "shared_analysis_failure": shared_analysis_failure,
                                        })
                                except (ValueError, OSError) as individual_error:
                                    failures[name] = str(individual_error)
                    except (ValueError, OSError) as error:
                        for row in modern:
                            failures[str(row["path"])] = str(error)
                modern = [row for row in modern if str(row["path"]) not in failures]
                with analysis_validation_phase(tools):
                    modern_results = (optimize_batch(tools, modern, headers, proposals, prepared, directory)
                                      if modern else {})
                    if (output / "transaction.json").exists():
                        tools.validated_analysis_inputs["phase"].clear()
                batch_results = []
                for index, row in enumerate(batch):
                    name = str(row["path"])
                    if row.get("analysis_status") in readonly:
                        result = {**row, "status": "readonly", "consumer_validation": "not_run"}
                    elif name in failures:
                        result = {**row, "status": "blocked", "error": failures[name],
                                  "consumer_validation": "not_run"}
                    elif name in modern_results:
                        result = modern_results[name]
                    else:
                        result = optimize_one(tools, row, headers[name], proposals.get(name),
                                              prepared[name])
                    if name in shared_analysis_paths:
                        result["shared_analysis_failure"] = shared_analysis_failure
                    if (output / "transaction.json").exists():
                        if result["status"] == "blocked":
                            journal.write(json.dumps(result, ensure_ascii=False) + "\n")
                            journal.flush()
                        raise ValueError("Source recovery is incomplete; stopped before another file")
                    batch_results.append((index, row, result))
                validate_inventory_sources(root, inventory, source_cache)
                with analysis_validation_phase(tools):
                    for _, _, result in batch_results:
                        if result["status"] == "verified":
                            verify_saved_candidate(result, output, tools)
                        elif result["status"] == "no_change":
                            verify_saved_no_change(result, tools)
                for index, row, result in batch_results:
                    name = str(row["path"])
                    journal.write(json.dumps(result, ensure_ascii=False) + "\n")
                    journal.flush()
                    completed[name] = result
                    print(f"[{offset + index + 1}/{len(rows)}] {result['status']}: {name}", flush=True)
                validate_inventory_sources(root, inventory, source_cache)
                write_json(directory / "checkpoint.json", {
                    "result_count": len(completed),
                    "verified_count": sum(row["status"] == "verified" for row in completed.values()),
                    "source_edits_retained": False,
                })
        validate_inventory_sources(root, inventory, source_cache)
        summary: dict[str, object] = {
            "file_count": len(rows), "result_count": len(completed),
            "pending_count": len(rows) - len(completed),
            "status_counts": {status: sum(row["status"] == status for row in completed.values())
                              for status in ("verified", "no_change", "blocked", "readonly")},
            "consumer_validation": "not_run", "global_optimality": "not_claimed",
        }
        write_json(output / "summary.json", summary)
        print(json.dumps(summary, indent=2), flush=True)
        return 1 if any(row["status"] == "blocked" for row in completed.values()) else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as error:
        print(f"Import run failed: {error}", file=sys.stderr)
        raise SystemExit(2) from error
