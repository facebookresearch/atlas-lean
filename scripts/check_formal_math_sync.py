#!/usr/bin/env python3
"""Check and update the Formal-Math ledger in provenance/.

    scripts/check_formal_math_sync.py                      check (check.sh preflight); exit 1 on failure
    scripts/check_formal_math_sync.py --record-divergence PATH... --rationale TEXT --backport pending|<url>
    scripts/check_formal_math_sync.py --retire PATH...
    scripts/check_formal_math_sync.py --split-by-domain    convert the legacy ledger without row changes

The manifest pins a fairinternal/formal-math commit and has a row for every root-library Lean file
taken from it (see `provenance/README.md`). The check is offline, deterministic, standard library
only, and scoped to those synced files, so a pull request fails only if it touches one:

- the manifest parses: schema, upstream pin (fairinternal/formal-math at a full commit), roots, unique sorted relative paths under the roots
  (no absolute, escaping, or symlinked paths);
- `identical`, `attributed`, and `behind` rows: the file exists and its SHA-256 is
  `published_sha256`, and it is the Meta header (or, with `"header": "upstream"`, the upstream
  third-party license block), then the recorded attribution notice if any, then a body whose
  SHA-256 is `upstream_sha256` (one parser: `split_published`);
- `diverged` rows: the file exists, its SHA-256 is `published_sha256` (so a later edit refreshes the
  row and its rationale), and `rationale` and `backport` are set;
- `retired` rows: the file is absent;
- compared with the base manifest: no row disappears or changes path (a deleted synced file keeps
  its row as `retired`), and while the upstream pin is unchanged no synced row is added or changes
  its `upstream_sha256` (only a sync says what upstream contains), and a pull request may move
  the pin only with the `formal-math-sync` label (pushes and merge groups are maintainer-only). In CI the base is the push's
  `before` commit, the merge group's base, or for a pull request the merge ref's first parent,
  fetched if the checkout is shallow (unreadable fails closed); locally the merge-base with
  origin/main (including the incoming parent during a local merge), falling back to HEAD's
  first parent;
- files without a row (ATLAS-only work) are ignored; new upstream files enter at sync time.

In the sharded layout (schema 2) each row lives in one of two files under the ledger directory:
its legacy shard (`<library>.json` for a library's root modules, `<library>/<first directory>.json`
below them) or its own module file (`<library>/<module path>.lean.json`, which holds just that
row). A row recorded in both, or in any other file, fails, and so does a symlink at any depth.
Rows are compared by path, wherever they live. The writers move every row they touch into its
module file and delete a legacy shard they empty, so that two pull requests that edit
neighbouring rows no longer touch neighbouring lines of one file.

A pull request that changes or deletes a synced or diverged file records that with
`--record-divergence` or `--retire`; neither needs a Formal-Math checkout. `scripts/sync_formal_math.py` regenerates the
manifest from a Formal-Math checkout and uses the header parser defined here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_copyright import META  # noqa: E402  (the one definition of the Meta header)

SCHEMA_VERSION = 1
SHARDED_SCHEMA_VERSION = 2
MANIFEST = "provenance/formal-math-sync.json"
# Every path the manifest has had. A base commit is compared through whichever of these it has, so
# moving the manifest cannot make the base look manifest-less; add a new path here, keep old ones.
MANIFEST_PATHS = (MANIFEST,)
CHECKER = "scripts/check_formal_math_sync.py"
ROOTS = ("MathlibExt", "MathlibExtTest", "CSLibExt", "CSLibExtTest", "WantedExt")
# identical:  Meta header + body of the upstream file at `upstream.commit`; with
#             "header": "upstream", the upstream file byte for byte (its third-party license kept)
# attributed: Meta header + recorded attribution notice + that body
# behind:     header-only copy of an older upstream version (`upstream_commit`)
# diverged:   reviewed ATLAS-side difference at `published_sha256`; needs `rationale` and `backport`
# retired:    removed from ATLAS on purpose; the file must stay absent
DISPOSITIONS = ("identical", "attributed", "behind", "diverged", "retired")
SYNCED = ("identical", "attributed", "behind")
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
PLAIN_BLOCK = re.compile(r"/-(?![-!]).*?-/", re.S)
UPSTREAM_REPOSITORY = "fairinternal/formal-math"
# An attribution notice names provenance or licensing; a descriptive comment is not one.
NOTICE_WORDS = re.compile(r"Copyright|[Ll]icen[cs]e|[Aa]ttribution|Authors?:|[Pp]orted from|[Aa]dapted from|Portions")
FLT_MARKERS = ("Anthropic, PBC", "flt-regular authors")
BACKPORT = re.compile(r"pending|not-needed|https://\S+")  # the formal-math backport PR, once it exists


def sha256(data: bytes | str) -> str:
    if isinstance(data, str):
        data = data.encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def is_notice(text: str) -> bool:
    """Exactly one plain block comment that names provenance or licensing."""
    block = PLAIN_BLOCK.match(text)
    return bool(block) and block.group(0) == text and bool(NOTICE_WORDS.search(text))


def split_published(text: str, notice: str = "", header: str = "meta") -> tuple[str | None, str | None]:
    """Split an ATLAS file into its body, or explain why it is not header + notice + body.

    `header="meta"`: the file starts with the exact Meta header, then the notice if one is
    recorded; a notice is exactly one plain block comment naming provenance or licensing, never
    Lean code or a descriptive comment. `header="upstream"`: the file keeps the upstream file's own
    third-party copyright and license block (as scripts/check_copyright.py allows for code copied
    from another project); that block is part of the body, which is then the whole file. Blank
    lines after the Meta header and after the notice are separators.
    Returns (body, None) or (None, problem).
    """
    if header == "upstream":
        block = PLAIN_BLOCK.match(text)
        if notice or not block or "Meta Platforms" in block.group(0) or "Copyright" not in block.group(0) \
                or not re.search(r"[Ll]icen[cs]e", block.group(0)):
            return None, "does not start with a third-party copyright and license header"
        return text.lstrip("\n"), None  # the header is part of the upstream body, kept byte for byte
    if header != "meta":
        return None, f"unknown header kind {header!r}"
    if not text.startswith(META):
        return None, "does not start with the Meta header"
    rest = text[len(META):].lstrip("\n")
    if notice:
        if not is_notice(notice):
            return None, "recorded notice is not exactly one attribution block comment"
        if not rest.startswith(notice):
            return None, "recorded notice does not follow the Meta header"
        rest = rest[len(notice):].lstrip("\n")
    return rest, None


def leading_notice(text: str) -> str | None:
    """The attribution block comment right after the Meta header, if any."""
    if not text.startswith(META):
        return None
    block = PLAIN_BLOCK.match(text[len(META):].lstrip("\n"))
    return block.group(0) if block and is_notice(block.group(0)) else None


# Formal-Math's own header names only these copyright holders and authors (Meta, its employees,
# and the agents and models formal-math is written with); ATLAS replaces such a header with the
# Meta header. Any other holder or author is third-party: the block is part of the body and stays
# byte for byte. Derived from the leading blocks of formal-math's own files.
FORMAL_MATH_HOLDERS = ("Meta Platforms, Inc. and affiliates", "Meta Platforms, Inc", "Adam Kiezun", "Avocado",
                       "The formal-math Contributors", "Mathlib Extension Contributors")
FORMAL_MATH_AUTHORS = ("Adam Kiezun", "@akiezun", "Tsutomu Okano", "@toskua", "toskua", "Toskua",
                       "toskua-Avocado", "Avocado", "Muse", "Muse Spark", "Muse Spark 1.3", "Muse Code",
                       "Muse Code powered by Meta Muse Spark", "Metamate", "Metamate metamate-algos", "Codex",
                       "Claude Opus 5.5", "@vonbo", "Formal Math", "Codex-assisted formalization")
CODEX_AGENT = re.compile(r"Codex [A-Z][a-z]+-[0-9a-f]{4}")  # named Codex agent runs, e.g. Codex Vale-62b0
COPYRIGHT_HOLDER = re.compile(r"Copyright(?: \(c\))?(?: \d{4}(?:[-–]\d{4})?)?\.?[ \t]*([^\n]*)")


def block_authors(block: str) -> list[str]:
    """Names on the block's `Author:`, `Authors:` and `Author(s):` lines.

    E-mail addresses are dropped. A parenthetical that is all lowercase description (`(canonical
    root support)`) is dropped too; any other parenthetical is read as more names, so it cannot
    hide a third-party author."""
    names = []
    for line in re.findall(r"Author(?:s|\(s\))?:([^\n]*)", block):
        line = re.sub(r"<[^<>@\s]+@[^<>\s]+>", "", line.replace("-/", ""))
        line = re.sub(r"\(([^()]*)\)", lambda m: "" if re.fullmatch(r"[a-z0-9 \-]+", m.group(1)) else f", {m.group(1)}", line)
        names += [n.strip().strip(".\"'") for n in re.split(r",|;| and ", line)]
    return [n for n in names if n]


def is_formal_math_header(block: str) -> bool:
    """Formal-Math's own header: every copyright holder and every author is Formal-Math's own,
    and a block without a copyright line carries no license text. Third-party (or mixed) copyright,
    authorship and license blocks are part of the body and must be kept byte for byte."""
    holders = [re.sub(r"\.?\s*All rights reserved\.?$", "", h).strip().rstrip(".") for h in COPYRIGHT_HOLDER.findall(block)]
    authors = block_authors(block)
    if not holders and (not authors or re.search(r"[Ll]icen[cs]e", block)):
        return False
    return all(h in FORMAL_MATH_HOLDERS for h in holders) and \
        all(a in FORMAL_MATH_AUTHORS or CODEX_AGENT.fullmatch(a) for a in authors)


def upstream_body(text: str) -> str:
    """Formal-Math file body: the text after Formal-Math's own leading header, if any."""
    block = PLAIN_BLOCK.match(text)
    if block and is_formal_math_header(block.group(0)):
        return text[block.end():].lstrip("\n")
    return text.lstrip("\n")


def is_flt(text: str) -> bool:
    """Third-party FLT content keeps its own header; ATLAS never rewrites it."""
    block = PLAIN_BLOCK.match(text)
    return bool(block) and any(marker in block.group(0) for marker in FLT_MARKERS)


FINGERPRINT = re.compile(r"[0-9a-f]{12}")
NEAR_COPY = 0.9  # share of a retired file's distinct lines that marks a new file as its near copy


def line_fingerprint(text: str) -> list[str]:
    """Sorted short hashes of a file's distinct non-trivial lines (8+ characters once stripped).

    A retired row keeps this, so a later near copy of the retired file is still recognized."""
    return sorted({sha256(line.strip())[:12] for line in text.splitlines() if len(line.strip()) >= 8})


def retired_row(old: dict, path: str, previous_text: str | None) -> dict:
    """The retired form of a row: its provenance and fingerprints stay, so copies stay visible."""
    if old.get("disposition") == "retired":
        return dict(old)
    row = {"path": path, "disposition": "retired"}
    row.update({k: old[k] for k in ("published_sha256", "upstream_sha256", "upstream_commit") if k in old})
    if previous_text is not None:
        row["line_fingerprint"] = line_fingerprint(previous_text)
    return row


def count_rows(rows: list[dict]) -> dict[str, int]:
    counts = {d: 0 for d in DISPOSITIONS}
    for row in rows:
        counts[row["disposition"]] = counts.get(row["disposition"], 0) + 1
    return counts


def dump_manifest(manifest: dict) -> str:
    """Serialize with one row per line so each changed file is one changed line."""
    lines = ["{"]
    for key, value in manifest.items():
        if key != "rows":
            lines.append(f"  {json.dumps(key)}: {json.dumps(value, ensure_ascii=False, sort_keys=True)},")
    lines.append('  "rows": [')
    rows = manifest["rows"]
    for i, row in enumerate(rows):
        ordered = {"path": row.get("path"), **{k: row[k] for k in sorted(row) if k != "path"}}
        lines.append("    " + json.dumps(ordered, ensure_ascii=False) + ("," if i + 1 < len(rows) else ""))
    lines.append("  ]")
    lines.append("}")
    return "\n".join(lines) + "\n"


def library_files(root: Path) -> tuple[set[str], list[str]]:
    """Every `.lean` file under the root libraries, and every symlink found there."""
    files: set[str] = set()
    links: list[str] = []
    for library in ROOTS:
        top = root / library
        if top.is_symlink():
            links.append(library)
            continue
        for directory, dirs, names in os.walk(top):
            here = Path(directory)
            for name in list(dirs):
                if (here / name).is_symlink():
                    links.append((here / name).relative_to(root).as_posix())
                    dirs.remove(name)
            for name in names:
                rel = (here / name).relative_to(root).as_posix()
                if (here / name).is_symlink():
                    links.append(rel)
                elif name.endswith(".lean"):
                    files.add(rel)
    return files, sorted(links)


def path_problem(root: Path, path: object) -> str | None:
    if not isinstance(path, str) or not path:
        return "row path is not a non-empty string"
    if path.startswith("/") or PurePosixPath(path).is_absolute() or re.match(r"[A-Za-z]:", path) or "\\" in path:
        return "absolute path"
    parts = PurePosixPath(path).parts
    if ".." in parts:
        return "escaping path"
    if "." in parts or "" in path.split("/") or PurePosixPath(path).as_posix() != path:
        return "non-normalized path"
    if parts[0] not in ROOTS or not path.endswith(".lean") or len(parts) < 2:
        return "path is outside the root libraries"
    current = root
    for part in parts:
        current = current / part
        if current.is_symlink():
            return "symlinked path"
    try:
        (root / path).resolve().relative_to(root.resolve())
    except ValueError:
        return "escaping path"
    return None


def field_problems(row: dict) -> list[str]:
    """Shape of a row's fields, independent of the files on disk."""
    path, disposition = row["path"], row.get("disposition")
    if disposition not in DISPOSITIONS:
        return [f"{path}: unknown disposition {disposition!r}"]
    problems = []
    required = {"identical": ("published_sha256", "upstream_sha256"),
                "attributed": ("published_sha256", "upstream_sha256", "notice"),
                "behind": ("published_sha256", "upstream_sha256", "upstream_commit"),
                "diverged": ("published_sha256", "rationale", "backport"), "retired": ()}[disposition]
    for field in required:
        if field not in row:
            problems.append(f"{path}: {disposition} row has no {field}")
    for field in ("published_sha256", "upstream_sha256"):
        if field in row and not (isinstance(row[field], str) and SHA256.fullmatch(row[field])):
            problems.append(f"{path}: {field} is not a SHA-256 hex digest")
    if "upstream_commit" in row and not (isinstance(row["upstream_commit"], str) and COMMIT.fullmatch(row["upstream_commit"])):
        problems.append(f"{path}: upstream_commit is not a full 40-hex commit")
    for field in ("notice", "rationale", "backport"):
        if field in row and not (isinstance(row[field], str) and row[field].strip()):
            problems.append(f"{path}: {field} must be a non-empty string")
    if isinstance(row.get("backport"), str) and row["backport"].strip() and not BACKPORT.fullmatch(row["backport"]):
        problems.append(f"{path}: backport must be 'pending', 'not-needed', or an https:// URL")
    fingerprint = row.get("line_fingerprint")
    if "line_fingerprint" in row and (disposition != "retired" or not isinstance(fingerprint, list)
                                      or not all(isinstance(h, str) and FINGERPRINT.fullmatch(h) for h in fingerprint)
                                      or fingerprint != sorted(set(fingerprint))):
        problems.append(f"{path}: line_fingerprint must be a sorted list of 12-hex line hashes on a retired row")
    if "notice" in row and disposition not in ("attributed", "behind"):
        problems.append(f"{path}: only attributed or behind rows record a notice")
    if "header" in row and (disposition not in ("identical", "behind") or row["header"] != "upstream"):
        problems.append(f"{path}: header field is only for identical or behind rows that keep the upstream header")
    return problems


def file_problems(root: Path, row: dict) -> list[str]:
    """What the files on disk must satisfy for this row."""
    path, disposition = row["path"], row["disposition"]
    target = root / path
    if disposition == "retired":
        return [f"{path}: retired row, but the file exists"] if target.exists() else []
    if not target.is_file():
        return [f"{path}: {disposition} file is missing"]
    data = target.read_bytes()
    if sha256(data) != row["published_sha256"]:
        what = "diverged file changed since its rationale was recorded" if disposition == "diverged" else "synced file changed"
        return [f"{path}: {what} (sha256 {sha256(data)}, manifest {row['published_sha256']})"]
    if disposition == "diverged":
        return []
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return [f"{path}: header-only violation: file is not UTF-8"]
    body, why = split_published(text, row.get("notice", ""), row.get("header", "meta"))
    if why:
        return [f"{path}: header-only violation: {why}"]
    if sha256(body) != row["upstream_sha256"]:
        return [f"{path}: header-only violation: body after the header does not hash to upstream_sha256"]
    return []


def shard_directory(manifest_path: Path) -> Path:
    """The sibling directory containing the v2 ledger's row files."""
    return manifest_path.with_suffix(".d")


def shard_path(manifest_path: Path, path: str) -> Path:
    """Route a source path by library and first directory, with separate root modules."""
    if not isinstance(path, str) or "\\" in path or "\x00" in path:
        raise ValueError(f"invalid source path: {path!r}")
    parts = path.split("/")
    if (len(parts) < 2 or parts[0] not in ROOTS or not path.endswith(".lean")
            or any(part in ("", ".", "..") for part in parts)):
        raise ValueError(f"invalid source path: {path!r}")
    if any(part.endswith(".lean") for part in parts[:-1]):  # its shard would be named like a module file
        raise ValueError(f"invalid source path: {path!r} has a directory named like a Lean file")
    directory = shard_directory(manifest_path)
    if len(parts) == 2:
        return directory / f"{parts[0]}.json"
    return directory / parts[0] / f"{parts[1]}.json"


def module_path(manifest_path: Path, path: str) -> Path:
    """A row's own module file, `<library>/<module path>.lean.json`, which holds only that row.
    No legacy shard name ends in `.lean.json`: `shard_path` rejects a directory named `X.lean`."""
    shard_path(manifest_path, path)  # the same validation
    return shard_directory(manifest_path) / f"{path}.json"


def module_rows(manifest_path: Path, manifest: dict, files) -> set[str]:
    """The paths whose rows the ledger files `files` keep in module files."""
    if manifest["schema_version"] != SHARDED_SCHEMA_VERSION:
        return set()
    return {row["path"] for row in manifest["rows"] if module_path(manifest_path, row["path"]) in files}


def unique_fields(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def manifest_documents(manifest_path: Path, manifest: dict, modules=frozenset()) -> dict[Path, str]:
    """Serialize the logical ledger to its on-disk layout without changing any row: a row whose
    path is in `modules` to its module file, any other to its legacy shard."""
    version = manifest["schema_version"]
    if version == SCHEMA_VERSION:
        return {manifest_path: dump_manifest(manifest)}
    if version != SHARDED_SCHEMA_VERSION:
        raise ValueError(f"unsupported manifest schema_version: {version!r}")
    groups: dict[Path, list[dict]] = {}
    for row in manifest["rows"]:
        home = module_path if row["path"] in modules else shard_path
        groups.setdefault(home(manifest_path, row["path"]), []).append(row)
    header = {key: value for key, value in manifest.items() if key != "rows"}
    documents = {manifest_path: json.dumps(header, indent=2, ensure_ascii=False, sort_keys=True) + "\n"}
    for shard, rows in sorted(groups.items()):
        documents[shard] = dump_manifest({"rows": sorted(rows, key=lambda row: row["path"])})
    return documents


def parse_manifest(manifest_path: Path, header: str, shards: dict[Path, str]) -> dict:
    """Assemble one logical ledger from either format, rejecting ambiguous storage."""
    manifest = json.loads(header, object_pairs_hook=unique_fields)
    if not isinstance(manifest, dict):
        raise ValueError("manifest is not a JSON object")
    version = manifest.get("schema_version")
    if type(version) is not int or version not in (SCHEMA_VERSION, SHARDED_SCHEMA_VERSION):
        raise ValueError(f"unsupported schema_version: {version!r}")
    if version == SCHEMA_VERSION:
        if shards:
            raise ValueError("monolithic manifest has a shard directory with files")
        if not isinstance(manifest.get("rows"), list):
            raise ValueError("manifest has no rows list")
        return manifest
    if "rows" in manifest:
        raise ValueError("sharded manifest metadata must not contain inline rows")
    all_rows: list[dict] = []
    homes: dict[str, Path] = {}
    for shard, text in sorted(shards.items()):
        try:
            document = json.loads(text, object_pairs_hook=unique_fields)
            if not (isinstance(document, dict) and set(document) == {"rows"}
                    and isinstance(document["rows"], list) and document["rows"]):
                raise ValueError("expected a nonempty rows list and no shard-local metadata")
            module = shard.name.endswith(".lean.json")
            if module and len(document["rows"]) != 1:
                raise ValueError("a module file holds exactly one row")
            home = module_path if module else shard_path
            paths = []
            for row in document["rows"]:
                if not isinstance(row, dict) or home(manifest_path, row.get("path")) != shard:
                    raise ValueError(f"row belongs in another shard: {row!r}")
                paths.append(row["path"])
            if paths != sorted(set(paths)):
                raise ValueError("shard rows must be sorted and unique")
            for path in paths:
                if path in homes:
                    raise ValueError(f"{path} is recorded in two files, here and in {homes[path]}")
                homes[path] = shard
            all_rows.extend(document["rows"])
        except ValueError as error:
            raise ValueError(f"{shard}: {error}") from error
    return {**manifest, "rows": sorted(all_rows, key=lambda row: row["path"])}


def worktree_shards(manifest_path: Path) -> dict[Path, str]:
    """Read every file below the ledger directory, at any depth, never through symlinks."""
    directory = shard_directory(manifest_path)
    if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
        raise ValueError(f"{directory}: shard directory is not a real directory")
    if not directory.exists():
        return {}
    shards = {}

    def read(folder: Path) -> None:  # in sorted order, depth first, so the first problem is reported
        for entry in sorted(folder.iterdir()):
            if entry.is_symlink():
                raise ValueError(f"{entry}: shard path must not go through a symlink")
            if entry.is_dir():
                read(entry)
            elif not entry.is_file() or entry.suffix != ".json":
                raise ValueError(f"{entry}: expected a regular JSON shard file")
            else:
                shards[entry] = entry.read_text(encoding="utf-8")
    read(directory)
    return shards


def write_manifest(manifest_path: Path, manifest: dict, *, paths: list[str] | None = None,
                   modules=frozenset()) -> None:
    """Write the ledger, or just the files that the edited paths leave and enter.

    In the sharded layout a row whose path is in `modules` goes to its module file, and so does
    every edited path; a legacy shard left without rows is deleted. Either every file changes or,
    on failure, none does."""
    sharded = manifest["schema_version"] == SHARDED_SCHEMA_VERSION
    if paths is not None and sharded:
        modules = set(modules) | set(paths)
    documents: dict[Path, str | None] = dict(manifest_documents(manifest_path, manifest, modules))
    if paths is not None and sharded:
        targets = {home(manifest_path, path) for path in paths for home in (shard_path, module_path)}
        documents = {target: documents.get(target) for target in targets
                     if target in documents or target.exists()}  # None: an emptied legacy shard
    # Validate and stage every changed file before replacing or deleting any ledger document.
    changes: dict[Path, tuple[bytes | None, bytes | None, int]] = {}
    for target, text in documents.items():
        absolute = target.absolute()
        if symlinked_component(Path(absolute.anchor), absolute):
            raise ValueError(f"{target}: manifest path must not go through a symlink")
        if target.exists() and not target.is_file():
            raise ValueError(f"{target}: expected a regular manifest file")
        original = target.read_bytes() if target.exists() else None
        data = None if text is None else text.encode("utf-8")
        if data != original:
            mode = stat.S_IMODE(target.stat().st_mode) if original is not None else 0o644
            changes[target] = data, original, mode
    if not changes:
        return
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".formal-math-write-", dir=manifest_path.parent))
    staged: dict[Path, tuple[Path | None, Path | None]] = {}
    replaced: list[Path] = []
    created: list[Path] = []  # directories made for new module files, removed again on failure
    keep_backups = False
    try:
        for index, (target, (data, original, mode)) in enumerate(changes.items()):
            new = None
            if data is not None:
                new = staging / f"{index}.new"
                new.write_bytes(data)
                new.chmod(mode)
            backup = None
            if original is not None:
                backup = staging / f"{index}.old"
                backup.write_bytes(original)
                backup.chmod(mode)
            staged[target] = new, backup
        recovery = {str(target): str(backup) for target, (_, backup) in staged.items()}
        (staging / "targets.json").write_text(json.dumps(recovery), encoding="utf-8")
        for target in sorted(staged, key=lambda target: (target == manifest_path, target)):
            new = staged[target][0]
            if new is None:
                target.unlink()
            else:
                missing = [parent for parent in target.parents if not parent.exists()]
                target.parent.mkdir(parents=True, exist_ok=True)
                created.extend(missing)
                os.replace(new, target)
            replaced.append(target)
    except BaseException as error:
        failures = []
        for target in reversed(replaced):
            try:
                backup = staged[target][1]
                if backup is None:
                    target.unlink()
                else:
                    os.replace(backup, target)
            except OSError as rollback_error:
                failures.append(f"{target}: {rollback_error}")
        for directory in sorted(created, key=lambda path: len(path.parts), reverse=True):
            try:
                directory.rmdir()
            except OSError as rollback_error:
                failures.append(f"{directory}: {rollback_error}")
        if failures:
            keep_backups = True
            raise OSError(f"ledger rollback failed: {'; '.join(failures)}; backups in {staging}") from error
        raise
    finally:
        if not keep_backups:
            shutil.rmtree(staging)


def load(manifest_path: Path) -> tuple[dict | None, list[str]]:
    """Parse either layout and check shared metadata. Return (logical ledger, problems)."""
    try:
        absolute = manifest_path.absolute()
        if symlinked_component(Path(absolute.anchor), absolute):
            raise ValueError("manifest path must not go through a symlink")
        if not manifest_path.is_file():
            raise ValueError("expected a regular manifest file")
        manifest = parse_manifest(manifest_path, manifest_path.read_text(encoding="utf-8"),
                                  worktree_shards(manifest_path))
    except (OSError, ValueError) as error:
        return None, [f"{manifest_path}: cannot read manifest: {error}"]
    return manifest, metadata_problems(manifest)


def metadata_problems(manifest: dict) -> list[str]:
    problems = []
    upstream = manifest.get("upstream")
    if not (isinstance(upstream, dict) and upstream.get("repository") == UPSTREAM_REPOSITORY
            and isinstance(upstream.get("commit"), str) and COMMIT.fullmatch(upstream["commit"])):
        problems.append(f"manifest: upstream must be repository {UPSTREAM_REPOSITORY!r} with a full 40-hex commit")
    if manifest.get("roots") != list(ROOTS):
        problems.append(f"manifest: roots are {manifest.get('roots')!r}, expected {list(ROOTS)!r}")
    if not isinstance(manifest.get("lean_toolchain"), str):
        problems.append("manifest: lean_toolchain is not a string")
    return problems


def manifest_rel(root: Path, manifest_path: Path) -> str:
    """The manifest's repository-relative path, derived lexically (never through symlinks)."""
    return Path(os.path.relpath(os.path.abspath(manifest_path), os.path.abspath(root))).as_posix()


def symlinked_component(root: Path, manifest_path: Path) -> str | None:
    """The first symlink on the way from the repository root to the manifest, if any."""
    current = Path(os.path.abspath(root))
    for part in Path(manifest_rel(root, manifest_path)).parts:
        current = current / part
        if current.is_symlink():
            return current.relative_to(os.path.abspath(root)).as_posix()
    return None


def check(root: Path, manifest_path: Path) -> tuple[list[str], dict[str, list[str]], int]:
    """Return (problems, suggested fixes {"record": [paths], "retire": [paths]}, row count)."""
    fixes: dict[str, list[str]] = {"record": [], "retire": []}
    link = symlinked_component(root, manifest_path)
    if link:
        return [f"{link}: the manifest path must not go through a symlink"], fixes, 0
    manifest, problems = load(manifest_path)
    if manifest is None:
        return problems, fixes, 0
    seen: set[str] = set()
    paths = []
    for index, row in enumerate(manifest["rows"]):
        if not isinstance(row, dict):
            problems.append(f"row {index}: not an object")
            continue
        path = row.get("path")
        why = path_problem(root, path)
        if why:
            problems.append(f"{path!r}: {why}")
            continue
        paths.append(path)
        if path in seen:
            problems.append(f"{path}: duplicate row")
            continue
        seen.add(path)
        shape = field_problems(row)
        problems += shape
        if shape:
            continue
        found = file_problems(root, row)
        problems += found
        if found:
            fixes["retire" if row["disposition"] != "retired" and not (root / path).exists() else "record"].append(path)
    if paths != sorted(paths):
        problems.append("manifest: rows are not sorted by path")
    # A byte-for-byte copy of a tracked file must be tracked too (no base commit needed).
    # Retired rows count too: a file retired in one PR and copied back in a later one is still caught.
    tracked = {row["published_sha256"]: row["path"] for row in manifest["rows"] if isinstance(row, dict)
               and row.get("disposition") in (*SYNCED, "diverged", "retired")
               and isinstance(row.get("published_sha256"), str)}
    retired = [(row["path"], set(row["line_fingerprint"])) for row in manifest["rows"] if isinstance(row, dict)
               and row.get("disposition") == "retired" and isinstance(row.get("line_fingerprint"), list)
               and len(row["line_fingerprint"]) >= 5]
    files, _ = library_files(root)
    for path in sorted(files - seen):
        data = (root / path).read_bytes()
        source = tracked.get(sha256(data))
        if source:
            problems.append(f"{path}: exact copy of tracked {source} but has no row; record it with --record-divergence")
            fixes["record"].append(path)
            continue
        if retired:
            lines = set(line_fingerprint(data.decode("utf-8", "replace")))
            for old_path, old_lines in retired:
                if len(old_lines & lines) >= NEAR_COPY * len(old_lines):
                    problems.append(f"{path}: near copy of retired {old_path} but has no row; record it with "
                                    "--record-divergence")
                    fixes["record"].append(path)
                    break
    return problems, fixes, len(manifest["rows"])


def git(root: Path, *args: str) -> str | None:
    """stdout of a git command in `root`, or None if it fails."""
    try:
        done = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return done.stdout.strip() if done.returncode == 0 else None


def load_revision(
    root: Path, revision: str, manifest_path: str = MANIFEST
) -> tuple[dict | None, list[str]]:
    """Load the full historical ledger from Git, checking file modes as well as contents."""
    header = Path(manifest_path)
    for parent in reversed(header.parents):
        if parent == Path("."):
            continue
        listing = git(root, "ls-tree", "--full-tree", "-z", revision, "--", parent.as_posix())
        if listing is None:
            return None, [f"cannot read {parent} in the manifest tree at {revision}"]
        if not listing:
            return None, []  # no ancestor (and hence no ledger) in this revision
        if not listing.startswith("040000 tree "):
            return None, [f"{revision}:{parent}: expected a real manifest directory"]
    directory = shard_directory(header)
    listing = git(root, "ls-tree", "--full-tree", "-r", "-z", revision, "--",
                  header.as_posix(), directory.as_posix())
    if listing is None:
        return None, [f"cannot read the manifest tree at {revision}"]
    documents = {}
    try:
        entries = []
        for line in listing.split("\0"):
            if not line:
                continue
            entry, name = line.split("\t", 1)
            mode, kind, oid = entry.split()
            if mode not in ("100644", "100755") or kind != "blob":
                raise ValueError(f"{name}: expected a regular manifest file")
            entries.append((name, oid))
        if not entries:
            return None, []
        contents = git_blobs(root, [oid for _, oid in entries])
        for index, (name, _) in enumerate(entries):
            if contents is None or contents[index] is None:
                raise ValueError(f"{name}: Git blob is missing")
            documents[Path(name)] = contents[index].decode("utf-8")
        if header not in documents:
            raise ValueError(f"{header}: missing manifest metadata file")
        manifest = parse_manifest(header, documents.pop(header), documents)
        return manifest, metadata_problems(manifest)
    except ValueError as error:
        return None, [f"{revision}:{manifest_path}: cannot read manifest: {error}"]


def git_blobs(root: Path, oids: list[str]) -> list[bytes | None] | None:
    """The contents of `oids` from one `git cat-file --batch` (None for an object that is missing
    or not a blob), or None if git fails: one process for the whole ledger, not one per file."""
    try:
        done = subprocess.run(["git", "-C", str(root), "cat-file", "--batch"], capture_output=True,
                              input="".join(f"{oid}\n" for oid in oids).encode(), timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if done.returncode != 0:
        return None
    data, position, contents = done.stdout, 0, []
    for _ in oids:
        end = data.find(b"\n", position)
        if end < 0:
            return None
        header = data[position:end].split()
        position = end + 1
        if len(header) == 3 and header[2].isdigit():  # "<oid> <type> <size>", the contents, a newline
            size = int(header[2])
            if data[position + size:position + size + 1] != b"\n":
                return None
            contents.append(data[position:position + size] if header[1] == b"blob" else None)
            position += size + 1
        else:  # "<oid> missing"
            contents.append(None)
    return contents


def last_committed_text(root: Path, path: str) -> str | None:
    """A deleted file's last committed text: from HEAD, or from before the commit that deleted it."""
    text = git(root, "show", f"HEAD:{path}")
    if text is None:
        deleting = git(root, "rev-list", "-1", "HEAD", "--", path)
        text = git(root, "show", f"{deleting}^:{path}") if deleting else None
    return None if text is None else text + "\n"


def first_parent(root: Path) -> str | None:
    """HEAD's first parent, read from the commit object (present even in a depth-1 checkout).

    In CI the checkout is the pull request's merge ref, whose first parent is the base branch."""
    commit = git(root, "cat-file", "-p", "HEAD")
    parents = [line.split()[1] for line in (commit or "").splitlines() if line.startswith("parent ")]
    return parents[0] if parents else None


SYNC_LABEL = "formal-math-sync"


def ci_event() -> dict | None:
    """The GitHub Actions event payload, or None if it cannot be read."""
    try:
        event = json.loads(Path(os.environ.get("GITHUB_EVENT_PATH", "")).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return event if isinstance(event, dict) else None


def repin_authorization(old_pin: str, pin: str) -> tuple[str | None, str | None]:
    """Whether this run may move the upstream pin: (problem, note).

    A pull request needs the `formal-math-sync` label, which only maintainers (triage or write
    access) can add. A push or merge group is already maintainer-only. A local run is allowed."""
    change = f"upstream pin changed from {old_pin[:12]} to {str(pin)[:12]}"
    if not os.environ.get("GITHUB_ACTIONS"):
        return None, f"{change}; allowed outside CI (a pull request needs the {SYNC_LABEL!r} label)"
    name = os.environ.get("GITHUB_EVENT_NAME", "")
    if name in ("push", "merge_group", "workflow_dispatch"):
        return None, f"{change} by a {name} event (maintainer-only)"
    event = ci_event()
    if name in ("pull_request", "pull_request_target") and event is not None:
        labels = (event.get("pull_request") or {}).get("labels") or []
        if any(isinstance(label, dict) and label.get("name") == SYNC_LABEL for label in labels):
            return None, f"{change}; authorized by the {SYNC_LABEL!r} label"
        return (f"manifest: {change} without the {SYNC_LABEL!r} label. A re-pin is a formal-math sync and "
                "needs a maintainer to add that label; then push a commit or close and reopen the pull request "
                "(adding a label does not start CI, and a re-run reuses the old event)."), None
    return f"manifest: {change}, but the {name or 'unknown'} event cannot authorize it (event payload unreadable)", None


def ci_base(root: Path) -> tuple[str | None, str]:
    """The base of a GitHub Actions run: (commit, where it came from).

    A push compares with the commit before the push (a multi-commit push must not hide a removal
    in an earlier commit), a merge group with its base, and a pull request with the merge ref's
    first parent."""
    event = ci_event() or {}
    name = os.environ.get("GITHUB_EVENT_NAME", "")
    if name == "push":
        before = event.get("before") if isinstance(event, dict) else None
        if isinstance(before, str) and COMMIT.fullmatch(before) and before != "0" * 40:
            return before, "the push event's before commit"
        if not event:
            return None, "the push event's before commit (event payload unreadable)"
    if name == "merge_group":
        group = event.get("merge_group") if isinstance(event, dict) else None
        sha = group.get("base_sha") if isinstance(group, dict) else None
        return (sha, "the merge group's base") if isinstance(sha, str) and COMMIT.fullmatch(sha) else \
            (None, "the merge group's base (missing from the event payload)")
    return first_parent(root), "first parent of HEAD"


def base_commit(root: Path, base: str | None,
                merge_head: str | None = None) -> tuple[str | None, str | None]:
    """The commit whose manifest this tree is compared with: (commit, None) or (None, why not)."""
    if git(root, "rev-parse", "--show-toplevel") != str(root.resolve()):
        return None, "not a git checkout"
    if base:
        commit = git(root, "rev-parse", "--verify", f"{base}^{{commit}}")
        return (commit, None) if commit else (None, f"cannot resolve --base {base}")
    if os.environ.get("GITHUB_ACTIONS"):
        candidate, source = ci_base(root)
        if candidate and git(root, "cat-file", "-e", f"{candidate}^{{commit}}") is None:
            git(root, "fetch", "--no-tags", "--depth=1", "origin", candidate)  # shallow CI checkout
        if candidate and git(root, "cat-file", "-e", f"{candidate}^{{commit}}") is not None:
            return candidate, None
        return None, f"cannot read the base commit ({source})"
    # With multiple heads, git finds the base of origin/main and their hypothetical merge.
    heads = ("HEAD", merge_head) if merge_head else ("HEAD",)
    for candidate in (git(root, "merge-base", "origin/main", *heads), first_parent(root)):
        if candidate and git(root, "cat-file", "-e", f"{candidate}^{{commit}}") is not None:
            return candidate, None
    return None, "no origin/main merge-base and no readable parent commit"


def row_transition_problems(path: str, before: dict | None, row: dict, short: str) -> list[str]:
    """With the upstream pin unchanged, a row may only stay as it was or take an allowed step:
    to `retired`; to `diverged` (keeping the base `upstream_sha256` and `upstream_commit`); or, for a diverged row, a new
    `published_sha256` with a new rationale, or a rationale/backport update, while `upstream_sha256`
    and `upstream_commit` stay the same. Synced rows are frozen: only a sync changes them."""
    disposition = row.get("disposition")
    if before is None:
        if disposition in SYNCED:
            return [f"{path}: new synced row while the upstream pin is unchanged; synced rows come "
                    "from scripts/sync_formal_math.py"]
        return []
    if row == before:
        return []
    if disposition == "retired":
        if before.get("disposition") == "retired":
            return [f"{path}: retired row changed (base {short}); a retired row keeps its provenance"]
        dropped = [k for k in ("published_sha256", "upstream_sha256", "upstream_commit") if row.get(k) != before.get(k)
                   and k in before]
        if dropped:
            return [f"{path}: retiring the row changed {', '.join(dropped)} (base {short}); --retire keeps them"]
        return []
    if disposition in SYNCED:
        fields = sorted(k for k in set(row) | set(before) if row.get(k) != before.get(k))
        return [f"{path}: synced row changed ({', '.join(fields)}) while the upstream pin is unchanged "
                f"(base {short}); record an edit with --record-divergence or a deletion with --retire"]
    if disposition != "diverged":
        return []  # check() reports an unknown disposition
    if before.get("disposition") != "diverged":
        changed = [k for k in ("upstream_sha256", "upstream_commit") if row.get(k) != before.get(k)]
        if changed:
            return [f"{path}: {', '.join(changed)} changed when the row became diverged (base {short})"]
        return []
    changed = [k for k in ("upstream_sha256", "upstream_commit") if row.get(k) != before.get(k)]
    if changed:
        return [f"{path}: diverged row changed {', '.join(changed)} while the upstream pin is unchanged "
                f"(base {short})"]
    if row.get("published_sha256") != before.get("published_sha256") and row.get("rationale") == before.get("rationale"):
        return [f"{path}: diverged file changed but its rationale did not (base {short}); "
                "explain the new change with --record-divergence"]
    return []


def copy_and_rename_status(root: Path, commit: str, *, staged: bool) -> str | None:
    """`git diff --name-status -z` of the roots with rename (50%) and near-copy (90%) detection,
    copies searched from every base file, not only modified ones. None if git fails or skips
    detection (too many files for the limit)."""
    revisions = ("--cached", commit) if staged else (commit, "HEAD")
    try:
        done = subprocess.run(["git", "-C", str(root), "diff", "--no-ext-diff", "-M", "-C90%", "--find-copies-harder",
                               "-l100000", "--name-status", "-z", *revisions, "--", *ROOTS],
                              capture_output=True, text=True, timeout=600)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if done.returncode != 0 or "detection was skipped" in done.stderr:
        return None
    return done.stdout


def base_problems(root: Path, manifest_path: Path, base: str | None) -> tuple[list[str], list[str]]:
    """Compare the manifest with the base manifest. Returns (problems, warnings).

    - No row of the base disappears or changes path, ever: a deleted file stays as `retired`.
    - While the upstream pin is unchanged, a synced row keeps the base row's `upstream_sha256`,
      and a new synced row is not allowed: only a sync (which moves the pin) says what upstream
      contains. Edits go through `--record-divergence` / `--retire`.
    Fails closed in GitHub Actions (or with --base) when the base cannot be read."""
    strict = bool(os.environ.get("GITHUB_ACTIONS") or base)

    def unreadable(why: str) -> tuple[list[str], list[str]]:
        if strict:
            return [f"manifest: {why}; cannot compare with the base manifest"], []
        return [], [f"skipping the base-manifest comparison: {why}"]

    merge_head = None
    if not os.environ.get("GITHUB_ACTIONS"):
        merge_head = git(root, "rev-parse", "--verify", "MERGE_HEAD")
    commit, why = base_commit(root, base, merge_head)
    if commit is None:
        return unreadable(why or "no base commit")
    if symlinked_component(root, manifest_path):
        return [], []  # check() reports it
    rel = manifest_rel(root, manifest_path)
    candidates = [*MANIFEST_PATHS, *([rel] if rel not in MANIFEST_PATHS else [])]
    for candidate in candidates:
        old_manifest, errors = load_revision(root, commit, candidate)
        if errors:
            return unreadable(f"cannot parse the base manifest at {commit}: {'; '.join(errors)}")
        if old_manifest is not None:
            break
    else:
        listing = git(root, "ls-tree", "--name-only", commit, "--", CHECKER)
        if listing is None:
            return unreadable(f"cannot read the tree of base {commit}")
        if CHECKER in listing.splitlines():  # only the original cutover may predate the ledger
            return [f"manifest: base {commit[:12]} has {CHECKER} but no manifest at {', '.join(candidates)}; "
                    "keep the manifest at a known path (MANIFEST_PATHS)"], []
        return [], []
    try:
        old = {row["path"]: row for row in old_manifest["rows"]}
        if len(old) != len(old_manifest["rows"]) or not all(isinstance(path, str) for path in old):
            raise ValueError("base row paths must be unique strings")
        old_pin = old_manifest["upstream"]["commit"]
    except (ValueError, KeyError, TypeError):
        return unreadable(f"cannot parse the base manifest at {commit}")
    new_manifest, errors = load(manifest_path)
    if new_manifest is None or errors:
        return [], []  # check() reports an invalid manifest
    new = {row["path"]: row for row in new_manifest["rows"]
           if isinstance(row, dict) and isinstance(row.get("path"), str)}
    pin = new_manifest["upstream"]["commit"]
    if old_manifest["schema_version"] == SHARDED_SCHEMA_VERSION:
        if new_manifest["schema_version"] != SHARDED_SCHEMA_VERSION:
            return ["manifest: cannot return to the monolithic layout after sharding"], []
    elif new_manifest["schema_version"] == SHARDED_SCHEMA_VERSION:
        if old_manifest != {**new_manifest, "schema_version": SCHEMA_VERSION}:
            return ["manifest: sharding must preserve every existing row and all shared metadata; "
                    "convert the base ledger separately from any sync or row edit"], []
    short = commit[:12]
    problems = [f"{path}: row removed or renamed (base {short}); rows are never dropped: restore it, then use "
                "--record-divergence for a changed file or --retire for a deleted one"
                for path in sorted(old.keys() - new.keys())]
    tracked = {path for path, row in old.items() if row.get("disposition") in (*SYNCED, "diverged")}
    moves = copy_and_rename_status(root, commit, staged=bool(merge_head))
    if moves is None:
        target = "the index" if merge_head else "HEAD"
        found, note = unreadable(f"cannot diff base {commit} with {target} for renames")
        problems += found
        warnings = note
    else:
        warnings = []
        fields = moves.split("\0")
        i = 0
        while i < len(fields):
            status = fields[i]
            if status[:1] in ("R", "C") and i + 2 < len(fields):
                source, target = fields[i + 1], fields[i + 2]
                if source in tracked and target not in new:
                    verb = "renamed" if status[0] == "R" else "copied"
                    problems.append(f"{target}: {verb} from tracked {source} (base {short}) but has no row; a "
                                    f"tracked file stays tracked when it moves: --record-divergence {target} "
                                    "(and --retire the old path if it was deleted)")
                i += 3
            else:
                i += 2
    if pin != old_pin:
        problem, note = repin_authorization(old_pin, pin)
        return problems + ([problem] if problem else []), warnings + ([note] if note else [])
    for path, row in sorted(new.items(), key=lambda item: str(item[0])):
        problems += row_transition_problems(path, old.get(path), row, short)
        before = old.get(path) or {}
        if row.get("disposition") == "retired" and before.get("disposition") not in (None, "retired"):
            text = git(root, "show", f"{commit}:{path}")
            if text is not None and row.get("line_fingerprint") != line_fingerprint(text + "\n"):
                problems.append(f"{path}: retired row's line_fingerprint does not match the file at base {short}; "
                                "use --retire")
    return problems, warnings


def fix_commands(fixes: dict[str, list[str]]) -> list[str]:
    script = "python3 scripts/check_formal_math_sync.py"
    commands = []
    if fixes["record"]:
        commands.append(f"{script} --record-divergence {' '.join(map(shlex.quote, fixes['record']))} "
                        "--rationale '<why ATLAS differs from formal-math>' --backport pending")
    if fixes["retire"]:
        commands.append(f"{script} --retire {' '.join(map(shlex.quote, fixes['retire']))}")
    return commands


def row_structure_problems(root: Path, manifest: dict) -> list[str]:
    """Check record shape without requiring old hashes to match edited Lean files."""
    paths = []
    problems = []
    for index, row in enumerate(manifest["rows"]):
        if not isinstance(row, dict):
            problems.append(f"row {index}: not an object")
            continue
        path = row.get("path")
        why = path_problem(root, path)
        if why:
            problems.append(f"{path!r}: {why}")
            continue
        paths.append(path)
        problems.extend(field_problems(row))
    if paths != sorted(set(paths)):
        problems.append("manifest: rows must be sorted and unique")
    return problems


def split_by_domain(root: Path, manifest_path: Path) -> int:
    """Convert only the file layout. No upstream checkout or record edits are involved."""
    manifest, problems = load(manifest_path)
    if manifest is not None:
        problems.extend(row_structure_problems(root, manifest))
    if problems or manifest is None:
        print("\n".join(problems), file=sys.stderr)
        return 1
    if manifest["schema_version"] == SHARDED_SCHEMA_VERSION:
        print(f"{manifest_path}: already sharded")
        return 0
    try:
        write_manifest(manifest_path, {**manifest, "schema_version": SHARDED_SCHEMA_VERSION})
    except (OSError, ValueError) as error:
        print(f"cannot shard {manifest_path}: {error}", file=sys.stderr)
        return 1
    print(f"sharded {len(manifest['rows'])} rows from {manifest_path} by library and domain")
    return 0


def edit(root: Path, manifest_path: Path, paths: list[str], new_row, create: bool = False) -> int:
    """Apply `new_row(old_row, path) -> row` to each path's row and rewrite the manifest. In the
    sharded layout each edited row moves to its module file; other rows stay where they are.

    With `create`, a path without a row starts from an empty row (a tracked file's new path)."""
    manifest, problems = load(manifest_path)
    if manifest is not None:
        problems.extend(row_structure_problems(root, manifest))
    if problems or manifest is None:
        print("\n".join(problems), file=sys.stderr)
        return 1
    rows = {row["path"]: row for row in manifest["rows"]}
    errors = []
    for path in paths:
        why = path_problem(root, path)
        if why:
            errors.append(f"{path}: {why}")
        elif path not in rows and not create:
            errors.append(f"{path}: no manifest row; files without a row are not synced and need no record")
        else:
            result = new_row(rows.get(path, {}), path)
            if isinstance(result, str):
                errors.append(f"{path}: {result}")
            else:
                rows[path] = result
    if errors:
        print("\n".join(f"FAIL [formal-math-sync]: {error}" for error in errors), file=sys.stderr)
        return 1
    manifest["rows"] = [rows[path] for path in sorted(rows)]
    try:
        modules = module_rows(manifest_path, manifest, worktree_shards(manifest_path))
        write_manifest(manifest_path, manifest, paths=paths, modules=modules)
    except (OSError, ValueError) as error:
        print(f"cannot update {manifest_path}: {error}", file=sys.stderr)
        return 1
    print(f"updated the ledger at {manifest_path}: {len(paths)} row(s)")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent, help="ATLAS checkout")
    ap.add_argument("--manifest", type=Path, help=f"manifest path (default: <root>/{MANIFEST})")
    writers = ap.add_mutually_exclusive_group()
    writers.add_argument("--record-divergence", nargs="+", metavar="PATH", help="mark synced files as reviewed divergences")
    writers.add_argument("--retire", nargs="+", metavar="PATH", help="mark deleted synced files as retired")
    writers.add_argument("--split-by-domain", action="store_true", help="convert a legacy ledger to domain shards without changing any row")
    ap.add_argument("--rationale", help="why ATLAS differs from formal-math (with --record-divergence)")
    ap.add_argument("--backport", help="'pending', 'not-needed', or the formal-math backport PR URL")
    ap.add_argument("--base", help="commit to compare rows with (default: in CI the event's base, "
                    "else the merge-base with origin/main)")
    a = ap.parse_args(argv)
    manifest_path = a.manifest or a.root / MANIFEST

    if a.split_by_domain:
        return split_by_domain(a.root, manifest_path)
    if a.record_divergence:
        if not (a.rationale and a.rationale.strip()) or not (a.backport and BACKPORT.fullmatch(a.backport)):
            ap.error("--record-divergence needs a non-empty --rationale and --backport pending|not-needed|<https URL>")

        def diverge(old: dict, path: str) -> dict | str:
            target = a.root / path
            if not target.is_file():
                return "file is missing; use --retire for a deleted file"
            row = {"path": path, "disposition": "diverged", "published_sha256": sha256(target.read_bytes())}
            if "upstream_sha256" in old:
                row["upstream_sha256"] = old["upstream_sha256"]
            if "upstream_commit" in old:  # the revision behind upstream_sha256, or the deleting commit
                row["upstream_commit"] = old["upstream_commit"]
            row.update(rationale=a.rationale.strip(), backport=a.backport)
            return row
        return edit(a.root, manifest_path, a.record_divergence, diverge, create=True)

    if a.retire:
        def retire(old: dict, path: str) -> dict | str:
            if (a.root / path).exists():
                return "file still exists; delete it first, or use --record-divergence for a changed file"
            return retired_row(old, path, last_committed_text(a.root, path))
        return edit(a.root, manifest_path, a.retire, retire)

    problems, fixes, rows = check(a.root, manifest_path)
    if os.environ.get("GITHUB_ACTIONS") and manifest_rel(a.root, manifest_path) != MANIFEST:
        problems.append(f"manifest: CI requires the canonical ledger at {MANIFEST}")
    removed, warnings = base_problems(a.root, manifest_path, a.base)
    problems += removed
    for warning in warnings:
        print(f"warning [formal-math-sync]: {warning}")
    for problem in problems:
        print(f"FAIL [formal-math-sync]: {problem}")
    if problems:
        print(f"FAIL [formal-math-sync]: {len(problems)} problem(s). A pull request that changes or deletes a "
              "file synced from formal-math records it in the manifest (no formal-math checkout needed):")
        for command in fix_commands(fixes):
            print(f"  {command}")
        return 1
    print(f"ok [formal-math-sync]: {rows} rows; synced files match the manifest.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
