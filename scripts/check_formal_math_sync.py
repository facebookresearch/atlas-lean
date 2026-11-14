#!/usr/bin/env python3
"""Check provenance/formal-math-sync.json against the ATLAS root libraries.

    scripts/check_formal_math_sync.py            report every mismatch, exit 0 (check.sh preflight)
    scripts/check_formal_math_sync.py --strict   exit 1 when there is any mismatch

The manifest records, for every Lean file under the root libraries that ATLAS shares with
fairinternal/formal-math, how the published file relates to its upstream source (see
`provenance/README.md`). The check is offline and deterministic and uses only the standard library:

- every root-library `.lean` file has exactly one row: no missing or extra rows, no duplicate,
  absolute, escaping, or symlinked paths;
- `published_sha256` is the SHA-256 of the file's bytes;
- for `identical`, `attributed`, and `behind` rows, the file is the Meta header (or, for rows marked
  `"header": "upstream"`, the upstream third-party copyright and license block), then the recorded
  notice (if any), then a body whose SHA-256 is `upstream_sha256` (one parser: `split_published`);
- `diverged` rows carry a rationale and a backport status;
- counts, the row digest, roots, and the Lean toolchain agree with the rows and the repository.

This module also holds the header parser that `scripts/sync_formal_math.py` uses to classify files,
so generation and checking cannot disagree about what a header is.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path, PurePosixPath

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_copyright import META  # noqa: E402  (the one definition of the Meta header)

SCHEMA_VERSION = 1
MANIFEST = "provenance/formal-math-sync.json"
ROOTS = ("MathlibExt", "MathlibExtTest", "CSLibExt", "CSLibExtTest", "WantedExt")
# identical:  Meta header + body of the upstream file at `upstream.commit`; with
#             "header": "upstream", the upstream file byte for byte (its third-party license kept)
# attributed: Meta header + recorded notice + that body
# behind:     Meta header (+ notice) + the body of an older upstream version (`upstream_commit`)
# diverged:   reviewed ATLAS-side change; needs `rationale` and `backport`
# local:      not taken from formal-math (never upstream, or third-party FLT content)
# retired:    deleted upstream; ATLAS still publishes it
DISPOSITIONS = ("identical", "attributed", "behind", "diverged", "local", "retired")
HEADER_CHECKED = ("identical", "attributed", "behind")
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
PLAIN_BLOCK = re.compile(r"/-(?![-!]).*?-/", re.S)
UPSTREAM_HEADER_WORDS = re.compile(r"Copyright|Authors?:|[Ll]icen[cs]e")
FLT_MARKERS = ("Anthropic, PBC", "flt-regular authors")


def sha256(data: bytes | str) -> str:
    if isinstance(data, str):
        data = data.encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def split_published(text: str, notice: str = "", header: str = "meta") -> tuple[str | None, str | None]:
    """Split an ATLAS file into its body, or explain why it is not header + notice + body.

    `header="meta"`: the file starts with the exact Meta header, then the notice if one is
    recorded. `header="upstream"`: the file keeps the upstream file's own third-party copyright and
    license block (as scripts/check_copyright.py allows for code copied from another project).
    Blank lines after the header and after the notice are separators, not body.
    Returns (body, None) or (None, problem).
    """
    if header == "upstream":
        block = PLAIN_BLOCK.match(text)
        if notice or not block or "Meta Platforms" in block.group(0) or "Copyright" not in block.group(0) \
                or not re.search(r"[Ll]icen[cs]e", block.group(0)):
            return None, "does not start with a third-party copyright and license header"
        return text[block.end():].lstrip("\n"), None
    if header != "meta":
        return None, f"unknown header kind {header!r}"
    if not text.startswith(META):
        return None, "does not start with the Meta header"
    rest = text[len(META):].lstrip("\n")
    if notice:
        if not rest.startswith(notice):
            return None, "recorded notice does not follow the Meta header"
        rest = rest[len(notice):].lstrip("\n")
    return rest, None


def leading_notice(text: str) -> str | None:
    """The plain block comment right after the Meta header, if any (an attribution candidate)."""
    if not text.startswith(META):
        return None
    block = PLAIN_BLOCK.match(text[len(META):].lstrip("\n"))
    return block.group(0) if block else None


def upstream_body(text: str) -> str:
    """Formal-Math file body: the text after a leading license or authorship block comment."""
    block = PLAIN_BLOCK.match(text)
    if block and UPSTREAM_HEADER_WORDS.search(block.group(0)):
        return text[block.end():].lstrip("\n")
    return text.lstrip("\n")


def is_flt(text: str) -> bool:
    """Third-party FLT content keeps its own header; ATLAS never rewrites it."""
    block = PLAIN_BLOCK.match(text)
    return bool(block) and any(marker in block.group(0) for marker in FLT_MARKERS)


def row_line(row: dict) -> str:
    return json.dumps(row, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def rows_digest(rows: list[dict]) -> str:
    return "sha256:" + sha256("".join(row_line(row) + "\n" for row in rows))


def count_rows(rows: list[dict]) -> dict[str, int]:
    counts = {d: 0 for d in DISPOSITIONS}
    for row in rows:
        if row.get("disposition") in counts:
            counts[row["disposition"]] += 1
    return counts


def dump_manifest(manifest: dict) -> str:
    """Serialize with one row per line so a sync diff shows one line per changed file."""
    head = {k: v for k, v in manifest.items() if k != "rows"}
    lines = ["{"]
    for key, value in head.items():
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


def check_row(root: Path, row: dict) -> list[str]:
    path = row["path"]
    problems: list[str] = []
    disposition = row.get("disposition")
    if disposition not in DISPOSITIONS:
        return [f"{path}: unknown disposition {disposition!r}"]
    target = root / path
    if not target.is_file():
        return [f"{path}: extra row: no such file"]
    data = target.read_bytes()
    published = row.get("published_sha256")
    if not isinstance(published, str) or not SHA256.fullmatch(published):
        problems.append(f"{path}: published_sha256 is not a SHA-256 hex digest")
    elif sha256(data) != published:
        problems.append(f"{path}: published_sha256 mismatch (file is {sha256(data)})")
    notice = row.get("notice", "")
    if disposition == "attributed" and not (isinstance(notice, str) and notice):
        problems.append(f"{path}: attributed row has no notice")
    if "header" in row and (disposition not in ("identical", "behind") or row["header"] != "upstream"):
        problems.append(f"{path}: header field is only for identical or behind rows that keep the upstream header")
    if disposition == "identical" and "notice" in row:
        problems.append(f"{path}: identical row records a notice; use the attributed disposition")
    if disposition == "behind" and not (isinstance(row.get("upstream_commit"), str) and COMMIT.fullmatch(row["upstream_commit"])):
        problems.append(f"{path}: behind row needs the full upstream_commit its body matches")
    if disposition in HEADER_CHECKED:
        upstream = row.get("upstream_sha256")
        if not isinstance(upstream, str) or not SHA256.fullmatch(upstream):
            problems.append(f"{path}: upstream_sha256 is not a SHA-256 hex digest")
        else:
            try:
                text = data.decode("utf-8")
            except UnicodeDecodeError:
                return problems + [f"{path}: header-only violation: file is not UTF-8"]
            body, why = split_published(text, notice if isinstance(notice, str) else "", row.get("header", "meta"))
            if why:
                problems.append(f"{path}: header-only violation: {why}")
            elif sha256(body) != upstream:
                problems.append(f"{path}: header-only violation: body after the header does not hash to upstream_sha256")
    if disposition == "diverged":
        for field in ("rationale", "backport"):
            value = row.get(field)
            if not isinstance(value, str) or not value.strip():
                problems.append(f"{path}: diverged row has no {field}")
    return problems


def check(root: Path, manifest_path: Path) -> tuple[list[str], int]:
    """Return (mismatches, row count)."""
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        return [f"{manifest_path}: cannot read manifest: {error}"], 0
    if not isinstance(manifest, dict) or not isinstance(manifest.get("rows"), list):
        return [f"{manifest_path}: manifest has no rows list"], 0
    problems: list[str] = []
    rows = manifest["rows"]
    if manifest.get("schema_version") != SCHEMA_VERSION:
        problems.append(f"manifest: schema_version is {manifest.get('schema_version')!r}, expected {SCHEMA_VERSION}")
    upstream = manifest.get("upstream")
    if not (isinstance(upstream, dict) and isinstance(upstream.get("repository"), str)
            and isinstance(upstream.get("commit"), str) and COMMIT.fullmatch(upstream["commit"])):
        problems.append("manifest: upstream needs a repository and a full 40-hex commit")
    if manifest.get("roots") != list(ROOTS):
        problems.append(f"manifest: roots are {manifest.get('roots')!r}, expected {list(ROOTS)!r}")
    toolchain = root / "lean-toolchain"
    if toolchain.is_file() and manifest.get("lean_toolchain") != toolchain.read_text().strip():
        problems.append(f"manifest: lean_toolchain {manifest.get('lean_toolchain')!r} differs from lean-toolchain")

    on_disk, links = library_files(root)
    problems += [f"{link}: symlinked path under the root libraries" for link in links]
    seen: set[str] = set()
    valid_rows: list[dict] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            problems.append(f"row {index}: not an object")
            continue
        path = row.get("path")
        why = path_problem(root, path)
        if why:
            problems.append(f"{path!r}: {why}")
            continue
        if path in seen:
            problems.append(f"{path}: duplicate row")
            continue
        seen.add(path)
        valid_rows.append(row)
        problems += check_row(root, row)
    problems += [f"{path}: missing row: file has no manifest row" for path in sorted(on_disk - seen)]

    paths = [row.get("path") for row in rows if isinstance(row, dict)]
    if all(isinstance(p, str) for p in paths) and paths != sorted(paths):
        problems.append("manifest: rows are not sorted by path")
    if manifest.get("counts") != count_rows(rows if all(isinstance(r, dict) for r in rows) else valid_rows):
        problems.append("manifest: counts do not match the rows")
    if manifest.get("total") != len(rows):
        problems.append(f"manifest: total is {manifest.get('total')!r}, rows has {len(rows)}")
    if all(isinstance(r, dict) for r in rows) and manifest.get("rows_digest") != rows_digest(rows):
        problems.append("manifest: rows_digest does not match the rows")
    return problems, len(rows)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--strict", action="store_true", help="exit 1 when there is any mismatch")
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent, help="ATLAS checkout")
    ap.add_argument("--manifest", type=Path, help=f"manifest path (default: <root>/{MANIFEST})")
    a = ap.parse_args(argv)
    manifest = a.manifest or a.root / MANIFEST
    problems, rows = check(a.root, manifest)
    for problem in problems:
        print(f"{'FAIL' if a.strict else 'mismatch'} [formal-math-sync]: {problem}")
    if not problems:
        print(f"ok [formal-math-sync]: {rows} rows match the root libraries.")
        return 0
    if a.strict:
        print(f"FAIL [formal-math-sync]: {len(problems)} mismatch(es) in {rows} rows.")
        return 1
    print(f"report-only [formal-math-sync]: {len(problems)} mismatch(es) in {rows} rows; "
          "not failing (pass --strict to fail). Refresh with scripts/sync_formal_math.py or record a divergence.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
