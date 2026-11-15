#!/usr/bin/env python3
"""Check, and record divergences in, provenance/formal-math-sync.json.

    scripts/check_formal_math_sync.py                      check (check.sh preflight); exit 1 on failure
    scripts/check_formal_math_sync.py --record-divergence PATH... --rationale TEXT --backport pending|<url>
    scripts/check_formal_math_sync.py --retire PATH...

The manifest pins a fairinternal/formal-math commit and has a row for every root-library Lean file
taken from it (see `provenance/README.md`). The check is offline, deterministic, standard library
only, and scoped to those synced files, so a pull request fails only if it touches one:

- the manifest parses: schema, upstream pin, roots, unique sorted relative paths under the roots
  (no absolute, escaping, or symlinked paths);
- `identical`, `attributed`, and `behind` rows: the file exists and its SHA-256 is
  `published_sha256`, and it is the Meta header (or, with `"header": "upstream"`, the upstream
  third-party license block), then the recorded attribution notice if any, then a body whose
  SHA-256 is `upstream_sha256` (one parser: `split_published`);
- `retired` rows: the file is absent;
- `diverged` rows: a non-empty `rationale` and `backport`; their hashes are not compared;
- files without a row (ATLAS-only work) are ignored.

A pull request that changes or deletes a synced file records that with `--record-divergence` or
`--retire`; neither needs a Formal-Math checkout. `scripts/sync_formal_math.py` regenerates the
manifest from a Formal-Math checkout and uses the header parser defined here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import sys
from pathlib import Path, PurePosixPath

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_copyright import META  # noqa: E402  (the one definition of the Meta header)

SCHEMA_VERSION = 1
MANIFEST = "provenance/formal-math-sync.json"
ROOTS = ("MathlibExt", "MathlibExtTest", "CSLibExt", "CSLibExtTest", "WantedExt")
# identical:  Meta header + body of the upstream file at `upstream.commit`; with
#             "header": "upstream", the upstream file byte for byte (its third-party license kept)
# attributed: Meta header + recorded attribution notice + that body
# behind:     header-only copy of an older upstream version (`upstream_commit`)
# diverged:   reviewed ATLAS-side difference; needs `rationale` and `backport`
# retired:    removed from ATLAS on purpose; the file must stay absent
DISPOSITIONS = ("identical", "attributed", "behind", "diverged", "retired")
SYNCED = ("identical", "attributed", "behind")
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
PLAIN_BLOCK = re.compile(r"/-(?![-!]).*?-/", re.S)
UPSTREAM_HEADER_WORDS = re.compile(r"Copyright|Authors?:|[Ll]icen[cs]e")
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
    from another project). Blank lines after the header and after the notice are separators.
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
                "diverged": ("rationale", "backport"), "retired": ()}[disposition]
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
    if disposition not in SYNCED:
        return []
    if not target.is_file():
        return [f"{path}: synced file is missing"]
    data = target.read_bytes()
    if sha256(data) != row["published_sha256"]:
        return [f"{path}: synced file changed (sha256 {sha256(data)}, manifest {row['published_sha256']})"]
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


def load(manifest_path: Path) -> tuple[dict | None, list[str]]:
    """Parse the manifest and check its shape. Returns (manifest or None, problems)."""
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        return None, [f"{manifest_path}: cannot read manifest: {error}"]
    if not isinstance(manifest, dict) or not isinstance(manifest.get("rows"), list):
        return None, [f"{manifest_path}: manifest has no rows list"]
    problems = []
    if manifest.get("schema_version") != SCHEMA_VERSION:
        problems.append(f"manifest: schema_version is {manifest.get('schema_version')!r}, expected {SCHEMA_VERSION}")
    upstream = manifest.get("upstream")
    if not (isinstance(upstream, dict) and isinstance(upstream.get("repository"), str)
            and isinstance(upstream.get("commit"), str) and COMMIT.fullmatch(upstream["commit"])):
        problems.append("manifest: upstream needs a repository and a full 40-hex commit")
    if manifest.get("roots") != list(ROOTS):
        problems.append(f"manifest: roots are {manifest.get('roots')!r}, expected {list(ROOTS)!r}")
    if not isinstance(manifest.get("lean_toolchain"), str):
        problems.append("manifest: lean_toolchain is not a string")
    return manifest, problems


def check(root: Path, manifest_path: Path) -> tuple[list[str], dict[str, list[str]], int]:
    """Return (problems, suggested fixes {"record": [paths], "retire": [paths]}, row count)."""
    manifest, problems = load(manifest_path)
    fixes: dict[str, list[str]] = {"record": [], "retire": []}
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
            fixes["retire" if row["disposition"] in SYNCED and not (root / path).exists() else "record"].append(path)
    if paths != sorted(paths):
        problems.append("manifest: rows are not sorted by path")
    return problems, fixes, len(manifest["rows"])


def fix_commands(fixes: dict[str, list[str]]) -> list[str]:
    script = "python3 scripts/check_formal_math_sync.py"
    commands = []
    if fixes["record"]:
        commands.append(f"{script} --record-divergence {' '.join(map(shlex.quote, fixes['record']))} "
                        "--rationale '<why ATLAS differs from formal-math>' --backport pending")
    if fixes["retire"]:
        commands.append(f"{script} --retire {' '.join(map(shlex.quote, fixes['retire']))}")
    return commands


def edit(root: Path, manifest_path: Path, paths: list[str], new_row) -> int:
    """Apply `new_row(old_row, path) -> row` to each path's row and rewrite the manifest."""
    manifest, problems = load(manifest_path)
    if manifest is None:
        print("\n".join(problems), file=sys.stderr)
        return 1
    rows = {row.get("path"): row for row in manifest["rows"] if isinstance(row, dict)}
    errors = []
    for path in paths:
        why = path_problem(root, path)
        if why:
            errors.append(f"{path}: {why}")
        elif path not in rows:
            errors.append(f"{path}: no manifest row; files without a row are not synced and need no record")
        else:
            result = new_row(rows[path], path)
            if isinstance(result, str):
                errors.append(f"{path}: {result}")
            else:
                rows[path] = result
    if errors:
        print("\n".join(f"FAIL [formal-math-sync]: {e}" for e in errors), file=sys.stderr)
        return 1
    manifest["rows"] = [rows[p] for p in sorted(rows)]
    manifest_path.write_text(dump_manifest(manifest), encoding="utf-8")
    print(f"updated {manifest_path}: {len(paths)} row(s)")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent, help="ATLAS checkout")
    ap.add_argument("--manifest", type=Path, help=f"manifest path (default: <root>/{MANIFEST})")
    ap.add_argument("--record-divergence", nargs="+", metavar="PATH", help="mark synced files as reviewed divergences")
    ap.add_argument("--rationale", help="why ATLAS differs from formal-math (with --record-divergence)")
    ap.add_argument("--backport", help="'pending', 'not-needed', or the formal-math backport PR URL")
    ap.add_argument("--retire", nargs="+", metavar="PATH", help="mark deleted synced files as retired")
    a = ap.parse_args(argv)
    manifest_path = a.manifest or a.root / MANIFEST

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
            row.update(rationale=a.rationale.strip(), backport=a.backport)
            return row
        return edit(a.root, manifest_path, a.record_divergence, diverge)

    if a.retire:
        def retire(old: dict, path: str) -> dict | str:
            if (a.root / path).exists():
                return "file still exists; delete it first, or use --record-divergence for a changed file"
            return {"path": path, "disposition": "retired"}
        return edit(a.root, manifest_path, a.retire, retire)

    problems, fixes, rows = check(a.root, manifest_path)
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
