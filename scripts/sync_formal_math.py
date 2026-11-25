#!/usr/bin/env python3
"""Regenerate the Formal-Math provenance ledger from a local upstream checkout.

    scripts/sync_formal_math.py --formal-math ~/formal-math --commit <sha> \\
        [--rationales divergences.json] [--report sync-report.md]

Reads Formal-Math only through `git` in the given local repository (the objects of `--commit`
and its first-parent history). It never fetches (lazy partial-clone fetches and `git replace`
refs are disabled) and refuses shallow clones, so internal automation fetches the pinned commit
first. Classifies every `.lean` file under the ATLAS root libraries, writes a row for each file
taken from Formal-Math (files that never came from it get no row), and prints a sync report:
counts, added, removed, changed, and diverged rows.

Fails closed, writing neither manifest nor report, when a file newly diverges from Formal-Math
(including a file deleted upstream that ATLAS still publishes) without a rationale and backport
status. Give them with `--rationales`, a JSON object mapping each path to
{"rationale": "...", "backport": "..."}. A row already diverged in the current manifest keeps its
explanation only while its published and upstream hashes are unchanged. Rows never disappear: a
file that left ATLAS keeps its row as `retired`. Output is deterministic for a fixed ATLAS tree and upstream commit.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_formal_math_sync import (  # noqa: E402  (the checker owns the header parser)
    BACKPORT, MANIFEST, ROOTS, SCHEMA_VERSION, UPSTREAM_REPOSITORY, count_rows, is_flt,
    git as atlas_git,
    last_committed_text, leading_notice, library_files, load, load_revision, manifest_documents,
    manifest_rel, retired_row, row_structure_problems, shard_directory, sha256, split_published,
    upstream_body, write_manifest,
)

ZERO = "0" * 40
# Read only what is already local: no `git replace` substitutions, no partial-clone lazy fetches.
GIT_ENV = {**os.environ, "GIT_NO_REPLACE_OBJECTS": "1", "GIT_NO_LAZY_FETCH": "1"}


def git(repo: Path, *args: str) -> bytes:
    # --no-replace-objects: `git replace` refs must not make the recorded commit read as another.
    return subprocess.run(["git", "--no-replace-objects", "-C", str(repo), "-c", "core.quotepath=off", *args], env=GIT_ENV,
                          check=True, capture_output=True).stdout


class Blobs:
    """Batch blob reader over `git cat-file --batch`."""

    def __init__(self, repo: Path) -> None:
        self.proc = subprocess.Popen(["git", "--no-replace-objects", "-C", str(repo), "cat-file", "--batch"],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                     env=GIT_ENV)

    def read(self, oid: str) -> bytes:
        assert self.proc.stdin and self.proc.stdout
        try:
            self.proc.stdin.write(oid.encode() + b"\n")
            self.proc.stdin.flush()
        except BrokenPipeError:
            pass  # the reader exited; the empty header below reports it
        header = self.proc.stdout.readline().split()
        # Older git ends the batch without a "missing" line when lazy fetching is disabled.
        if not header or header[1:] == [b"missing"]:
            raise SystemExit(f"sync: blob {oid} is not in the local Formal-Math repository (partial clone?); "
                             "fetch the pinned commit's objects first, this script never fetches")
        if len(header) != 3 or header[1] != b"blob":
            raise SystemExit(f"sync: cannot read blob {oid}: {header!r}")
        data = self.proc.stdout.read(int(header[2]))
        self.proc.stdout.read(1)
        return data

    def close(self) -> None:
        if self.proc.stdin:
            try:
                self.proc.stdin.close()
            except BrokenPipeError:
                pass
        self.proc.wait()


def upstream_tree(repo: Path, commit: str) -> dict[str, str]:
    """Path -> blob id for every regular `.lean` file under the roots at `commit`."""
    out = git(repo, "ls-tree", "-r", "-z", "--full-tree", commit, "--", *ROOTS)
    tree: dict[str, str] = {}
    for entry in out.split(b"\0"):
        if not entry:
            continue
        meta, path = entry.decode().split("\t", 1)
        mode, kind, oid = meta.split()
        if kind == "blob" and mode in ("100644", "100755") and path.endswith(".lean"):
            tree[path] = oid
    return tree


def upstream_history(repo: Path, commit: str, wanted: set[str]) -> dict[str, list[tuple[str, str]]]:
    """Path -> [(commit, blob id it set)], newest first, along the first-parent history."""
    out = git(repo, "log", "--first-parent", "-m", "--raw", "--no-renames", "--no-abbrev",
              "--format=%x00%H", commit, "--", *ROOTS)
    history: dict[str, list[tuple[str, str]]] = {}
    current = ""
    for line in out.decode().splitlines():
        if line.startswith("\0"):
            current = line[1:]
        elif line.startswith(":"):
            meta, path = line.split("\t", 1)
            if path in wanted:
                history.setdefault(path, []).append((current, meta.split()[3]))
    return history


def classify(text: str, up_text: str | None, versions: list[tuple[str, str]], current_oid: str | None,
             blobs: Blobs) -> dict:
    """Disposition fields for one ATLAS file (without path, published hash, or rationale)."""
    if is_flt(text):
        return {"disposition": "local"}  # third-party FLT content keeps its own header
    # Meta-header readings of the ATLAS file (with and without an attribution notice), keyed by
    # the hash of the body they leave.
    readings = [""] + ([notice] if (notice := leading_notice(text)) else [])
    bodies: dict[str, str] = {}
    for n in readings:
        body = split_published(text, n)[0]
        if body is not None:
            bodies.setdefault(sha256(body), n)

    def match(source: str) -> tuple[str, dict] | None:
        if source == text and split_published(text, "", "upstream")[1] is None:
            # The upstream file byte for byte, its own copyright and license header kept.
            return sha256(text), {"upstream_sha256": sha256(text), "header": "upstream"}
        digest = sha256(upstream_body(source))
        if digest not in bodies:
            return None
        fields = {"upstream_sha256": digest}
        if bodies[digest]:
            fields["notice"] = bodies[digest]
        return digest, fields

    if up_text is None:
        deleted = next((c for c, oid in versions if oid == ZERO), None)
        if deleted is None:
            return {"disposition": "local"}
        return {"disposition": "diverged", "upstream_commit": deleted}  # deleted upstream, still published
    if found := match(up_text):
        fields = found[1]
        return {"disposition": "attributed" if "notice" in fields else "identical", **fields}
    seen = {current_oid}
    for old_commit, oid in versions:
        if oid in seen or oid == ZERO:
            continue
        seen.add(oid)
        if found := match(blobs.read(oid).decode("utf-8", "replace")):
            return {"disposition": "behind", "upstream_commit": old_commit, **found[1]}
    return {"disposition": "diverged", "upstream_sha256": sha256(upstream_body(up_text))}


def explained(source: object) -> bool:
    """A divergence is explained by a non-empty rationale and a valid backport status (the checker's rule)."""
    return (isinstance(source, dict) and isinstance(source.get("rationale"), str) and bool(source["rationale"].strip())
            and isinstance(source.get("backport"), str) and bool(BACKPORT.fullmatch(source["backport"])))


def load_json(path: Path | None) -> dict:
    if path is None or not path.is_file():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def build(atlas: Path, repo: Path, commit: str, previous: dict,
          rationales: dict) -> tuple[dict, list[str], int]:
    """Return (manifest, paths that newly diverged without a rationale, count of files with no row)."""
    files, links = library_files(atlas)
    if links:
        raise SystemExit("sync: symlinked paths under the root libraries: " + ", ".join(links))
    tree = upstream_tree(repo, commit)
    history = upstream_history(repo, commit, files)
    old_rows = {row["path"]: row for row in previous.get("rows", [])}
    same_pin = previous.get("upstream", {}).get("commit") == commit
    blobs = Blobs(repo)
    rows, unexplained, dropped, local = [], [], [], 0
    try:
        for path in sorted(files):
            data = (atlas / path).read_bytes()
            text = data.decode("utf-8", "replace")
            oid = tree.get(path)
            up_text = blobs.read(oid).decode("utf-8", "replace") if oid else None
            row = {"path": path, "published_sha256": sha256(data)}
            row.update(classify(text, up_text, history.get(path, []), oid, blobs))
            if row["disposition"] == "local":
                if path in old_rows:
                    dropped.append(path)
                local += 1
                continue
            old = old_rows.get(path, {})
            if row["disposition"] == "diverged" and same_pin and old.get("disposition") == "diverged" \
                    and old.get("published_sha256") == row["published_sha256"] and path not in rationales:
                rows.append(dict(old))  # same pin, same bytes: the recorded row stands as reviewed
                continue
            if row["disposition"] == "diverged":
                # A recorded explanation covers only the exact difference it was written for.
                same = old.get("disposition") == "diverged" and all(
                    old.get(k) == row.get(k) for k in ("published_sha256", "upstream_sha256"))
                source = rationales.get(path) if path in rationales else old if same else {}
                if explained(source):
                    row["rationale"], row["backport"] = source["rationale"], source["backport"]
                else:
                    unexplained.append(path)
            rows.append(row)
    finally:
        blobs.close()
    if dropped:  # rows never disappear; the checker rejects a manifest that drops one
        raise SystemExit("sync: these files have manifest rows but no longer look upstream-derived "
                         "(third-party FLT header or no upstream history); resolve them by hand: " + ", ".join(dropped))
    # A file that left ATLAS keeps its row as retired, with its provenance and line fingerprint.
    rows += [retired_row(old_rows[path], path, last_committed_text(atlas, path))
             for path in sorted(old_rows) if not (atlas / path).exists()]
    rows.sort(key=lambda row: row["path"])
    toolchain = (atlas / "lean-toolchain").read_text().strip()
    manifest = {
        "schema_version": previous.get("schema_version", SCHEMA_VERSION),
        "upstream": {"repository": UPSTREAM_REPOSITORY, "commit": commit},
        "lean_toolchain": toolchain,
        "roots": list(ROOTS),
        "rows": rows,
    }
    return manifest, unexplained, local


def report(previous: dict, manifest: dict, local: int) -> str:
    old = {row["path"]: row for row in previous.get("rows", [])}
    new = {row["path"]: row for row in manifest["rows"]}
    added = sorted(new.keys() - old.keys())
    removed = sorted(old.keys() - new.keys())
    # Whole rows, every provenance field included: the report is how a sync gets reviewed.
    changed = sorted(p for p in new.keys() & old.keys()
                     if json.dumps(new[p], sort_keys=True) != json.dumps(old[p], sort_keys=True))
    diverged = [p for p in sorted(new) if new[p]["disposition"] == "diverged"]
    up = manifest["upstream"]
    lines = [f"# Formal-Math sync report: {up['repository']}@{up['commit']}", "",
             f"Previous upstream commit: {previous.get('upstream', {}).get('commit', 'none')}", "",
             "| Disposition | Files |", "| --- | ---: |"]
    counts = count_rows(manifest["rows"])
    lines += [f"| {d} | {n} |" for d, n in counts.items()]
    lines += [f"| local (no row) | {local} |", f"| rows | {len(manifest['rows'])} |", ""]

    def section(title: str, paths: list[str], detail=lambda p: "") -> None:
        lines.append(f"## {title} ({len(paths)})")
        lines.extend(f"- `{p}`{detail(p)}" for p in paths)
        lines.append("")

    section("Added", added, lambda p: f": {new[p]['disposition']}")
    section("Removed", removed, lambda p: f": was {old[p]['disposition']}")
    section("Changed", changed,
            lambda p: f": {old[p]['disposition']} -> {new[p]['disposition']}"
            + ("" if old[p].get("published_sha256") == new[p].get("published_sha256") else ", ATLAS bytes changed"))
    section("Diverged", diverged, lambda p: f": {new[p].get('rationale', 'NO RATIONALE')} "
            f"(backport: {new[p].get('backport', 'none')})")
    return "\n".join(lines)


def previous_manifest(atlas: Path, manifest_path: Path) -> dict:
    """Read an existing ledger, refusing to forget committed rows before a sync."""
    shards = shard_directory(manifest_path)
    if manifest_path.exists() or manifest_path.is_symlink() or shards.exists() or shards.is_symlink():
        previous, problems = load(manifest_path)
        if previous is not None:
            problems.extend(row_structure_problems(atlas, previous))
        if problems or previous is None:
            raise SystemExit("sync: cannot read the existing ledger: " + "; ".join(problems))
    else:
        previous = {}
    if atlas_git(atlas, "rev-parse", "--show-toplevel") != str(atlas.resolve()):
        return previous
    rel = manifest_rel(atlas, manifest_path)
    if rel.startswith("../") or not atlas_git(atlas, "rev-parse", "--verify", "HEAD"):
        return previous
    committed, problems = load_revision(atlas, "HEAD", rel)
    if committed is not None:
        problems.extend(row_structure_problems(atlas, committed))
    if problems:
        raise SystemExit("sync: cannot read the committed ledger: " + "; ".join(problems))
    if committed is not None:
        old = {row["path"] for row in committed["rows"]}
        missing = old - {row["path"] for row in previous.get("rows", [])}
        if not previous or committed["schema_version"] > previous["schema_version"] or missing:
            raise SystemExit("sync: restore the existing ledger layout and all committed rows before "
                             "syncing" + (f": {', '.join(sorted(missing)[:10])}" if missing else ""))
    return previous


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--formal-math", type=Path, required=True, help="local Formal-Math git repository")
    ap.add_argument("--commit", required=True, help="Formal-Math commit to record (resolved to a full SHA)")
    ap.add_argument("--atlas", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--manifest", type=Path, help=f"default: <atlas>/{MANIFEST}")
    ap.add_argument("--rationales", type=Path, help="JSON: path -> {rationale, backport} for new divergences")
    ap.add_argument("--report", type=Path, help="also write the sync report here")
    a = ap.parse_args(argv)
    manifest_path = a.manifest or a.atlas / MANIFEST
    if a.report:
        report_target = a.report.resolve()
        if (report_target == manifest_path.resolve()
                or report_target.is_relative_to(shard_directory(manifest_path).resolve())):
            ap.error("--report must be outside the provenance ledger")
    if git(a.formal_math, "rev-parse", "--is-shallow-repository").decode().strip() != "false":
        raise SystemExit(f"sync: {a.formal_math} is a shallow clone; classification needs the full first-parent "
                         "history (run `git fetch --unshallow` first)")
    commit = git(a.formal_math, "rev-parse", "--verify", f"{a.commit}^{{commit}}").decode().strip()
    previous = previous_manifest(a.atlas, manifest_path)
    if previous and a.report and a.report.exists():
        for target in manifest_documents(manifest_path, previous):
            if target.exists() and a.report.samefile(target):
                ap.error("--report must not alias a provenance ledger file")
    rationales = load_json(a.rationales)
    if not isinstance(rationales, dict):
        raise SystemExit("sync: --rationales must be a JSON object mapping paths to {rationale, backport}")
    manifest, unexplained, local = build(a.atlas, a.formal_math, commit, previous, rationales)
    text = report(previous, manifest, local)
    print(text)
    if unexplained:
        print(f"FAIL [formal-math-sync]: {len(unexplained)} new divergence(s) without a rationale and "
              "backport status; manifest not written. Add them with --rationales:", file=sys.stderr)
        for path in unexplained:
            print(f"  {path}", file=sys.stderr)
        return 1
    if a.report:
        try:
            a.report.write_text(text + "\n", encoding="utf-8")
        except OSError as error:
            print(f"sync: cannot write report {a.report}: {error}; ledger not written", file=sys.stderr)
            return 1
    write_manifest(manifest_path, manifest)
    print(f"wrote ledger at {manifest_path} ({len(manifest['rows'])} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
