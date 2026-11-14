#!/usr/bin/env python3
"""Regenerate provenance/formal-math-sync.json from a local Formal-Math checkout.

    scripts/sync_formal_math.py --formal-math ~/formal-math --commit <sha> \\
        [--rationales divergences.json] [--report sync-report.md]

Reads Formal-Math only through `git` in the given local repository (the objects of `--commit`
and its first-parent history); it never fetches, so internal automation fetches the pinned
commit first. Classifies every `.lean` file under the ATLAS root libraries, writes the manifest,
and prints a sync report: added, removed, changed, and diverged rows.

Fails closed, writing nothing, when a file newly diverges from Formal-Math without a rationale
and backport status. Give them with `--rationales`, a JSON object mapping each path to
{"rationale": "...", "backport": "..."}; rows already diverged in the current manifest keep
theirs. Output is deterministic for a fixed ATLAS tree and upstream commit.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_formal_math_sync import (  # noqa: E402  (the checker owns the header parser)
    MANIFEST, ROOTS, SCHEMA_VERSION, count_rows, dump_manifest, is_flt, leading_notice,
    library_files, rows_digest, sha256, split_published, upstream_body,
)

ZERO = "0" * 40
FLT_RATIONALE = "third-party FLT content; keeps its own copyright header"


def git(repo: Path, *args: str) -> bytes:
    return subprocess.run(["git", "-C", str(repo), "-c", "core.quotepath=off", *args],
                          check=True, capture_output=True).stdout


class Blobs:
    """Batch blob reader over `git cat-file --batch`."""

    def __init__(self, repo: Path) -> None:
        self.proc = subprocess.Popen(["git", "-C", str(repo), "cat-file", "--batch"],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def read(self, oid: str) -> bytes:
        assert self.proc.stdin and self.proc.stdout
        self.proc.stdin.write(oid.encode() + b"\n")
        self.proc.stdin.flush()
        header = self.proc.stdout.readline().split()
        if len(header) != 3 or header[1] != b"blob":
            raise SystemExit(f"sync: cannot read blob {oid}: {header!r}")
        data = self.proc.stdout.read(int(header[2]))
        self.proc.stdout.read(1)
        return data

    def close(self) -> None:
        if self.proc.stdin:
            self.proc.stdin.close()
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
        return {"disposition": "local", "rationale": FLT_RATIONALE}
    # Candidate (notice, header) readings of the ATLAS file, keyed by the hash of the body they leave.
    readings: list[tuple[str, str]] = [("", "meta")]
    notice = leading_notice(text)
    if notice:
        readings.append((notice, "meta"))
    readings.append(("", "upstream"))
    bodies: dict[str, tuple[str, str]] = {}
    for n, header in readings:
        body = split_published(text, n, header)[0]
        if body is not None:
            bodies.setdefault(sha256(body), (n, header))

    def match(source: str) -> tuple[str, dict] | None:
        digest = sha256(upstream_body(source))
        if digest not in bodies:
            return None
        n, header = bodies[digest]
        if header == "upstream" and source != text:
            return None  # a kept third-party header must be the upstream header byte for byte
        fields = {"upstream_sha256": digest}
        if n:
            fields["notice"] = n
        if header == "upstream":
            fields["header"] = "upstream"
        return digest, fields

    if up_text is None:
        deleted = next((c for c, oid in versions if oid == ZERO), None)
        if deleted is None:
            return {"disposition": "local"}
        return {"disposition": "retired", "upstream_commit": deleted}
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


def load_json(path: Path | None) -> dict:
    if path is None or not path.is_file():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def build(atlas: Path, repo: Path, commit: str, repository: str, previous: dict,
          rationales: dict) -> tuple[dict, list[str]]:
    """Return (manifest, paths that newly diverged without a rationale)."""
    files, links = library_files(atlas)
    if links:
        raise SystemExit("sync: symlinked paths under the root libraries: " + ", ".join(links))
    tree = upstream_tree(repo, commit)
    history = upstream_history(repo, commit, files)
    old_rows = {row["path"]: row for row in previous.get("rows", [])}
    blobs = Blobs(repo)
    rows, unexplained = [], []
    try:
        for path in sorted(files):
            data = (atlas / path).read_bytes()
            text = data.decode("utf-8", "replace")
            oid = tree.get(path)
            up_text = blobs.read(oid).decode("utf-8", "replace") if oid else None
            row = {"path": path, "published_sha256": sha256(data)}
            row.update(classify(text, up_text, history.get(path, []), oid, blobs))
            if row["disposition"] == "diverged":
                given = rationales.get(path) or {}
                old = old_rows.get(path, {})
                source = given if given.get("rationale") else old if old.get("disposition") == "diverged" else {}
                if source.get("rationale") and source.get("backport"):
                    row["rationale"], row["backport"] = source["rationale"], source["backport"]
                else:
                    unexplained.append(path)
            rows.append(row)
    finally:
        blobs.close()
    toolchain = (atlas / "lean-toolchain").read_text().strip()
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "upstream": {"repository": repository, "commit": commit},
        "lean_toolchain": toolchain,
        "roots": list(ROOTS),
        "counts": count_rows(rows),
        "total": len(rows),
        "rows_digest": rows_digest(rows),
        "rows": rows,
    }
    return manifest, unexplained


def report(previous: dict, manifest: dict) -> str:
    old = {row["path"]: row for row in previous.get("rows", [])}
    new = {row["path"]: row for row in manifest["rows"]}
    keys = ("disposition", "published_sha256", "upstream_sha256", "notice", "header")
    added = sorted(new.keys() - old.keys())
    removed = sorted(old.keys() - new.keys())
    changed = sorted(p for p in new.keys() & old.keys() if any(new[p].get(k) != old[p].get(k) for k in keys))
    diverged = [p for p in sorted(new) if new[p]["disposition"] == "diverged"]
    up = manifest["upstream"]
    lines = [f"# Formal-Math sync report: {up['repository']}@{up['commit']}", "",
             f"Previous upstream commit: {previous.get('upstream', {}).get('commit', 'none')}", "",
             "| Disposition | Files |", "| --- | ---: |"]
    lines += [f"| {d} | {n} |" for d, n in manifest["counts"].items()]
    lines += [f"| total | {manifest['total']} |", ""]

    def section(title: str, paths: list[str], detail=lambda p: "") -> None:
        lines.append(f"## {title} ({len(paths)})")
        lines.extend(f"- `{p}`{detail(p)}" for p in paths)
        lines.append("")

    section("Added", added, lambda p: f": {new[p]['disposition']}")
    section("Removed", removed, lambda p: f": was {old[p]['disposition']}")
    section("Changed", changed,
            lambda p: f": {old[p]['disposition']} -> {new[p]['disposition']}"
            + ("" if old[p]["published_sha256"] == new[p]["published_sha256"] else ", ATLAS bytes changed"))
    section("Diverged", diverged, lambda p: f": {new[p].get('rationale', 'NO RATIONALE')} "
            f"(backport: {new[p].get('backport', 'none')})")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--formal-math", type=Path, required=True, help="local Formal-Math git repository")
    ap.add_argument("--commit", required=True, help="Formal-Math commit to record (resolved to a full SHA)")
    ap.add_argument("--repository", default="fairinternal/formal-math")
    ap.add_argument("--atlas", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--manifest", type=Path, help=f"default: <atlas>/{MANIFEST}")
    ap.add_argument("--rationales", type=Path, help="JSON: path -> {rationale, backport} for new divergences")
    ap.add_argument("--report", type=Path, help="also write the sync report here")
    a = ap.parse_args(argv)
    manifest_path = a.manifest or a.atlas / MANIFEST
    commit = git(a.formal_math, "rev-parse", "--verify", f"{a.commit}^{{commit}}").decode().strip()
    previous = load_json(manifest_path)
    manifest, unexplained = build(a.atlas, a.formal_math, commit, a.repository, previous,
                                  load_json(a.rationales))
    text = report(previous, manifest)
    if a.report:
        a.report.write_text(text + "\n", encoding="utf-8")
    print(text)
    if unexplained:
        print(f"FAIL [formal-math-sync]: {len(unexplained)} new divergence(s) without a rationale and "
              "backport status; manifest not written. Add them with --rationales:", file=sys.stderr)
        for path in unexplained:
            print(f"  {path}", file=sys.stderr)
        return 1
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(dump_manifest(manifest), encoding="utf-8")
    print(f"wrote {manifest_path} ({manifest['total']} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
