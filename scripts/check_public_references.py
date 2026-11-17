#!/usr/bin/env python3
"""Check public PR content as data; never check out or execute the PR head."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.error
import urllib.request


RULES = {
    "internal-reference": re.compile(r"\b(?:[DTP][0-9]{5,}|[SNL][0-9]{6,})\b"),
    "private-host": re.compile(
        r"\b(?:internalfb\.com|internalmeta\.com|"
        r"fb\.workplace\.com|fburl\.com)\b",
        re.I,
    ),
    "private-machine": re.compile(
        r"\b(?:devvm|devgpu|twshared)[0-9]+(?:\.[a-z0-9.-]+)?\b", re.I
    ),
    "personal-workspace": re.compile(
        r"/(?:data/users|home|Users)/(?!runner/)[a-zA-Z0-9_.-]+/[^\s\"'`<>]+"
    ),
    "internal-source-path": re.compile(
        r"(?<![\w./])(?:fbcode|fbsource)/[a-zA-Z0-9_./-]+"
    ),
    "temporary-workspace": re.compile(
        r"/(?:tmp|var/tmp)/[^/\s\"'`<>]+/(?:lanes|worktrees|shards|state)/"
        r"[^\s\"'`<>]+"
    ),
    "session-reference": re.compile(
        r"\b(?:session|agent)[ _-]?(?:id)?[\s:=/#]+"
        r"[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}\b",
        re.I,
    ),
    "private-planning-reference": re.compile(
        r"\b(?:F[0-9]{1,2}[.:-][A-Z][A-Z0-9]*(?:[.:-][A-Z0-9]+)+|"
        r"[A-Z]{2,8}-(?:[A-Z][0-9]{2}|[0-9]{2})\.[A-Z][0-9]{2})\b"
    ),
}
MAX_BLOB_BYTES = 64 * 1024 * 1024
MAX_FINDINGS = 100
MAX_LOCATION_CHARS = 240
LFS_POINTER_PREFIXES = tuple(
    "version " + version + ending
    for version in (
        "https://git-lfs.github.com/spec/v1",
        "https://hawser.github.com/spec/v1",
        "http://git-media.io/v/2",
    )
    for ending in ("\n", "\r\n")
)


class IncompleteScan(RuntimeError):
    pass


class Findings(list):
    """One bounded report shared by every input in the requested range."""

    truncated = False


def scan(text, location, findings=None, rules=None):
    """Return bounded locations/rules, never the matched private text."""
    findings = Findings() if findings is None else findings
    if findings.truncated:
        return findings
    safe_location = None
    for rule, pattern in (RULES if rules is None else rules).items():
        previous, line = 0, 1
        for match in pattern.finditer(text):
            if len(findings) >= MAX_FINDINGS:
                findings.truncated = True
                return findings
            # Each prefix character is counted at most once per rule.
            line += text.count("\n", previous, match.start())
            previous = match.start()
            if safe_location is None:
                safe_location = redact(location)
                if len(safe_location) > MAX_LOCATION_CHARS:
                    safe_location = (
                        safe_location[: MAX_LOCATION_CHARS - 3] + "..."
                    )
            findings.append(
                {"location": safe_location, "line": line, "rule": rule}
            )
    return findings


def redact(text):
    # Mask the whole unsafe location, including any private hostname prefix.
    return "[redacted]" if any(p.search(text) for p in RULES.values()) else text


def git(root, *args, input_data=None):
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        input=input_data,
        capture_output=True,
        timeout=180,
    )
    if result.returncode:
        # Git's stderr may repeat an offending path or arbitrary commit text.
        raise IncompleteScan("Git could not read the complete requested range")
    return result.stdout


def oid(value):
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value):
        raise IncompleteScan("Expected an exact SHA-1 commit ID")
    return value


def scan_commit(raw, sha, findings=None):
    if b"\n\n" not in raw:
        raise IncompleteScan("Malformed commit object")
    return scan(
        raw.decode("utf-8", errors="replace"), "commit " + sha, findings
    )


def check_range(root, base, head, metadata=None):
    base, head = oid(base), oid(head)
    git(root, "cat-file", "-e", base + "^{commit}")
    git(root, "cat-file", "-e", head + "^{commit}")
    git(root, "merge-base", base, head)
    commits = git(root, "rev-list", base + ".." + head).splitlines()
    findings, blobs, paths = Findings(), {}, set()
    introduced = set(
        git(
            root,
            "rev-list",
            "--objects",
            "--no-object-names",
            base + ".." + head,
        ).splitlines()
    )
    for commit in commits:
        sha = oid(commit.decode("ascii"))
        scan_commit(git(root, "cat-file", "commit", sha), sha, findings)
        # Every parent of a merge matters. Inspect intermediate versions too,
        # including files added and later removed before the final head.
        records = git(
            root,
            "diff-tree",
            "--root",
            "-r",
            "-m",
            "-z",
            "--raw",
            "--no-commit-id",
            "--no-renames",
            "--no-abbrev",
            "--no-ext-diff",
            "--diff-filter=ACMT",
            sha,
            "--",
        ).split(b"\0")
        if records[-1] != b"" or (len(records) - 1) % 2:
            raise IncompleteScan("Incomplete raw tree diff")
        for index in range(0, len(records) - 1, 2):
            header, raw_path = records[index : index + 2]
            fields = header.split()
            if len(fields) != 5 or not fields[0].startswith(b":"):
                raise IncompleteScan("Malformed raw tree diff")
            _, mode, _, blob, status = fields
            if mode not in (b"100644", b"100755", b"120000"):
                raise IncompleteScan(
                    "Changed submodule or unsupported tree entry"
                )
            path = raw_path.decode("utf-8", errors="surrogateescape")
            paths.add(path)
            scan(path, "filename in commit " + sha, findings)
            # Base-history content is already published, even if main later
            # changed/deleted it. Do not attribute it to a base-merge PR.
            if blob not in introduced:
                continue
            if status not in (b"A", b"C", b"M", b"T"):
                raise IncompleteScan("Unsupported change status")
            blob = oid(blob.decode("ascii"))
            blobs.setdefault(blob, path + " @ " + sha)

    byte_count, binary_count = 0, 0
    if blobs:
        requests = ("\n".join(blobs) + "\n").encode("ascii")
        checks = git(
            root, "cat-file", "--batch-check", input_data=requests
        ).splitlines()
        if len(checks) != len(blobs):
            raise IncompleteScan("Incomplete blob inventory")
        sizes = []
        for expected, row in zip(blobs, checks):
            fields = row.split()
            if len(fields) != 3 or fields[:2] != [expected.encode(), b"blob"]:
                raise IncompleteScan("Missing blob object")
            size = int(fields[2])
            if not 0 <= size <= MAX_BLOB_BYTES:
                raise IncompleteScan("Changed file exceeds the scan size bound")
            sizes.append(size)
        byte_count = sum(sizes)
        if byte_count > 256 * 1024 * 1024:
            raise IncompleteScan("PR content exceeds the total scan size bound")
        payload = git(root, "cat-file", "--batch", input_data=requests)
        cursor = 0
        for (blob, location), size in zip(blobs.items(), sizes):
            end = payload.find(b"\n", cursor)
            expected = f"{blob} blob {size}".encode("ascii")
            if end < 0 or payload[cursor:end] != expected:
                raise IncompleteScan("Malformed blob stream")
            cursor = end + 1
            contents = payload[cursor : cursor + size]
            cursor += size
            if len(contents) != size or payload[cursor : cursor + 1] != b"\n":
                raise IncompleteScan("Incomplete file contents")
            cursor += 1
            text = contents.decode("utf-8", errors="replace")
            if text.lstrip().startswith(LFS_POINTER_PREFIXES):
                raise IncompleteScan(
                    "LFS content requires a separate full-content review"
                )
            binary_count += b"\0" in contents
            # Symlinks are text, not followed. No decompression or OCR.
            scan(text, location, findings)
        if cursor != len(payload):
            raise IncompleteScan("Unexpected trailing blob data")
    for field in ("title", "body", "branch"):
        value = (metadata or {}).get(field, "")
        if not isinstance(value, str):
            raise IncompleteScan("Malformed PR metadata")
        if field == "branch":
            identifiers = ("internal-reference", "private-planning-reference")
            scan(
                value,
                "PR branch",
                findings,
                {k: p for k, p in RULES.items() if k not in identifiers},
            )
            scan(
                value.upper().replace("_", "-"),
                "PR branch",
                findings,
                {k: RULES[k] for k in identifiers},
            )
        else:
            scan(value, "PR " + field, findings)
    return {
        "commits": len(commits),
        "files": len(paths),
        "blobs": len(blobs),
        "bytes": byte_count,
        "binary_files": binary_count,
        "findings": findings,
        "findings_truncated": findings.truncated,
    }


def get_pr(repo, number, token):
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo):
        raise IncompleteScan("Invalid repository name")
    request = urllib.request.Request(
        f"https://api.github.com/repos/{repo}/pulls/{number}",
        headers={
            "Authorization": "Bearer " + token,
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=45) as response:
            return json.load(response)
    except (urllib.error.URLError, ValueError) as error:
        raise IncompleteScan("Could not read current PR metadata") from error


def pr_snapshot(pr):
    try:
        return {
            "base": oid(pr["base"]["sha"]),
            "head": oid(pr["head"]["sha"]),
            "title": pr["title"],
            "body": pr["body"] or "",
            "branch": pr["head"]["ref"],
            "commits": pr["commits"],
        }
    except (KeyError, TypeError) as error:
        raise IncompleteScan("Incomplete PR metadata") from error


def check_pr(root, repo, number, token, expected_head=None):
    before = pr_snapshot(get_pr(repo, number, token))
    if expected_head is not None and before["head"] != oid(expected_head):
        raise IncompleteScan("Event head no longer matches the current PR head")
    # Fetch only from the workflow's configured repository, never a payload URL.
    git(root, "fetch", "--no-tags", "origin", before["base"])
    git(root, "fetch", "--no-tags", "origin", f"refs/pull/{number}/head")
    fetched = git(root, "rev-parse", "FETCH_HEAD").decode("ascii").strip()
    if fetched != before["head"]:
        raise IncompleteScan("PR head moved before its scan")
    result = check_range(root, before["base"], before["head"], before)
    if result["commits"] != before["commits"]:
        raise IncompleteScan(
            "Commit count differs from the PR's complete range"
        )
    if pr_snapshot(get_pr(repo, number, token)) != before:
        raise IncompleteScan(
            "PR content moved during its scan; run the check again"
        )
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--base")
    parser.add_argument("--head")
    parser.add_argument(
        "--metadata", type=Path, help="JSON with title/body/branch"
    )
    parser.add_argument("--github-repository")
    parser.add_argument("--pr", type=int)
    parser.add_argument("--expected-head", help="Event head SHA for a CI run")
    args = parser.parse_args(argv)
    try:
        if args.pr is not None:
            if (
                args.pr <= 0
                or not args.github_repository
                or args.base
                or args.head
                or args.metadata
            ):
                raise IncompleteScan("Use --pr with --github-repository only")
            token = os.environ.get("GH_TOKEN", "")
            if not token:
                raise IncompleteScan("A read-only GitHub token is required")
            result = check_pr(
                args.repo_root,
                args.github_repository,
                args.pr,
                token,
                args.expected_head,
            )
        else:
            if args.expected_head:
                raise IncompleteScan("--expected-head requires --pr")
            metadata = (
                json.loads(args.metadata.read_text()) if args.metadata else {}
            )
            if not isinstance(metadata, dict):
                raise IncompleteScan("Expected a metadata object")
            result = check_range(args.repo_root, args.base, args.head, metadata)
        print(json.dumps(result, ensure_ascii=True, sort_keys=True))
        return 1 if result["findings"] or result["findings_truncated"] else 0
    except (
        IncompleteScan,
        OSError,
        ValueError,
        subprocess.TimeoutExpired,
    ) as error:
        print(
            "Public-reference scan incomplete: " + redact(str(error)),
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
