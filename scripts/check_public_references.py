#!/usr/bin/env python3
"""Check public PR content as data; never check out or execute the PR head."""

import argparse
import functools
import heapq
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.error
import urllib.request


PROFILE_ROOT = r"[/\\]+(?:data[/\\]+users|home|(?i:Users))[/\\]+"
# Line boundaries, as str.splitlines() sees them.
LINE_BREAKS = r"\n\r\x0b\x0c\x1c-\x1e\x85\u2028\u2029"
# A quoted profile: the opening quote sits right before the root (or its
# drive letter) and the matching quote closes the path later on the same
# line. The profile name ends at that quote or at the next separator, so
# punctuation, spaces and other quote characters inside it belong to the
# name. A quote right after the root is a text boundary; an empty or blank
# terminal name, "." and ".." are not profiles; only the exact CI accounts
# are exempt.
QUOTED_PROFILES = tuple(
    rf"(?:(?<={q}[A-Za-z]:)|(?<={q})){PROFILE_ROOT}"
    rf"(?!\s*['`\"])(?!(?:\.{{1,2}}|\s*){q})"
    rf"(?!runner(?:admin)?(?:{q}|[/\\]))"
    rf"[^/\\{LINE_BREAKS}{q}]+(?={q}|[/\\][^{LINE_BREAKS}{q}]*{q})"
    for q in ('"', "'", "`")
)


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
        "|".join(QUOTED_PROFILES)
        + r"|(?<![/\\])[/\\]+(?:data[/\\]+users|home|(?i:Users))[/\\]+"
        r"(?!\s*['`])(?:"
        # A profile name followed by a separator.
        r"(?!runner(?:admin)?[/\\])"
        r"[^/\\\x00-\x1f\x85\u2028\u2029\"<>|:*?]+[/\\]+"
        # A terminal profile name. It may start with punctuation only when a
        # name character follows. The exact CI accounts stay clean only
        # before a boundary or trailing punctuation that ends the text; a
        # longer name is still reported.
        r"|(?!\s|[.,;!)\]}]+(?:$|[\s/\\\x00-\x1f\x85\u2028\u2029\"'`<>|:*?]))"
        r"(?!runner(?:admin)?(?:[.,;!)\]}'`]+"
        r"(?:$|[\s/\\\x00-\x1f\x85\u2028\u2029\"<>|:*?])"
        r"|[^\S\x00-\x1f\x85\u2028\u2029]*"
        r"(?:$|[/\\\x00-\x1f\x85\u2028\u2029\"<>|:*?])))"
        r"[^/\\\x00-\x1f\x85\u2028\u2029\"<>|:*?\s'`]+"
        r")"
    ),
    "internal-source-path": re.compile(
        r"(?<!\w)(?:fbcode|fbsource)[/\\]+[a-zA-Z0-9_./\\-]+"
    ),
    "temporary-workspace": re.compile(
        r"(?<![/\\])[/\\]+(?:tmp|var[/\\]+tmp)[/\\]+[^/\\\s\"'`<>]+"
        r"[/\\]+(?:lanes|worktrees|shards|state)[/\\]+[^\s\"'`<>]+"
    ),
    "session-reference": re.compile(
        r"\b(?:session|agent)[ _-]?(?:id)?[\s:=/#]+"
        r"[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}\b",
        re.I,
    ),
    "private-planning-reference": re.compile(
        r"\b(?:F[0-9]{1,2}[.:-][A-Z][A-Z0-9]*(?:[.:-][A-Z0-9]+)+|"
        r"[A-Z]{2,8}-(?:[A-Z][0-9]{2}|[0-9]{2})\.[A-Z][0-9]{2}|"
        r"S[0-9]{1,2}\.L[0-9]{2})\b|"
        r"(?i:(?<![a-z0-9])f[0-9]{1,2}[/_-]s[0-9]{1,2}"
        r"\.?l[0-9]{2}(?![0-9]))"
    ),
    "private-roadmap-reference": re.compile(
        r"\b[A-Z]{2,8}(?:\.[A-Z][A-Z0-9]*){3,}\b"
    ),
}
# Filenames, symlink targets, branch names and commit identity names are
# literal values, not prose: a profile name there runs to the next separator,
# a line break or the end of the value, with the same root, dot and
# exact-account exceptions as a quoted path.
LITERAL_END = rf"(?=[{LINE_BREAKS}]|\Z)"
LITERAL_PROFILE = re.compile(
    rf"(?<![/\\]){PROFILE_ROOT}(?!\s*['`\"])"
    rf"(?!(?:\.{{1,2}}|\s*){LITERAL_END})"
    rf"(?!runner(?:admin)?(?:[/\\]|{LITERAL_END}))"
    rf"[^/\\{LINE_BREAKS}]+"
)
LITERAL_RULES = dict(RULES)
LITERAL_RULES["personal-workspace"] = re.compile(
    LITERAL_PROFILE.pattern + "|" + RULES["personal-workspace"].pattern
)

FILE_MODES = (b"100644", b"100755")
TEXT_MODES = FILE_MODES + (b"120000",)
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

# Public citations whose publisher identifier has an internal-reference shape.
# Only the identifier slot inside a complete recognized citation is exempt from
# the internal-reference rule; every other rule and every other match in the
# same text is still checked. Exact reviewed citations are written in full.
REVIEWED_CITATIONS = (
    "D. Cimasoni, *A generalized Kac-Ward formula*, J. Stat. Mech. (2010) P07023",
)
PUBLISHER_PII = r"(S[0-9]{7}[0-9X][0-9]{7}[0-9X])"
PUBLISHER_PII_SLOTS = (
    re.compile(
        r"(?<![\w./:-])(?:https://doi\.org/|doi:)?"
        r"10\.(?:1017|1112|1134|1137|1142|1155)/"
        + PUBLISHER_PII
        + r"(?![\w/?#&=%+-])"
    ),
    re.compile(
        r"(?<![\w./:-])https://www\.sciencedirect\.com/science/article/"
        r"(?:abs/)?pii/" + PUBLISHER_PII + r"(?![\w/-])"
    ),
)
REVIEWED_CITATION_SLOTS = tuple(
    re.compile(
        r"(?<!\w)"
        + re.escape(citation.rsplit(" ", 1)[0] + " ")
        + "("
        + re.escape(citation.rsplit(" ", 1)[1])
        + r")(?!\w)"
    )
    for citation in REVIEWED_CITATIONS
)


def valid_issn(pii):
    """A publisher PII starts with an ISSN: mod-11 check, never all zeros."""
    issn = pii[1:9]
    if not issn[:7].isdigit() or issn[:7] == "0000000":
        return False
    total = sum(int(c) * w for c, w in zip(issn[:7], range(8, 1, -1)))
    check = (11 - total % 11) % 11
    return issn[7] == ("X" if check == 10 else str(check))


def prose_regions(text, start):
    """Sorted, non-overlapping (start, end) prose regions of text."""
    if isinstance(start, int):
        return [(start, len(text))]
    return list(start)


def citation_slots(text, start):
    """Exempt spans inside the prose regions, in increasing order.

    A whole recognized citation must lie in one region (constant memory).
    """

    def slots(pattern, publisher, begin, end):
        for match in pattern.finditer(text, begin, end):
            if not publisher or valid_issn(match.group(1)):
                yield match.span(1)

    return itertools.chain.from_iterable(
        heapq.merge(
            *(slots(p, True, begin, end) for p in PUBLISHER_PII_SLOTS),
            *(slots(p, False, begin, end) for p in REVIEWED_CITATION_SLOTS),
        )
        for begin, end in prose_regions(text, start)
    )


# The path component of an http(s) URL is not a filesystem path. Only the
# filesystem-path rules skip a match wholly inside such a path; the query,
# fragment, other rules, and a path with an embedded drive-letter segment are
# still checked. A backslash ends the path, so backslash paths stay visible.
# RFC 1035 limits a host name to 253 characters without its optional trailing
# dot; with that dot and the largest port (":65535") an authority this checker
# can accept is at most 260 characters. Longer authorities never match, so they
# are neither copied nor cached and their paths stay strict.
MAX_AUTHORITY_CHARS = 253 + 1 + 6
# A control character (C0, DEL or C1) ends the path: it is never part of a
# URL, so text after one is checked like any other text.
URL_PATH = re.compile(
    r"(?<![\w+.-])(?i:https?)://([^\s/?#\\\"'<>`]{1,%d})"
    r"(/[^\s?#\\\"'<>`\x00-\x1f\x7f-\x9f]*)" % MAX_AUTHORITY_CHARS
)
FILESYSTEM_PATH_RULES = ("personal-workspace", "temporary-workspace")
# Only a public-looking DNS authority earns the URL-path reading: no userinfo,
# an optional numeric port, two or more valid labels, and an alphabetic or
# punycode top-level label outside special-use and private-use suffixes.
# Local, single-label, IP-literal, and unparsable authorities stay strict.
DNS_LABEL = re.compile(r"[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?")
PUBLIC_TLD = re.compile(r"[a-z]{2,63}|xn--[a-z0-9-]{1,59}")
NONPUBLIC_SUFFIXES = (
    "localhost",
    "local",
    "localdomain",
    "internal",
    "intranet",
    "private",
    "corp",
    "lan",
    "home",
    "home.arpa",
    "test",
    "invalid",
    "example",
    "example.com",
    "example.net",
    "example.org",
    "alt",
    "onion",
    "arpa",
)


# A URL path with any drive-letter segment gets no exemption at all, whatever
# dot segments follow; checked once per URL. The letter and the separator may
# each be literal or one level percent-encoded ("/C:", "/%43:", "/c%3A",
# "/%43%3A", "/C|", "/C%7C"); deeper encodings are out of scope.
DRIVE_LETTER = r"(?:[A-Za-z]|%(?:4[1-9A-Fa-f]|5[0-9Aa]|6[1-9A-Fa-f]|7[0-9Aa]))"
DRIVE_SEGMENT = re.compile(r"/" + DRIVE_LETTER + r"(?::|%3[Aa]|\||%7[Cc])")


def public_authority(authority):
    """True only for a public-looking DNS host; never resolves anything."""
    # The length check runs before the cache, so only bounded keys are kept.
    return len(authority) <= MAX_AUTHORITY_CHARS and _public_authority(
        authority
    )


@functools.lru_cache(maxsize=4096)
def _public_authority(authority):
    host, _, port = authority.lower().partition(":")
    if "@" in authority:
        return False
    if port and not (re.fullmatch(r"[0-9]{1,5}", port) and int(port) <= 65535):
        return False
    name = host[:-1] if host.endswith(".") else host
    labels = name.split(".")
    if len(labels) < 2 or len(name) > 253:
        return False
    if not all(DNS_LABEL.fullmatch(label) for label in labels):
        return False
    if not PUBLIC_TLD.fullmatch(labels[-1]):
        return False
    return not any(
        name == suffix or name.endswith("." + suffix)
        for suffix in NONPUBLIC_SUFFIXES
    )


def url_path_matches(pattern, text, start):
    """Filesystem-path matches outside public URL paths (lazy, ordered).

    A whole URL must lie in one prose region for its path to count.
    """
    regions = prose_regions(text, start)
    first = regions[0][0] if regions else len(text)
    paths = path = None
    for match in pattern.finditer(text):
        if match.start() < first:
            yield match
            continue
        if paths is None:
            paths = (
                m.span(2)
                for begin, end in regions
                for m in URL_PATH.finditer(text, begin, end)
                if public_authority(m.group(1))
                and not DRIVE_SEGMENT.search(m.group(2))
            )
            path = next(paths, None)
        while path is not None and path[1] <= match.start():
            path = next(paths, None)
        inside = (
            path is not None
            and path[0] <= match.start()
            and match.end() <= path[1]
        )
        if not inside:
            yield match


def rule_matches(rule, pattern, text, citation_start=None):
    """Matches of one rule after public-citation and URL-path recognition."""
    if citation_start is not None and rule in FILESYSTEM_PATH_RULES:
        yield from url_path_matches(pattern, text, citation_start)
        return
    if citation_start is None or rule != "internal-reference":
        yield from pattern.finditer(text)
        return
    slots = slot = None
    for match in pattern.finditer(text):
        if slots is None:
            # Recognize citations only once a reference-shaped match exists.
            slots = citation_slots(text, citation_start)
            slot = next(slots, None)
        while slot is not None and slot < match.span():
            slot = next(slots, None)
        if slot != match.span():
            yield match


def reference_spans(text, citation_start=None):
    """Spans the internal-reference rule reports (for tests and audits)."""
    pattern = RULES["internal-reference"]
    return [
        m.span()
        for m in rule_matches(
            "internal-reference", pattern, text, citation_start
        )
    ]


class IncompleteScan(RuntimeError):
    pass


class Findings(list):
    """One bounded report shared by every input in the requested range."""

    truncated = False


def scan(text, location, findings=None, rules=None, citation_start=None):
    """Return bounded locations/rules, never the matched private text."""
    findings = Findings() if findings is None else findings
    if findings.truncated:
        return findings
    safe_location = None
    for rule, pattern in (RULES if rules is None else rules).items():
        previous, line = 0, 1
        for match in rule_matches(rule, pattern, text, citation_start):
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
    # Locations quote filenames, so the literal reading applies.
    unsafe = any(p.search(text) for p in LITERAL_RULES.values())
    return "[redacted]" if unsafe else text


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


def scan_commit(raw, sha, findings=None, identity=None):
    if b"\n\n" not in raw:
        raise IncompleteScan("Malformed commit object")
    text = raw.decode("utf-8", errors="replace")
    # The whole raw object is scanned with raw line numbers. Citations and
    # public URL paths are recognized only in prose: the message after the
    # header/body separator and, with identities parsed, the message of each
    # supported embedded tag. Each recognized span lies in one region.
    findings = Findings() if findings is None else findings
    first = len(findings)
    body = text.index("\n\n") + 2
    regions = [(body, len(text))]
    if identity is not None:
        header = text[: body - 2].split("\n")
        starts = [0]
        for row in header:
            starts.append(starts[-1] + len(row) + 1)
        regions = [
            (starts[top - 1], starts[bottom] - 1)
            for top, bottom in tag_messages(header)
        ] + regions
    scan(text, "commit " + sha, findings, citation_start=regions)
    if identity is None:
        return findings
    # Header values are literal, not prose: identity names (read like Git
    # reads them) and every other header value, including unknown headers
    # and an embedded merge tag's header. Only an embedded tag message stays
    # text. A terminal profile that only the literal reading finds is added
    # at its raw header line, unless the text scan already reported it.
    header = text[: text.index("\n\n")].split("\n")
    values = header_values(header)
    for role, name in zip(("author", "committer"), identity):
        # Git's own parser must agree with the first identity line.
        parsed = [value for line, kind, value in values if kind == role]
        if not parsed or parsed[0] != name:
            raise IncompleteScan("Unparsed commit identity")
    reported = {
        f["line"] for f in findings[first:] if f["rule"] == "personal-workspace"
    }
    for line, _, value in values:
        if line not in reported and LITERAL_PROFILE.search(value):
            reported.add(line)
            scan(
                "\n" * (line - 1) + value,
                "commit " + sha,
                findings,
                {"personal-workspace": LITERAL_PROFILE},
            )
    return findings


def identity_name(value):
    """Git's identity name: text before "<", without trailing ASCII
    whitespace. Without a "<", the whole value is kept, which is stricter."""
    name, bracket, _ = value.partition("<")
    return name.rstrip(" \t\n\r") if bracket else value


TAG_OBJECT = re.compile(r"object (?:[0-9a-f]{40}|[0-9a-f]{64})")
TAG_FIELDS = (
    re.compile(r"type (?:commit|tree|blob|tag)"),
    re.compile(r"tag \S.*"),
    re.compile(r"tagger .*"),
)


def supported_tags(header):
    """Line numbers of mergetag headers whose embedded tag header is the
    supported shape: "object <id>", then "type", "tag" and an optional
    "tagger" continuation, in that order, closed by a blank continuation."""
    supported, start, fields = set(), None, -1
    for line, row in enumerate(header, 1):
        if start is not None and row.startswith(" "):
            field = row[1:]
            if field == "":
                if fields >= 2:
                    supported.add(start)
                start = None
            elif 0 <= fields < 3 and TAG_FIELDS[fields].fullmatch(field):
                fields += 1
            else:
                fields = -1
            continue
        start = None
        key, _, value = row.partition(" ")
        if key == "mergetag":
            start = line
            fields = 0 if TAG_OBJECT.fullmatch(value) else -1
    return supported


def tag_messages(header):
    """(first, last) 1-based line numbers of each supported tag's message:
    after its blank separator, up to its first signature armor line."""
    supported, messages = supported_tags(header), []
    state, top = None, None

    def close(last):
        if top is not None and last >= top:
            messages.append((top, last))

    for line, row in enumerate(header, 1):
        if state and row.startswith(" "):
            if state == "header" and row == " ":
                state, top = "message", line + 1
            elif state == "message" and row[1:].startswith("-----BEGIN "):
                close(line - 1)
                state = "opaque"
            continue
        if state == "message":
            close(line - 1)
        key = row.partition(" ")[0]
        state = "header" if key == "mergetag" and line in supported else None
        top = None
    if state == "message":
        close(len(header))
    return messages


def header_values(header):
    """(line, kind, value) for each raw header line. Every header byte is
    covered except the message of a supported embedded merge tag, which stays
    prose like the commit message. An identity line gives its Git name and,
    separately, the text inside and after its brackets; other lines give the
    whole line, key included. Only a supported tag (see supported_tags) has
    a tagger identity or a prose message; any other shape keeps its whole
    payload literal. A tag signature is opaque data, from its first armor
    line to the end of that tag."""
    values, supported = [], supported_tags(header)
    tag = tag_header = ok = signature = False
    for line, row in enumerate(header, 1):
        if row.startswith(" ") and tag:
            field = row[1:]
            if tag_header and field == "":
                tag_header = False
            elif tag_header and ok and field.startswith("tagger "):
                values += identity_values(line, "tagger", field[7:])
            elif tag_header:
                values.append((line, "tag-header", field))
            else:
                signature = signature or field.startswith("-----BEGIN ")
                if signature or not ok:
                    values.append((line, "tag-body", field))
            continue
        if row.startswith(" "):
            values.append((line, "continuation", row[1:]))
            continue
        key, _, value = row.partition(" ")
        tag = tag_header = key == "mergetag"
        ok, signature = tag and line in supported, False
        if key in ("author", "committer"):
            values += identity_values(line, key, value)
        else:
            values.append((line, key, row))
    return values


def identity_values(line, kind, value):
    email, _, rest = value.partition("<")[2].partition(">")
    return [
        (line, kind, identity_name(value)),
        (line, kind + "-email", email),
        (line, kind + "-rest", rest),
    ]


def tree_entries(root, rev):
    """Every (mode, object, path) entry of a commit's tree, recursively."""
    entries = set()
    for row in git(root, "ls-tree", "-r", "-z", "--full-tree", rev).split(
        b"\0"
    ):
        if row:
            info, path = row.split(b"\t", 1)
            mode, _, obj = info.split()
            entries.add((mode, obj, path))
    return entries


def unvetted_parents(root, base, commits, exclusions):
    """Boundary parents whose tree names were never checked or trusted.

    Outgoing parents were scanned, public tips are trusted current trees, and
    ancestors of base are the declared boundary. Only with public tips can a
    parent be none of these: history a public tip reached but no longer has.
    """
    if not exclusions:
        return set()
    tips = {tip[1:].encode() for tip in exclusions}
    outgoing = {row[0] for row in commits}
    found = set()
    for parent in {p for row in commits for p in row[1:]}:
        if parent in outgoing or parent in tips:
            continue
        ancestor = subprocess.run(
            ["git", "-C", str(root), "merge-base", "--is-ancestor"]
            + [parent.decode(), base],
            capture_output=True,
            timeout=180,
        ).returncode
        if ancestor not in (0, 1):
            raise IncompleteScan("Git could not compare public history")
        if ancestor == 1:
            found.add(parent)
    return found


def public_history_entries(root, base, commits, exclusions, public):
    """Entries outgoing commits inherit from excluded non-base history.

    With public tips, the walk stops at commits only reachable from them. An
    entry such a boundary parent has, that no public tip's current tree has,
    and that its outgoing child keeps unchanged, was never checked by any diff
    in the walk; report it as new in that child.
    """
    if not exclusions:
        return {}
    tips = {tip[1:].encode() for tip in exclusions}
    outgoing = {row[0] for row in commits}
    inherited, cache = {}, {}

    def entries(rev):
        if rev not in cache:
            cache[rev] = tree_entries(root, rev.decode())
        return cache[rev]

    for row in commits:
        for parent in row[1:]:
            if parent in outgoing or parent in tips:
                continue
            ancestor = subprocess.run(
                ["git", "-C", str(root), "merge-base", "--is-ancestor"]
                + [parent.decode(), base],
                capture_output=True,
                timeout=180,
            ).returncode
            if ancestor not in (0, 1):
                raise IncompleteScan("Git could not compare public history")
            if ancestor == 0:
                continue  # The declared base boundary.
            unvetted = entries(parent) - public
            if unvetted:
                kept = unvetted & entries(row[0])
                inherited.setdefault(row[0], set()).update(kept)
    return inherited


def check_range(root, base, head, metadata=None, public=()):
    """Scan commits reachable from head but not from base or public tips.

    Public tips are full commit SHAs the caller has just fetched and verified
    as already published (local pre-push use); this function cannot prove it.
    Their history is not walked again, but only objects in a tip's current
    tree are treated as already public: content a public commit later removed
    is checked again if a new commit or merge brings it back.
    """
    base, head = oid(base), oid(head)
    git(root, "cat-file", "-e", base + "^{commit}")
    git(root, "cat-file", "-e", head + "^{commit}")
    exclusions = []
    for tip in public:
        tip = oid(tip)
        if git(root, "cat-file", "-t", tip) != b"commit\n":
            raise IncompleteScan("Each public tip must be a commit")
        exclusions.append("^" + tip)
    git(root, "merge-base", base, head)
    revisions = [head, "^" + base, *exclusions]
    commits = [
        row.split()
        for row in git(root, "rev-list", "--parents", *revisions).splitlines()
    ]
    findings, blobs, paths, symlinks = Findings(), {}, set(), {}
    introduced = set(
        git(
            root,
            "rev-list",
            "--objects",
            "--no-object-names",
            head,
            "^" + base,
        ).splitlines()
    )
    public_entries = set()
    for tip in exclusions:
        # Entries and names in a public tip's current tree are already public;
        # editing such a file does not re-report its name. Removed ones count.
        public_entries |= tree_entries(root, tip[1:])
        introduced.difference_update(
            git(
                root,
                "rev-list",
                "--objects",
                "--no-object-names",
                "--no-walk",
                tip[1:],
            ).splitlines()
        )
    public_paths = {path for _, _, path in public_entries}
    inherited = public_history_entries(
        root, base, commits, exclusions, public_entries
    )
    unvetted = unvetted_parents(root, base, commits, exclusions)
    outgoing = {row[0] for row in commits}

    def check_entry(
        sha, mode, blob, raw_path, status, new_entry, new_name, restored=False
    ):
        if mode not in (b"100644", b"100755", b"120000"):
            raise IncompleteScan("Changed submodule or unsupported tree entry")
        path = raw_path.decode("utf-8", errors="surrogateescape")
        paths.add(path)
        # A name is new where no checked or trusted parent has that path;
        # changing an existing path's contents or mode does not rename it.
        if new_name and raw_path not in public_paths:
            scan(path, "filename in commit " + sha, findings, LITERAL_RULES)
            checked_names.add(raw_path)
        # Symlink targets are always strict, so a new symlink entry is
        # scanned even when its bytes were accepted earlier as file text.
        strict_link = mode == b"120000" and new_entry
        # Git omits base-history content inherited by a merge. A new
        # destination still receives the filename check above, and content a
        # merge restores after the current snapshots dropped it is scanned.
        if blob not in introduced and not strict_link and not restored:
            return
        if status not in (b"A", b"C", b"M", b"T"):
            raise IncompleteScan("Unsupported change status")
        blob = oid(blob.decode("ascii"))
        location = path + " @ " + sha
        if strict_link:
            # Strict wins for a shared blob and reports the symlink.
            symlinks.setdefault(blob, location)
        blobs.setdefault(blob, location)

    def diff_records(sha, merge):
        """ACMT records against every parent, and for a merge the paths
        that differ from every parent (its combined diff)."""
        combined = None
        if merge:
            filenames = git(
                root,
                "diff-tree",
                "--root",
                "-r",
                "-c",
                "--name-only",
                "-z",
                "--no-commit-id",
                "--no-renames",
                "--no-ext-diff",
                sha,
                "--",
            ).split(b"\0")
            if filenames[-1] != b"":
                raise IncompleteScan("Incomplete combined filename diff")
            combined = set(filenames[:-1])
        # Every parent of a merge matters. Inspect intermediate versions too,
        # including files added and later removed before the final head.
        raw = git(
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
        if raw[-1] != b"" or (len(raw) - 1) % 2:
            raise IncompleteScan("Incomplete raw tree diff")
        records = []
        for index in range(0, len(raw) - 1, 2):
            header, raw_path = raw[index : index + 2]
            fields = header.split()
            if len(fields) != 5 or not fields[0].startswith(b":"):
                raise IncompleteScan("Malformed raw tree diff")
            old_mode, mode, old_blob, blob, status = fields
            records.append(
                (mode, blob, raw_path, status, old_mode[1:], old_blob)
            )
        return records, combined

    diffs = {}
    for commit in commits:
        sha = oid(commit[0].decode("ascii"))
        diffs[commit[0]] = diff_records(sha, len(commit) > 2)
    # What was actually checked so far, in parent-before-child order: names
    # scanned as filenames, blobs scanned as content (the blobs and symlinks
    # maps, strict symlink scans in the latter). A visited entry whose name
    # or bytes were skipped does not count.
    checked_names = set()
    base_entries = tree_entries(root, base) if commits else set()
    current_entries = base_entries | public_entries
    current_files = {
        obj for mode, obj, _ in current_entries if mode in TEXT_MODES
    }
    current_links = {
        obj for mode, obj, _ in current_entries if mode == b"120000"
    }
    snapshots = {}

    def snapshot(rev):
        if rev not in snapshots:
            snapshots[rev] = tree_entries(root, rev.decode())
        return snapshots[rev]

    ancestry = {}

    def is_ancestor(older, newer):
        """Whether older is already contained in newer: merging it adds no
        history, so its tree cannot vouch for an entry newer dropped."""
        if (older, newer) not in ancestry:
            code = subprocess.run(
                ["git", "-C", str(root), "merge-base", "--is-ancestor"]
                + [older.decode(), newer.decode()],
                capture_output=True,
                timeout=180,
            ).returncode
            if code not in (0, 1):
                raise IncompleteScan("Git could not compare merge parents")
            ancestry[(older, newer)] = code == 0
        return ancestry[(older, newer)]

    def check_merge(sha, commit, records, combined):
        """Check each component of a merge entry against its own authority.

        A name is exempt if the current base, a public tip, or an eligible
        base-side parent has that exact path, or it was scanned already.
        Bytes and symlink targets are exempt only when the current base or a
        public tip holds them, an eligible parent holds the exact (mode,
        object, path) entry the merge kept, or they were scanned already. A
        same-path entry kept from an eligible parent can be a stale import;
        the commit graph cannot tell, and such an entry still qualifies."""
        # An eligible base-side parent is a direct parent reachable from the
        # supplied base and not contained in any other direct parent.
        base_side = [
            parent
            for parent in commit[1:]
            if parent not in outgoing
            and is_ancestor(parent, base.encode())
            and not any(
                other != parent and is_ancestor(parent, other)
                for other in commit[1:]
            )
        ]
        present = current_entries
        for parent in base_side:
            present = present | snapshot(parent)
        names = {path for _, _, path in present}
        # Byte authority: the current base and public tips vouch for bytes at
        # any path (a current symlink target may also be reused as file
        # contents); a base-side parent vouches only for its exact entry.
        seen = set()
        for mode, blob, raw_path, status, _, _ in records:
            if mode not in TEXT_MODES and (
                raw_path in combined
                or (mode, blob, raw_path) not in current_entries
            ):
                # Refuse an unsupported entry unless the current base or a
                # public tip holds that exact entry and the merge kept it.
                raise IncompleteScan("Changed submodule or unsupported entry")
            if raw_path in seen:
                continue
            seen.add(raw_path)
            if mode not in TEXT_MODES:
                continue  # Kept unchanged from a current snapshot.
            new_name = raw_path not in names and raw_path not in checked_names
            key = blob.decode("ascii")
            # Old file bytes the current snapshots do not vouch for and no
            # completed scan covered are scanned, kept or resolved alike.
            exact = (mode, blob, raw_path) in present
            bytes_ = mode in FILE_MODES and blob not in current_files
            bytes_ = bytes_ and not exact and key not in blobs
            if raw_path in combined:
                # A path the merge itself wrote is not inherited from any
                # parent, so only the current base and public tips (or a
                # completed scan) vouch for its bytes.
                bytes_ = mode in FILE_MODES and blob not in current_files
                bytes_ = bytes_ and key not in blobs
                check_entry(
                    sha, mode, blob, raw_path, status, True, new_name, bytes_
                )
                continue
            link = mode == b"120000" and blob not in current_links
            link = link and not exact and key not in symlinks
            if new_name or link or bytes_:
                check_entry(
                    sha, mode, blob, raw_path, status, link, new_name, bytes_
                )

    # Git's own parser supplies the author and committer names.
    fields = (
        git(
            root,
            "log",
            "--no-walk=unsorted",
            "--no-mailmap",
            "--stdin",
            "-z",
            "--format=%H%x00%an%x00%cn",
            input_data=b"".join(commit[0] + b"\n" for commit in commits),
        ).split(b"\0")
        if commits
        else []
    )
    identities = {}
    for i in range(0, len(fields) - 2, 3):
        identities[fields[i].decode("ascii")] = tuple(
            value.decode("utf-8", errors="replace")
            for value in fields[i + 1 : i + 3]
        )
    # Parents before children, so completed checks are known to merges.
    position = {
        row: index
        for index, row in enumerate(
            git(
                root, "rev-list", "--topo-order", "--reverse", *revisions
            ).split()
        )
    }
    if set(position) != {row[0] for row in commits}:
        raise IncompleteScan("Inconsistent commit order")
    for commit in sorted(commits, key=lambda row: position[row[0]]):
        sha = oid(commit[0].decode("ascii"))
        if sha not in identities:
            raise IncompleteScan("Unparsed commit identity")
        scan_commit(
            git(root, "cat-file", "commit", sha),
            sha,
            findings,
            identities[sha],
        )
        # Entries inherited unchanged from excluded public history that the
        # public tips no longer contain are new relative to those snapshots.
        for mode, blob, raw_path in sorted(inherited.get(commit[0], ())):
            check_entry(sha, mode, blob, raw_path, b"A", True, True)
        records, combined = diffs[commit[0]]
        if len(commit) <= 2:
            for mode, blob, raw_path, status, old_mode, old_blob in records:
                # One parent: an added path is a new name; a modified or
                # retyped path keeps it unless that parent is unchecked.
                new_name = status == b"A" or (
                    len(commit) == 2 and commit[1] in unvetted
                )
                # Old bytes the current base and public tips no longer hold
                # are scanned again when a commit brings them back. Making a
                # base-history file executable, bytes and path unchanged,
                # brings nothing back; the skip is not a completed scan.
                executable_only = (
                    len(commit) == 2
                    and (old_mode, mode) == (b"100644", b"100755")
                    and old_blob == blob
                    and status == b"M"
                    and blob not in introduced
                    and is_ancestor(commit[1], base.encode())
                )
                bytes_ = (
                    mode in FILE_MODES
                    and not executable_only
                    and blob not in current_files
                    and blob.decode("ascii") not in blobs
                )
                check_entry(
                    sha, mode, blob, raw_path, status, True, new_name, bytes_
                )
        else:
            check_merge(sha, commit, records, combined)

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
            scan(
                text,
                symlinks.get(blob, location),
                findings,
                LITERAL_RULES if blob in symlinks else None,
                citation_start=None if blob in symlinks else 0,
            )
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
                {
                    k: p
                    for k, p in LITERAL_RULES.items()
                    if k not in identifiers
                },
            )
            scan(
                value.upper().replace("_", "-"),
                "PR branch",
                findings,
                {k: RULES[k] for k in identifiers},
            )
        else:
            scan(value, "PR " + field, findings, citation_start=0)
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
    parser.add_argument(
        "--public",
        action="append",
        default=[],
        help="Local mode: full SHA of an already-published commit to exclude "
        "with its history (repeatable; fetch and verify it first)",
    )
    args = parser.parse_args(argv)
    try:
        if args.pr is not None:
            if (
                args.pr <= 0
                or not args.github_repository
                or args.base
                or args.head
                or args.metadata
                or args.public
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
            result = check_range(
                args.repo_root, args.base, args.head, metadata, args.public
            )
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
