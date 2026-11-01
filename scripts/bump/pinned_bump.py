#!/usr/bin/env python3
"""Pinned-release-only Lean/Mathlib bump automation.

Entry points (see .github/workflows/bump-pinned-release.yml and bump-guard.yml):

  select   Credential-free. Pick the next final release tag shared by every
           pinned dependency (Lean, Mathlib, CSLib, plus Physlib/repl where
           configured), or print an empty target. Never writes anything and
           never sees the App secret. Adapted from TauCeti's select/publish
           split: the selector cannot push, the publisher never executes
           upstream code.
  prepare  Read-only job (its default token is read-only, and the App
           token is never minted there). Revalidate the selected target,
           apply the tag to lean-toolchain, lakefile.toml, README/BACKPORTS
           version lines and the pin-policy constants (atlas
           check_lake_surface.py), run `lake update`, and verify the
           manifest. Writes only the working tree; commits nothing, pushes
           nothing, opens nothing, so `lake update` (which executes the
           newly tagged Lean/Lake) never sees a write-capable token.
           Hands only the prepared files (`prepared_files`) to the publish
           job via an artifact.
  finish   App-token only, on a fresh checkout whose default token stays
           read-only, with the verified staged tree overlaid. Commit the
           prepared tree, push it via an explicit push URL (the checkout
           never persists the App token), and open the bump PR. Reconciles an existing branch: an open PR
           on it means leave it alone; a branch with no PR and a tree
           identical to the prepared tree means create the missing PR
           (recovery from a push followed by a PR-creation failure); a
           branch with no PR and a different tree fails visibly for a human.
           No auto-merge: a human merges after CI green plus repairs.
  validate-prepared
           Trusted-script revalidation of a prepared tree after overlay,
           run in the publish job BEFORE the App token is minted (and
           again inside finish). The prepare job executes the newly
           tagged Lake code, which can rewrite any working-tree file,
           so filename-only staged-tree checks are not enough: this
           semantically revalidates every prepared file (manifest,
           lakefile, pin-policy, docs, migration ledgers) against the
           trusted base tree and the live tags, with a read-only token.
  merge-group-pr
           Parse a merge-group head ref (gh-readonly-queue/<branch>/
           pr-<number>-...) to its PR number, for the guard's merge_group
           run (see bump-guard.yml).
  guard    Run on every PR touching (or renaming) any file, from trusted
           base code (pull_request_target). Validates a pin-change PR
           without building it or running any PR code. Adapted from
           TauCeti's check-bump.sh: the complete lakefile compared after
           normalizing only the configured pinned revs; toolchain matches
           that tag and the tag exists in the Lean repo too; every direct
           manifest entry equals the base entry except rev/inputRev, with
           rev == that dep's tag SHA; the transitive manifest is exactly
           the union of the deps' manifests at the tag (conflicts between
           upstream manifests fail instead of silently winning); no
           duplicate package names; pin-policy constants match the new
           tag/SHAs; Mathlib@tag has a successful master-push build (so its
           oleans are published to the cache).

Nothing here tracks nightly, master, last-known-good, or first-known-bad
commits. A `-rc` tag is accepted only via an explicit manual dispatch with
--allow-rc, and then only onto a bump-pinned-rc/ branch.
"""

from __future__ import annotations

import argparse
import base64
import copy
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

FINAL_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)$")
RC_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)-rc(\d+)$")
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
PIN_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
GUARD_FILES = (
    ".github/workflows/bump-guard.yml",
    ".github/workflows/bump-pinned-release.yml",
    "scripts/bump/pinned_bump.py",
    "scripts/bump/pinned_deps.json",
    "scripts/bump/test_pinned_bump.py",
)


def version_key(tag: str):
    """Sortable key: a final release sorts after every rc of the same X.Y.Z."""
    m = FINAL_RE.match(tag)
    if m:
        return (int(m.group(1)), int(m.group(2)), int(m.group(3)), 1, 0)
    m = RC_RE.match(tag)
    if m:
        return (int(m.group(1)), int(m.group(2)), int(m.group(3)), 0, int(m.group(4)))
    raise ValueError(f"not a version tag: {tag!r}")


def is_final(tag: str) -> bool:
    return FINAL_RE.match(tag) is not None


def is_version_tag(tag: str, *, allow_rc: bool) -> bool:
    return is_final(tag) or (allow_rc and RC_RE.match(tag) is not None)


def load_config(root: Path) -> dict:
    path = Path(__file__).resolve().parent / "pinned_deps.json"
    with open(path, encoding="utf-8") as f:
        config = json.load(f)
    for dep in config["deps"]:
        if not dep.get("name") or not dep.get("repo"):
            raise ValueError(f"bad dep entry in {path}: {dep!r}")
    return config


def prepared_files(config: dict) -> list[str]:
    """Files the prepare step may hand to the publish step: the pin files
    plus the configured doc + pin-policy files. Everything else in the
    working tree (`.git`, Lake build outputs) stays behind."""
    files = ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
    files += [entry["path"] for entry in config.get("doc_replacements", [])]
    if config.get("pin_policy"):
        files.append(config["pin_policy"]["path"])
    files += list(config.get("migration_ledgers") or [])
    return sorted(set(files))


# Pin-coupled migration ledgers (AlgebraNotes). Their Mathlib API
# revisions and `pins` must track the pinned Mathlib/Lean release, or
# `scripts/check_algebra_notes_migration.py --source-revision HEAD` fails
# on the bump PR with stale pins. They are part of the prepared tree, so
# `prepared_files` includes them; the guard validates them on pin-change
# PRs. These paths are fixed repo paths, like lean-toolchain.
MIGRATION_LEDGER = "blueprint/migrations/AlgebraNotes.json"
MIGRATION_CHECKS = "blueprint/migrations/AlgebraNotesChecks.json"


def _migration_ledger_paths(config: dict) -> tuple[str, str]:
    ledgers = config.get("migration_ledgers") or []
    if len(ledgers) == 2:
        return str(ledgers[0]), str(ledgers[1])
    return MIGRATION_LEDGER, MIGRATION_CHECKS


def _canonical_json(value) -> bytes:
    """Canonical JSON bytes, matching inventory_v1.canonical: sorted keys,
    compact separators, no ASCII escaping, no NaN."""
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _content_sha256(value) -> str:
    return hashlib.sha256(_canonical_json(value)).hexdigest()


def _row_content_sha256(row: dict) -> str:
    return _content_sha256(
        {key: value for key, value in row.items() if key != "row_content_sha256"}
    )


def _ledger_identity_sha256(ledger: dict) -> str:
    return _content_sha256(
        {key: ledger[key] for key in ("book", "base", "sources", "pins")}
    )


def _lane_content_fingerprints(lane: str, triage_rows: list, api_rows: list) -> dict:
    """Mirror check_algebra_notes_migration.lane_content_fingerprints."""
    lane_triage = sorted(
        (
            {key: value for key, value in row.items() if key != "row_content_sha256"}
            for row in triage_rows
            if row["lane"] == lane
        ),
        key=lambda row: row["ordinal"],
    )
    declarations = [
        {"ordinal": row["ordinal"], "legacy_declarations": row["legacy_declarations"]}
        for row in lane_triage
    ]
    lane_apis = sorted(
        (
            {key: value for key, value in row.items() if key != "row_content_sha256"}
            for row in api_rows
            if row["lane"] == lane
        ),
        key=lambda row: row["id"],
    )
    return {
        "targets_content_sha256": _content_sha256(lane_triage),
        "declarations_content_sha256": _content_sha256(declarations),
        "api_rows_content_sha256": _content_sha256(lane_apis),
    }


def _expected_api_revision(module: str, *, mathlib_sha: str, base: str) -> str | None:
    if module.startswith("Mathlib."):
        return mathlib_sha
    if module.startswith("MathlibExt."):
        return base
    return None


def check_migration_ledger_pins(
    ledger: dict, checks: dict, *, mathlib_sha: str, lean_tag: str
) -> list[str]:
    """Pin-consistency problems for a (ledger, checks) pair at the given
    expected pins, mirroring the pin checks in
    check_algebra_notes_migration.py. Returns [] when the pair is
    consistent. This checks pins and content hashes, not whether the
    named Mathlib APIs still exist at the new pin; that is covered by
    the bump PR's Lean build."""
    problems: list[str] = []
    try:
        pins = ledger["pins"]
        base = ledger["base"]
    except (KeyError, TypeError):
        return ["migration ledger is missing pins/base"]
    if pins.get("mathlib") != mathlib_sha:
        problems.append(
            f"migration ledger pins.mathlib {pins.get('mathlib')!r} != {mathlib_sha!r}"
        )
    if pins.get("lean") != lean_tag:
        problems.append(
            f"migration ledger pins.lean {pins.get('lean')!r} != {lean_tag!r}"
        )
    for api in ledger.get("destination_apis", []):
        expected = _expected_api_revision(
            api.get("module", ""), mathlib_sha=mathlib_sha, base=base
        )
        if expected is None:
            problems.append(
                f"migration API {api.get('id')} has unexpected module "
                f"{api.get('module')!r}"
            )
        elif api.get("revision") != expected:
            problems.append(
                f"migration API {api.get('id')} revision is stale: "
                f"{api.get('revision')!r} != {expected!r}"
            )
    if checks.get("identity_sha256") != _ledger_identity_sha256(ledger):
        problems.append("migration checks identity_sha256 is stale")
    for api in checks.get("triage_apis", []):
        expected = _expected_api_revision(
            api.get("module", ""), mathlib_sha=mathlib_sha, base=base
        )
        if expected is None:
            problems.append(
                f"triage API {api.get('id')} has unexpected module "
                f"{api.get('module')!r}"
            )
        elif api.get("revision") != expected:
            problems.append(
                f"triage API {api.get('id')} revision is stale: "
                f"{api.get('revision')!r} != {expected!r}"
            )
        if api.get("row_content_sha256") != _row_content_sha256(api):
            problems.append(
                f"triage API {api.get('id')} has a stale row_content_sha256"
            )
    for source in checks.get("triage_sources", []):
        lane = source.get("lane")
        expected_fp = _lane_content_fingerprints(
            lane, checks.get("triage", []), checks.get("triage_apis", [])
        )
        for key, value in expected_fp.items():
            if source.get(key) != value:
                problems.append(f"triage source {lane} has a stale {key}")
    return problems


def _swap_once(text: str, needle: str, replacement: str, *, expected: int, label: str) -> str:
    count = text.count(needle)
    if count != expected:
        raise ValueError(
            f"cannot re-pin migration ledgers: expected {expected} {label}, "
            f"found {count}"
        )
    return text.replace(needle, replacement)


def repin_migration_ledgers(
    root: Path, target: str, shas: dict[str, str],
    *, ledger_rel: str = MIGRATION_LEDGER, checks_rel: str = MIGRATION_CHECKS,
) -> list[str]:
    """Re-pin the AlgebraNotes migration ledgers to a new release.

    The ledger's `pins` and every Mathlib.* API revision move to the new
    Mathlib SHA / Lean tag; MathlibExt.* revisions stay at the ledger
    `base` (the frozen audit base, not the bump). Content hashes that
    bind the changed rows (triage API `row_content_sha256`, lane
    `api_rows_content_sha256`, checks `identity_sha256`) are recomputed,
    so the pair still satisfies check_algebra_notes_migration.py.

    Fail-closed: the pre-bump pair must already be consistent with the
    tree being prepared from (its manifest Mathlib rev + toolchain), and
    every Mathlib API revision must be exactly the old pin. Anything else
    (a stale ledger, an unexpected revision, a mismatched hash) raises
    ValueError instead of rewriting audit pointers. The writes are
    textual (same-length SHA/tag swaps plus hash swaps), so the ledgers'
    committed formatting is unchanged; the result is re-parsed and
    re-checked against the new pins before returning.
    """
    ledger_path = root / ledger_rel
    checks_path = root / checks_rel
    try:
        ledger_text = ledger_path.read_text(encoding="utf-8")
        checks_text = checks_path.read_text(encoding="utf-8")
        ledger = json.loads(ledger_text)
        checks = json.loads(checks_text)
        manifest = load_manifest(root)
        old_mathlib = next(
            p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"
        )
        old_lean = f"leanprover/lean4:{toolchain_tag(root)}"
    except (OSError, json.JSONDecodeError, KeyError, StopIteration, ValueError) as exc:
        raise ValueError(f"cannot re-pin migration ledgers: {exc}") from exc
    new_mathlib = shas.get("mathlib")
    if not new_mathlib or not SHA_RE.fullmatch(new_mathlib):
        raise ValueError("cannot re-pin migration ledgers: missing/invalid mathlib SHA")
    new_lean = f"leanprover/lean4:{target}"
    pre = check_migration_ledger_pins(
        ledger, checks, mathlib_sha=old_mathlib, lean_tag=old_lean
    )
    if pre:
        raise ValueError(
            "cannot re-pin migration ledgers: pre-bump pair is inconsistent: "
            + "; ".join(pre)
        )
    if old_mathlib == new_mathlib and old_lean == new_lean:
        return []
    new_ledger = copy.deepcopy(ledger)
    new_ledger["pins"] = {"mathlib": new_mathlib, "lean": new_lean}
    mathlib_apis = [
        api for api in new_ledger.get("destination_apis", [])
        if api.get("module", "").startswith("Mathlib.")
    ]
    for api in mathlib_apis:
        api["revision"] = new_mathlib
    new_checks = copy.deepcopy(checks)
    mathlib_triage = [
        api for api in new_checks.get("triage_apis", [])
        if api.get("module", "").startswith("Mathlib.")
    ]
    for api in mathlib_triage:
        api["revision"] = new_mathlib
        api["row_content_sha256"] = _row_content_sha256(api)
    for source in new_checks.get("triage_sources", []):
        source.update(_lane_content_fingerprints(
            source["lane"], new_checks.get("triage", []),
            new_checks.get("triage_apis", []),
        ))
    new_checks["identity_sha256"] = _ledger_identity_sha256(new_ledger)
    new_ledger_text = _swap_once(
        ledger_text, f'"mathlib":"{old_mathlib}"', f'"mathlib":"{new_mathlib}"',
        expected=1, label="pins.mathlib occurrences",
    )
    new_ledger_text = _swap_once(
        new_ledger_text, f'"lean":"{old_lean}"', f'"lean":"{new_lean}"',
        expected=1, label="pins.lean occurrences",
    )
    new_ledger_text = _swap_once(
        new_ledger_text, f'"revision":"{old_mathlib}"',
        f'"revision":"{new_mathlib}"',
        expected=len(mathlib_apis), label="Mathlib destination_apis revisions",
    )
    new_checks_text = _swap_once(
        checks_text, f'"revision":"{old_mathlib}"',
        f'"revision":"{new_mathlib}"',
        expected=len(mathlib_triage), label="Mathlib triage_apis revisions",
    )
    for api in mathlib_triage:
        old_hash = next(
            a["row_content_sha256"] for a in checks["triage_apis"]
            if a["id"] == api["id"]
        )
        new_checks_text = _swap_once(
            new_checks_text,
            f'"row_content_sha256":"{old_hash}"',
            f'"row_content_sha256":"{api["row_content_sha256"]}"',
            expected=1, label=f"row_content_sha256 for {api['id']}",
        )
    old_identity = checks["identity_sha256"]
    new_checks_text, identity_count = re.subn(
        r'"identity_sha256"(\s*:\s*)"' + re.escape(old_identity) + r'"',
        lambda m: f'"identity_sha256"{m.group(1)}"{new_checks["identity_sha256"]}"',
        new_checks_text,
    )
    if identity_count != 1:
        raise ValueError(
            "cannot re-pin migration ledgers: expected 1 identity_sha256 "
            f"occurrences, found {identity_count}"
        )
    old_sources = {s["lane"]: s for s in checks.get("triage_sources", [])}
    for source in new_checks.get("triage_sources", []):
        old_fp = old_sources[source["lane"]]["api_rows_content_sha256"]
        new_fp = source["api_rows_content_sha256"]
        if old_fp != new_fp:
            new_checks_text = _swap_once(
                new_checks_text,
                f'"api_rows_content_sha256":"{old_fp}"',
                f'"api_rows_content_sha256":"{new_fp}"',
                expected=1,
                label=f"api_rows_content_sha256 for {source['lane']}",
            )
    ledger_path.write_text(new_ledger_text, encoding="utf-8")
    checks_path.write_text(new_checks_text, encoding="utf-8")
    re_ledger = json.loads(new_ledger_text)
    re_checks = json.loads(new_checks_text)
    post = check_migration_ledger_pins(
        re_ledger, re_checks, mathlib_sha=new_mathlib, lean_tag=new_lean
    )
    if post:
        raise ValueError(
            "cannot re-pin migration ledgers: re-pinned pair is inconsistent: "
            + "; ".join(post)
        )
    if re_ledger != new_ledger or re_checks != new_checks:
        raise ValueError(
            "cannot re-pin migration ledgers: re-parsed pair differs from "
            "the intended re-pinned pair"
        )
    return [ledger_rel, checks_rel]


def _is_existing_bump_pr(pr: dict, repo: str, branch: str) -> bool:
    """True if `pr` is this repo's bump PR on `branch` targeting main. A fork
    can use the predictable branch name `bump-pinned/<target>`, so the head
    repository (and the base branch) must match before the workflow treats
    a PR as its own."""
    head = pr.get("head") or {}
    return (
        head.get("ref") == branch
        and (head.get("repo") or {}).get("full_name") == repo
        and (pr.get("base") or {}).get("ref") == "main"
    )


def _is_superseded_candidate(pr: dict, repo: str, branch: str, target: str) -> bool:
    """True if `pr` is a same-repo bump PR on a strictly older target branch
    than `target` targeting main: the head repository must match, so a fork
    PR reusing a `bump-pinned/` branch name is never closed as superseded;
    the base must be main, so a bump PR intentionally targeting a
    maintenance or release branch is never closed; and a PR for a
    newer (or unparseable) target is never closed when this run publishes an
    older manual target."""
    head = pr.get("head") or {}
    ref = head.get("ref", "")
    if not (
        ref.startswith("bump-pinned/")
        and ref != branch
        and (head.get("repo") or {}).get("full_name") == repo
        and (pr.get("base") or {}).get("ref") == "main"
    ):
        return False
    try:
        return version_key(ref[len("bump-pinned/"):]) < version_key(target)
    except ValueError:
        return False


def _pr_is_bot_only(commits: list[dict], total: int | None) -> bool:
    """True if every fetched commit is bot-authored. Fails closed: if the
    PR reports more commits than were fetched, a later human repair commit
    may have been omitted, so the PR is not treated as bot-only."""
    if isinstance(total, int) and total > len(commits):
        return False
    authors = {(c.get("author") or {}).get("login", "") for c in commits}
    return bool(authors) and all(a.endswith("[bot]") for a in authors)


def parse_merge_group_head_ref(head_ref: str) -> int | None:
    """PR number from a merge-group head ref, or None if unparseable.

    Merge-group head refs look like
    ``gh-readonly-queue/main/pr-123-abcdef...``. A plain ``pr-123``
    also parses. Anything else returns None so the caller fails
    closed instead of guarding the wrong PR.
    """
    match = re.search(r"(?:^|/)pr-(\d+)(?:-|$)", head_ref or "")
    return int(match.group(1)) if match else None


def toolchain_tag(root: Path) -> str:
    text = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    prefix = "leanprover/lean4:"
    if not text.startswith(prefix):
        raise ValueError(f"unexpected lean-toolchain content: {text!r}")
    return text[len(prefix):]


def load_lakefile(root: Path) -> dict:
    with open(root / "lakefile.toml", "rb") as f:
        return tomllib.load(f)


def lakefile_requires(root: Path) -> list[dict]:
    requires = load_lakefile(root).get("require", [])
    if not isinstance(requires, list):
        raise ValueError("lakefile.toml [[require]] is not a list")
    return requires


def current_tag(root: Path, config: dict) -> str:
    """The single tag all pinned pins must agree on, or an error."""
    toolchain = toolchain_tag(root)
    revs = {}
    wanted = {dep["name"] for dep in config["deps"]}
    for entry in lakefile_requires(root):
        if entry.get("name") in wanted:
            revs[entry["name"]] = entry.get("rev")
    missing = wanted - set(revs)
    if missing:
        raise ValueError(f"lakefile.toml is missing pinned deps: {sorted(missing)}")
    tags = {toolchain, *revs.values()}
    if len(tags) != 1:
        raise ValueError(f"pinned tags disagree: toolchain={toolchain!r} revs={revs}")
    return toolchain


class GitHub:
    """Thin wrapper over `gh api`. Subclassed by the unit tests."""

    def __init__(self, repo: str | None = None):
        self.repo = repo or os.environ.get("GITHUB_REPOSITORY", "")

    def api(self, path: str):
        result = subprocess.run(
            ["gh", "api", path], text=True, capture_output=True, check=False
        )
        if result.returncode != 0:
            raise RuntimeError(f"gh api {path} failed: {result.stderr.strip()}")
        return json.loads(result.stdout)

    def tags(self, slug: str) -> list[dict]:
        return self.api(f"repos/{slug}/tags?per_page=100")

    def tag_sha(self, slug: str, tag: str) -> str | None:
        for entry in self.tags(slug):
            if entry.get("name") == tag:
                sha = entry.get("commit", {}).get("sha", "")
                return sha if SHA_RE.match(sha) else None
        return None

    def successful_master_build_run(self, slug: str, sha: str) -> int | None:
        """Id of a completed successful push build on master at sha, else None."""
        runs = self.api(
            f"repos/{slug}/actions/workflows/build.yml/runs"
            f"?head_sha={sha}&event=push&per_page=20"
        ).get("workflow_runs", [])
        for run in runs:
            if (
                run.get("head_branch") == "master"
                and run.get("status") == "completed"
                and run.get("conclusion") == "success"
            ):
                return run.get("id")
        return None

    def contents(self, slug: str, path: str, ref: str) -> bytes:
        data = self.api(f"repos/{slug}/contents/{path}?ref={ref}")
        if data.get("encoding") != "base64":
            raise ValueError(f"unexpected encoding for {path}@{ref}")
        return base64.b64decode(data["content"])

    def open_prs(self) -> list[dict]:
        if not self.repo:
            return []
        return self.api(f"repos/{self.repo}/pulls?state=open&per_page=100")

    def pr_commits(self, number: int) -> list[dict]:
        if not self.repo:
            return []
        commits: list[dict] = []
        page = 1
        while True:
            batch = self.api(
                f"repos/{self.repo}/pulls/{number}/commits?per_page=100&page={page}"
            )
            if not isinstance(batch, list):
                break
            commits.extend(batch)
            if len(batch) < 100:
                break
            page += 1
        return commits

    def close_pr(self, number: int, comment: str) -> None:
        if not self.repo:
            raise ValueError("GITHUB_REPOSITORY is required to close a PR")
        subprocess.run(
            ["gh", "pr", "close", str(number), "--repo", self.repo,
             "--comment", comment],
            text=True, capture_output=True, check=True,
        )


def select_target(
    client: GitHub, root: Path, config: dict,
    *, manual: str = "", allow_rc: bool = False,
) -> tuple[str, int | None, str]:
    """Return (target, mathlib_run_id, reason). Empty target means no-op."""
    current = current_tag(root, config)
    slugs = [config["toolchain_repo"]] + [dep["repo"] for dep in config["deps"]]
    tags_by_slug: dict[str, list[str]] = {}
    for slug in slugs:
        tags_by_slug[slug] = [
            entry["name"]
            for entry in client.tags(slug)
            if is_version_tag(entry.get("name", ""), allow_rc=allow_rc)
        ]
    if manual:
        if not is_version_tag(manual, allow_rc=allow_rc):
            raise ValueError(f"manual target {manual!r} is not a version tag")
        target = manual
        missing = [s for s in slugs if target not in tags_by_slug[s]]
        if missing:
            return "", None, f"manual target {target} is missing in: {', '.join(missing)}"
    else:
        candidates = sorted(
            {t for tags in tags_by_slug.values() for t in tags if is_final(t)},
            key=version_key,
        )
        target = ""
        for candidate in reversed(candidates):
            if version_key(candidate) <= version_key(current):
                break
            if all(candidate in tags_by_slug[s] for s in slugs):
                target = candidate
                break
        if not target:
            have = {
                s: max(tags_by_slug[s], key=version_key) if tags_by_slug[s] else "none"
                for s in slugs
            }
            return "", None, f"no newer final tag in every repo (current {current}); latest: {have}"
        if version_key(target) <= version_key(current):
            return "", None, f"target {target} is not newer than current {current}"
    mathlib = next(d for d in config["deps"] if d["name"] == "mathlib")
    sha = client.tag_sha(mathlib["repo"], target)
    if not sha:
        return "", None, f"could not resolve tag SHA for mathlib {target}"
    run_id = client.successful_master_build_run(mathlib["repo"], sha)
    if run_id is None:
        return "", None, (
            f"mathlib {target} ({sha}) has no completed successful master-push "
            "build yet, so its oleans may not be published; retry on a later tick"
        )
    return target, run_id, f"target {target} (mathlib {sha}, build run {run_id})"


def apply_replacements_to_text(
    text: str, replacements: list[dict], target: str, shas: dict[str, str]
) -> str:
    for entry in replacements:
        replacement = entry["replacement"].replace("{target}", target)
        for name, sha in shas.items():
            replacement = replacement.replace("{sha:" + name + "}", sha)
        if "{sha:" in replacement:
            raise ValueError(
                f"replacement {entry['replacement']!r} references an unresolved SHA"
            )
        # Resolve {g1}, {g2}, ... via a function, never a replacement
        # string: a backreference immediately followed by SHA digits
        # (e.g. \1 + "444...") would be parsed as a different group.
        def _repl(match, _replacement=replacement):
            out = _replacement
            for i in range(match.re.groups + 1):
                out = out.replace(f"{{g{i}}}", match.group(i) or "")
            return out

        new_text, count = re.subn(entry["pattern"], _repl, text)
        if count == 0:
            raise ValueError(
                f"replacement pattern {entry['pattern']!r} did not match"
            )
        text = new_text
    return text


def apply_pin_edits(
    root: Path, config: dict, current: str, target: str,
    shas: dict[str, str] | None = None,
) -> list[str]:
    """Edit toolchain, lakefile revs, doc + pin-policy version lines, and
    the pin-coupled migration ledgers. The ledgers move first, while the
    tree still carries the old pins, so the re-pin can validate the
    pre-bump pair against the tree being prepared from."""
    shas = shas or {}
    changed: list[str] = []
    ledgers = config.get("migration_ledgers") or []
    if ledgers:
        if len(ledgers) != 2:
            raise ValueError(
                f"migration_ledgers must list the ledger and checks files: {ledgers!r}"
            )
        changed += repin_migration_ledgers(
            root, target, shas, ledger_rel=ledgers[0], checks_rel=ledgers[1]
        )
    toolchain_path = root / "lean-toolchain"
    toolchain_path.write_text(f"leanprover/lean4:{target}\n", encoding="utf-8")
    changed.append("lean-toolchain")

    lakefile_path = root / "lakefile.toml"
    text = lakefile_path.read_text(encoding="utf-8")
    blocks = text.split("[[require]]")
    wanted = {dep["name"] for dep in config["deps"]}
    for i, block in enumerate(blocks[1:], start=1):
        name_match = re.search(r'(?m)^name\s*=\s*"([^"]+)"', block)
        if name_match and name_match.group(1) in wanted:
            new_block, count = re.subn(
                r'(?m)^(rev\s*=\s*")[^"]*(")', rf"\g<1>{target}\g<2>", block, count=1
            )
            if count != 1:
                raise ValueError(f"could not replace rev in lakefile block {i}")
            blocks[i] = new_block
    lakefile_path.write_text("[[require]]".join(blocks), encoding="utf-8")
    changed.append("lakefile.toml")

    for entry in config.get("doc_replacements", []):
        path = root / entry["path"]
        content = path.read_text(encoding="utf-8")
        new_content = apply_replacements_to_text(content, [entry], target, shas)
        if new_content != content:
            path.write_text(new_content, encoding="utf-8")
            changed.append(entry["path"])
    pin_policy = config.get("pin_policy")
    if pin_policy:
        path = root / pin_policy["path"]
        content = path.read_text(encoding="utf-8")
        new_content = apply_replacements_to_text(
            content, pin_policy["replacements"], target, shas
        )
        if new_content != content:
            path.write_text(new_content, encoding="utf-8")
            changed.append(pin_policy["path"])
    _ = current
    return changed


def load_manifest(root: Path) -> dict:
    with open(root / "lake-manifest.json", encoding="utf-8") as f:
        return json.load(f)


def direct_entries(manifest: dict) -> dict[str, dict]:
    return {
        pkg["name"]: pkg
        for pkg in manifest.get("packages", [])
        if not pkg.get("inherited", False)
    }


def check_no_duplicate_packages(manifest: dict, label: str) -> list[str]:
    names = [pkg.get("name") for pkg in manifest.get("packages", [])]
    dups = sorted({n for n in names if names.count(n) > 1})
    if dups:
        return [f"{label} has duplicate package names: {dups}"]
    return []


def verify_manifest(
    client: GitHub, root: Path, config: dict, target: str,
    base_manifest: dict | None = None,
) -> list[str]:
    """Check direct + transitive manifest entries against deps@target."""
    problems: list[str] = []
    manifest = load_manifest(root)
    problems.extend(check_no_duplicate_packages(manifest, "PR manifest"))
    if base_manifest is not None:
        problems.extend(check_no_duplicate_packages(base_manifest, "base manifest"))
        base_top = {k: v for k, v in base_manifest.items() if k != "packages"}
        pr_top = {k: v for k, v in manifest.items() if k != "packages"}
        if base_top != pr_top:
            diff = sorted(
                k for k in set(base_top) | set(pr_top) if base_top.get(k) != pr_top.get(k)
            )
            problems.append(f"manifest top-level fields differ from base: {diff}")
    wanted = {dep["name"]: dep for dep in config["deps"]}
    direct = direct_entries(manifest)
    if set(direct) != set(wanted):
        problems.append(
            f"direct manifest entries {sorted(direct)} != pinned deps {sorted(wanted)}"
        )
    shas: dict[str, str] = {}
    for name, dep in wanted.items():
        sha = client.tag_sha(dep["repo"], target)
        if sha is None:
            problems.append(f"could not resolve tag SHA for {name} {target}")
            continue
        shas[name] = sha
        entry = direct.get(name)
        if entry is None:
            continue
        if entry.get("inputRev") != target:
            problems.append(f"{name}: inputRev {entry.get('inputRev')!r} != {target!r}")
        if entry.get("rev") != sha:
            problems.append(f"{name}: rev {entry.get('rev')!r} != tag SHA {sha}")
        if base_manifest is not None:
            base_entry = direct_entries(base_manifest).get(name)
            if base_entry is not None:
                diff = sorted(
                    k for k in set(entry) | set(base_entry)
                    if k not in ("rev", "inputRev") and entry.get(k) != base_entry.get(k)
                )
                if diff:
                    problems.append(
                        f"{name}: manifest entry differs from base in {diff} "
                        "(only rev/inputRev may change)"
                    )
        else:
            expected_url = f"https://github.com/{dep['repo']}"
            if entry.get("type") != "git":
                problems.append(f"{name}: type {entry.get('type')!r} != 'git'")
            if entry.get("url", "").rstrip("/").removesuffix(".git") != expected_url:
                problems.append(f"{name}: url {entry.get('url')!r} != {expected_url!r}")
    # Transitive entries must be exactly the union of the deps' manifests.
    # Conflicting records for one package from different upstream manifests
    # fail instead of letting one silently win.
    expected: dict[str, dict] = {}
    for name, dep in wanted.items():
        sha = shas.get(name)
        if not sha:
            continue
        upstream = json.loads(client.contents(dep["repo"], "lake-manifest.json", sha))
        problems.extend(
            check_no_duplicate_packages(upstream, f"{name}@{target} manifest")
        )
        for pkg in upstream.get("packages", []):
            if pkg.get("name") in wanted:
                continue
            canonical = dict(pkg, inherited=True)
            if pkg["name"] in expected and expected[pkg["name"]] != canonical:
                problems.append(
                    f"transitive entry {pkg['name']} conflicts between "
                    f"upstream manifests at {target}"
                )
            expected.setdefault(pkg["name"], canonical)
    actual = {
        pkg["name"]: pkg
        for pkg in manifest.get("packages", [])
        if pkg.get("inherited", False)
    }
    for name in sorted(set(expected) | set(actual)):
        if name not in expected:
            problems.append(f"transitive entry {name} is not in any dep@{target} manifest")
        elif name not in actual:
            problems.append(f"transitive entry {name} from a dep@{target} manifest is missing")
        elif actual[name] != expected[name]:
            diff = sorted(
                k for k in set(actual[name]) | set(expected[name])
                if actual[name].get(k) != expected[name].get(k)
            )
            problems.append(f"transitive entry {name} differs from dep@{target} in {diff}")
    return problems


def run(cmd: list[str], *, cwd: Path | None = None, env: dict | None = None) -> str:
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True)
    if result.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} failed: {result.stderr.strip()}")
    return result.stdout.strip()


def resolve_shas(client: GitHub, config: dict, target: str) -> dict[str, str]:
    shas = {}
    for dep in config["deps"]:
        sha = client.tag_sha(dep["repo"], target)
        if sha is None:
            raise ValueError(f"could not resolve tag SHA for {dep['name']} {target}")
        shas[dep["name"]] = sha
    toolchain_sha = client.tag_sha(config["toolchain_repo"], target)
    if toolchain_sha is None:
        raise ValueError(f"could not resolve tag SHA for Lean {target}")
    return shas


def validate_target(client: GitHub, root: Path, config: dict, target: str,
                    *, allow_rc: bool) -> None:
    if not is_version_tag(target, allow_rc=allow_rc):
        raise ValueError(f"target {target!r} is not a version tag")
    current = current_tag(root, config)
    if version_key(target) <= version_key(current):
        raise ValueError(f"target {target} is not newer than current {current}")
    # Revalidate against the live tags + cache, so a stale or forged job
    # output cannot smuggle a target past the selector into the App-token job.
    selected, _run_id, reason = select_target(
        client, root, config, manual=target, allow_rc=allow_rc
    )
    if selected != target:
        raise ValueError(f"target {target} failed revalidation: {reason}")


def cmd_prepare(args: argparse.Namespace) -> int:
    root = Path.cwd()
    config = load_config(root)
    client = GitHub()
    target = args.target
    try:
        validate_target(client, root, config, target, allow_rc=args.allow_rc)
        base_manifest = load_manifest(root)
        shas = resolve_shas(client, config, target)
        changed = apply_pin_edits(root, config, current_tag(root, config), target, shas)
        print(f"edited: {', '.join(changed)}")
        run(["lake", "update"], cwd=root)
        problems = verify_manifest(client, root, config, target, base_manifest)
    except (ValueError, RuntimeError) as exc:
        print(f"prepare: FAIL - {exc}", file=sys.stderr)
        return 1
    if problems:
        print("prepare: FAIL - manifest verification failed after lake update:")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print(f"prepare: OK - tree prepared for {target} (nothing committed or pushed)")
    return 0


def _git_show(root: Path, rel: str) -> str:
    """Unstripped contents of ``rel`` at HEAD (the trusted base tree)."""
    result = subprocess.run(
        ["git", "show", f"HEAD:{rel}"], cwd=root, text=True,
        capture_output=True, check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"git show HEAD:{rel} failed: {result.stderr.strip()}"
        )
    return result.stdout


def validate_prepared_contents(
    client: GitHub, root: Path, config: dict, target: str, *, allow_rc: bool,
    base_files: dict[str, str] | None = None,
) -> list[str]:
    """Semantic problems in a prepared tree at ``target``, or [].

    Every prepared file is revalidated against the trusted base tree
    (``base_files`` when given, else ``git show HEAD:<path>``) and
    the live tags, using the same checks the guard applies to a PR:
    the manifest (direct + transitive, against the base manifest),
    the lakefile (only pinned revs may differ from base), the
    pin-policy file, the doc replacements, and the migration-ledger
    pins/hashes. A compromised prepare step that rewrites a
    whitelisted file to arbitrary contents fails here, before any
    write credential exists, even though the filenames are unchanged.
    """
    problems: list[str] = []
    if not is_version_tag(target, allow_rc=allow_rc):
        return [f"target {target!r} is not a version tag"]
    try:
        prepared_tag = current_tag(root, config)
    except ValueError as exc:
        return [str(exc)]
    if prepared_tag != target:
        problems.append(
            f"prepared tree is at {prepared_tag} not {target}; "
            "run prepare first on the same checkout"
        )
        return problems
    try:
        shas = resolve_shas(client, config, target)
    except ValueError as exc:
        return problems + [str(exc)]

    def base_text(rel: str) -> str:
        if base_files is not None and rel in base_files:
            return base_files[rel]
        return _git_show(root, rel)

    # Manifest: direct + transitive entries, against the base manifest.
    try:
        base_manifest = json.loads(base_text("lake-manifest.json"))
        problems.extend(
            verify_manifest(client, root, config, target, base_manifest)
        )
    except (ValueError, RuntimeError, json.JSONDecodeError, OSError) as exc:
        problems.append(f"manifest validation failed: {exc}")

    # Lakefile: only the pinned revs may differ from the base file.
    try:
        base_doc = tomllib.loads(base_text("lakefile.toml"))
        prepared_doc = load_lakefile(root)
        if normalized_lakefile(prepared_doc, config, target) != (
            normalized_lakefile(base_doc, config, target)
        ):
            problems.append(
                "lakefile.toml differs from base outside the pinned revs"
            )
    except (ValueError, RuntimeError, OSError) as exc:
        problems.append(f"lakefile validation failed: {exc}")

    # Pin-policy file: exactly the base file with the new tag/SHAs.
    pin_policy = config.get("pin_policy")
    if pin_policy:
        try:
            expected = apply_replacements_to_text(
                base_text(pin_policy["path"]),
                pin_policy["replacements"], target, shas,
            )
            prepared = (root / pin_policy["path"]).read_text(encoding="utf-8")
            if prepared != expected:
                problems.append(
                    f"{pin_policy['path']} does not match the base file "
                    "with the new tag/SHAs applied"
                )
        except (ValueError, RuntimeError, OSError) as exc:
            problems.append(f"pin-policy validation failed: {exc}")

    # Doc replacements: group by path, apply in order to the base text.
    by_path: dict[str, list[dict]] = {}
    for entry in config.get("doc_replacements", []):
        by_path.setdefault(entry["path"], []).append(entry)
    for path, entries in by_path.items():
        try:
            expected = base_text(path)
            for entry in entries:
                expected = apply_replacements_to_text(
                    expected, [entry], target, shas
                )
            prepared = (root / path).read_text(encoding="utf-8")
            if prepared != expected:
                problems.append(
                    f"{path} does not match the base file with the "
                    "new tag applied"
                )
        except (ValueError, RuntimeError, OSError) as exc:
            problems.append(f"doc validation failed for {path}: {exc}")

    # Migration ledgers: pin-consistent with the prepared manifest.
    ledgers = config.get("migration_ledgers") or []
    if ledgers:
        try:
            ledger_rel, checks_rel = _migration_ledger_paths(config)
            prepared_manifest = load_manifest(root)
            prepared_mathlib = next(
                p["rev"] for p in prepared_manifest["packages"]
                if p["name"] == "mathlib"
            )
            prepared_ledger = json.loads(
                (root / ledger_rel).read_text(encoding="utf-8"))
            prepared_checks = json.loads(
                (root / checks_rel).read_text(encoding="utf-8"))
            problems.extend(check_migration_ledger_pins(
                prepared_ledger, prepared_checks,
                mathlib_sha=prepared_mathlib,
                lean_tag=f"leanprover/lean4:{target}",
            ))
        except (ValueError, RuntimeError, OSError, json.JSONDecodeError,
                KeyError, StopIteration) as exc:
            problems.append(f"migration ledgers are inconsistent: {exc}")

    # The target must still exist with a published Mathlib cache.
    mathlib = next(d for d in config["deps"] if d["name"] == "mathlib")
    sha = client.tag_sha(mathlib["repo"], target)
    if sha and client.successful_master_build_run(mathlib["repo"], sha) is None:
        problems.append(f"mathlib {target} has no successful master-push build")
    return problems


def validate_prepared_tree(
    client: GitHub, root: Path, config: dict, target: str, *, allow_rc: bool
) -> str:
    """Validate a prepared tree: it must already be at target, and the
    target must still exist in every repo with a published Mathlib cache.
    Returns the base tag the tree was prepared from (from HEAD)."""
    if not is_version_tag(target, allow_rc=allow_rc):
        raise ValueError(f"target {target!r} is not a version tag")
    if current_tag(root, config) != target:
        raise ValueError(
            f"prepared tree is at {current_tag(root, config)} not {target}; "
            "run prepare first on the same checkout"
        )
    problems = validate_prepared_contents(
        client, root, config, target, allow_rc=allow_rc
    )
    if problems:
        raise ValueError(
            "prepared tree validation failed: " + "; ".join(problems)
        )
    head_toolchain = _git_show(root, "lean-toolchain").strip()
    prefix = "leanprover/lean4:"
    if not head_toolchain.startswith(prefix):
        raise ValueError(f"unexpected HEAD lean-toolchain: {head_toolchain!r}")
    base = head_toolchain[len(prefix):]
    if version_key(target) <= version_key(base):
        raise ValueError(f"target {target} is not newer than base {base}")
    return base


def check_prepare_base() -> None:
    """Fail if HEAD is not the commit `prepare` prepared from.

    The workflow sets PREPARE_BASE_SHA; an empty value means the caller
    did not set it, in which case this check is skipped (the workflow
    is the only supported `finish` caller).
    """
    prepare_base = os.environ.get("PREPARE_BASE_SHA", "")
    if not prepare_base:
        return
    head_sha = run(["git", "rev-parse", "HEAD"])
    if head_sha != prepare_base:
        raise ValueError(
            f"HEAD {head_sha} != prepare base {prepare_base}; refusing to "
            "publish prepared files onto a different tree"
        )


def cmd_finish(args: argparse.Namespace) -> int:
    root = Path.cwd()
    config = load_config(root)
    client = GitHub()
    target = args.target
    try:
        check_prepare_base()
        base_tag = validate_prepared_tree(
            client, root, config, target, allow_rc=args.allow_rc
        )
    except (ValueError, RuntimeError) as exc:
        print(f"finish: FAIL - {exc}", file=sys.stderr)
        return 2
    branch = f"bump-pinned-rc/{target}" if args.allow_rc else f"bump-pinned/{target}"
    # If an open PR already points at this branch, leave it alone: it may
    # hold human repair commits. Only a PR from this repo targeting main
    # counts: a fork can reuse the predictable branch name.
    for pr in client.open_prs():
        if _is_existing_bump_pr(pr, client.repo, branch):
            print(f"open bump PR #{pr['number']} already exists on {branch}; leaving it alone")
            return 0
    bot_name = os.environ.get("BUMP_BOT_NAME") or "bump-pinned-release[bot]"
    bot_email = os.environ.get("BUMP_BOT_NAME_EMAIL") or (
        "bump-pinned-release[bot]@users.noreply.github.com"
    )
    try:
        run(["git", "config", "user.name", bot_name])
        run(["git", "config", "user.email", bot_email])
        changed = prepared_files(config)
        if run(["git", "status", "--porcelain"]):
            run(["git", "add"] + sorted(set(changed)))
            run(["git", "commit", "-m", f"Bump pinned Lean/Mathlib to {target}"])
        else:
            # Re-running finish after a previous run committed (but failed
            # to open the PR): the tree is already committed, do not fail.
            print("working tree already committed; reusing HEAD")
        local_tree = run(["git", "rev-parse", "HEAD^{tree}"])
        remote = run(["git", "ls-remote", "--heads", "origin", branch])
        if remote:
            run(["git", "fetch", "origin", branch])
            remote_tree = run(["git", "rev-parse", "FETCH_HEAD^{tree}"])
            if remote_tree != local_tree:
                print(
                    f"finish: FAIL - remote branch {branch} exists with different "
                    "content and no open PR; human intervention needed (refusing to overwrite)"
                )
                return 1
            print(f"remote branch {branch} already has the prepared tree; creating the missing PR")
        else:
            app_token = os.environ.get("APP_TOKEN")
            if not app_token:
                print("finish: FAIL - APP_TOKEN is not set", file=sys.stderr)
                return 2
            push_url = f"https://x-access-token:{app_token}@github.com/{client.repo}.git"
            run(["git", "push", push_url, f"HEAD:refs/heads/{branch}"])
    except RuntimeError as exc:
        print(f"finish: FAIL - {exc}", file=sys.stderr)
        return 1
    rows = []
    for dep in config["deps"]:
        rows.append(
            f"| {dep['name']} | `{base_tag}` | `{target}` | "
            f"{client.tag_sha(dep['repo'], target)} |"
        )
    body = (
        f"Bump the pinned Lean/Mathlib release from `{base_tag}` to `{target}`.\n\n"
        "| Dependency | From | To | Tag SHA |\n|---|---|---|---|\n"
        + "\n".join(rows)
        + "\n\n"
        + "Opened automatically by the pinned-release bump workflow "
        "(selector: newest final release tag present in every pinned repo; "
        "Mathlib@target has a successful master-push build, so its oleans are published).\n\n"
        "Checklist before merging: CI green; commit source repairs on this branch if CI "
        "fails (the bot never rewrites this branch once it exists); do not delete "
        "`BACKPORTS.md` ledger rows on the strength of the bump alone — each row's "
        "removal condition must be rechecked against the new pin.\n"
    )
    body_file = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "bump-pr-body.md"
    body_file.write_text(body, encoding="utf-8")
    try:
        run([
            "gh", "pr", "create", "--repo", client.repo, "--base", "main",
            "--head", branch, "--title", f"Bump pinned Lean/Mathlib to {target}",
            "--body-file", str(body_file),
        ])
    except RuntimeError as exc:
        print(
            f"finish: FAIL - PR creation failed after the branch was pushed; "
            f"re-running finish will create the missing PR instead of pushing again: {exc}",
            file=sys.stderr,
        )
        return 1
    print(f"opened bump PR on {branch}")
    # Close superseded bot-only bump PRs for older targets, only now that
    # the new PR exists. A PR with human repair commits is never closed here.
    for pr in client.open_prs():
        if not _is_superseded_candidate(pr, client.repo, branch, target):
            continue
        head = (pr.get("head") or {}).get("ref", "")
        commits = client.pr_commits(pr["number"])
        total = pr.get("commits")
        if isinstance(total, int) and total > len(commits):
            print(
                f"leaving {head} (#{pr['number']}) alone: fetched "
                f"{len(commits)} of {total} commits; failing closed"
            )
            continue
        if _pr_is_bot_only(commits, total if isinstance(total, int) else None):
            client.close_pr(
                pr["number"],
                f"Superseded by the bump to {target}: this PR is bot-only, "
                "so it is safe to close. A PR with human repair commits is never closed here.",
            )
            print(f"closed superseded bot-only bump PR #{pr['number']}")
        else:
            print(f"leaving {head} (#{pr['number']}) alone: it has non-bot commits")
    return 0


def cmd_validate_prepared(args: argparse.Namespace) -> int:
    """Revalidate an overlaid prepared tree before any write credential."""
    root = Path.cwd()
    config = load_config(root)
    client = GitHub()
    target = args.target
    try:
        problems = validate_prepared_contents(
            client, root, config, target, allow_rc=args.allow_rc
        )
    except (ValueError, RuntimeError) as exc:
        print(f"validate-prepared: FAIL - {exc}", file=sys.stderr)
        return 2
    if problems:
        print("validate-prepared: FAIL - prepared tree validation failed:")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print(f"validate-prepared: OK - prepared tree for {target} revalidated")
    return 0


def cmd_merge_group_pr(args: argparse.Namespace) -> int:
    """Print the PR number for a merge-group head ref, or fail closed."""
    number = parse_merge_group_head_ref(args.head_ref)
    if number is None:
        print(
            f"merge-group-pr: FAIL - cannot parse PR number from "
            f"{args.head_ref!r}",
            file=sys.stderr,
        )
        return 1
    print(number)
    return 0


def cmd_stage_prepared(args: argparse.Namespace) -> int:
    """Copy the prepared files into an artifact staging directory."""
    root = Path.cwd()
    config = load_config(root)
    dest = Path(args.dest)
    for rel in prepared_files(config):
        src = root / rel
        if not src.is_file():
            print(f"stage-prepared: FAIL - {rel} is missing", file=sys.stderr)
            return 1
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, target)
    print(f"stage-prepared: OK - staged {len(prepared_files(config))} files to {dest}")
    return 0


def cmd_verify_staged(args: argparse.Namespace) -> int:
    """Refuse a staged tree containing anything outside the prepared-file
    whitelist (or missing a whitelisted file)."""
    config = load_config(Path.cwd())
    allowed = set(prepared_files(config))
    staged_dir = Path(args.dir)
    staged = {
        str(p.relative_to(staged_dir))
        for p in staged_dir.rglob("*")
        if p.is_file()
    }
    extra = sorted(staged - allowed)
    missing = sorted(allowed - staged)
    if extra or missing:
        if extra:
            print(f"verify-staged: FAIL - unexpected files: {extra}", file=sys.stderr)
        if missing:
            print(f"verify-staged: FAIL - missing files: {missing}", file=sys.stderr)
        return 1
    print(f"verify-staged: OK - staged tree holds only the {len(allowed)} prepared files")
    return 0


def cmd_select(args: argparse.Namespace) -> int:
    root = Path.cwd()
    config = load_config(root)
    client = GitHub()
    manual = args.target or os.environ.get("INPUT_TARGET", "")
    allow_rc = args.allow_rc or os.environ.get("INPUT_ALLOW_RC") == "true"
    try:
        target, run_id, reason = select_target(
            client, root, config, manual=manual, allow_rc=allow_rc,
        )
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(reason)
    output_file = os.environ.get("GITHUB_OUTPUT")
    if output_file:
        with open(output_file, "a", encoding="utf-8") as f:
            f.write(f"target={target}\n")
            f.write(f"mathlib_run_id={run_id or 0}\n")
    else:
        print(f"target={target}")
        print(f"mathlib_run_id={run_id or 0}")
    return 0


def normalized_lakefile(doc: dict, config: dict, tag: str) -> dict:
    """Deep copy of a lakefile doc with pinned dep revs set to tag."""
    doc = copy.deepcopy(doc)
    requires = doc.get("require", [])
    if not isinstance(requires, list):
        raise ValueError("lakefile.toml [[require]] is not a list")
    names = [entry.get("name") for entry in requires if isinstance(entry, dict)]
    dups = sorted({n for n in names if names.count(n) > 1})
    if dups:
        raise ValueError(f"lakefile.toml has duplicate [[require]] names: {dups}")
    wanted = {dep["name"] for dep in config["deps"]}
    for entry in requires:
        if isinstance(entry, dict) and entry.get("name") in wanted:
            entry["rev"] = tag
    return doc


def cmd_guard(args: argparse.Namespace) -> int:
    base = Path(args.base)
    merge_base = Path(args.merge_base)
    pr = Path(args.pr)
    config = load_config(base)
    client = GitHub()
    changed = {
        line.strip() for line in Path(args.changed_files).read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    if not (changed & set(PIN_FILES)):
        print("guard: PASS - no pin files changed")
        return 0
    if changed & set(GUARD_FILES):
        print("guard: FAIL - a pin-change PR must not touch the guard, its config, or the bump workflow")
        return 1
    problems: list[str] = []
    try:
        base_tag = current_tag(base, config)
        pr_tag = current_tag(pr, config)
    except ValueError as exc:
        print(f"guard: FAIL - {exc}")
        return 1
    if not is_final(pr_tag):
        problems.append(f"PR tag {pr_tag!r} is not a final release tag")
    if version_key(pr_tag) <= version_key(base_tag):
        problems.append(f"PR tag {pr_tag} is not newer than base tag {base_tag}")
    if (pr / "lean-toolchain").read_text(encoding="utf-8").strip() != f"leanprover/lean4:{pr_tag}":
        problems.append("lean-toolchain does not match the PR tag")
    # The complete lakefile, not just [[require]]: normalize only the pinned
    # revs in both documents and compare everything else exactly.
    try:
        base_doc = normalized_lakefile(load_lakefile(base), config, base_tag)
        pr_doc = normalized_lakefile(load_lakefile(pr), config, base_tag)
        if base_doc != pr_doc:
            top_diff = sorted(
                k for k in set(base_doc) | set(pr_doc) if base_doc.get(k) != pr_doc.get(k)
            )
            problems.append(
                f"lakefile.toml differs from base outside the pinned revs: {top_diff}"
            )
    except ValueError as exc:
        problems.append(f"lakefile.toml is malformed: {exc}")
    # Pin-policy constants (atlas check_lake_surface.py) must be exactly the
    # base file with the configured replacements applied for the new tag.
    pin_policy = config.get("pin_policy")
    if pin_policy:
        try:
            shas = resolve_shas(client, config, pr_tag)
            base_text = (base / pin_policy["path"]).read_text(encoding="utf-8")
            pr_text = (pr / pin_policy["path"]).read_text(encoding="utf-8")
            expected = apply_replacements_to_text(
                base_text, pin_policy["replacements"], pr_tag, shas
            )
            if pr_text != expected:
                problems.append(
                    f"{pin_policy['path']} does not match the base file with "
                    "the new tag/SHAs applied (missing update, or an unrelated edit)"
                )
        except (ValueError, OSError) as exc:
            problems.append(f"pin-policy check failed: {exc}")
    # Migration ledgers: if either tree carries them, the PR tree's pair
    # must be consistent with the PR's own manifest/toolchain pins, or
    # the bump PR leaves the migration validator failing on stale pins.
    ledger_rel, checks_rel = _migration_ledger_paths(config)
    if (
        (base / ledger_rel).is_file() or (pr / ledger_rel).is_file()
        or (base / checks_rel).is_file() or (pr / checks_rel).is_file()
    ):
        try:
            pr_manifest = load_manifest(pr)
            pr_mathlib = next(
                p["rev"] for p in pr_manifest["packages"] if p["name"] == "mathlib"
            )
            pr_ledger = json.loads((pr / ledger_rel).read_text(encoding="utf-8"))
            pr_checks = json.loads((pr / checks_rel).read_text(encoding="utf-8"))
            problems.extend(check_migration_ledger_pins(
                pr_ledger, pr_checks,
                mathlib_sha=pr_mathlib, lean_tag=f"leanprover/lean4:{pr_tag}",
            ))
        except (OSError, json.JSONDecodeError, KeyError, StopIteration, ValueError) as exc:
            problems.append(f"migration ledgers are unreadable or inconsistent: {exc}")
    _ = merge_base
    try:
        base_manifest = load_manifest(base)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"guard: FAIL - cannot read base manifest: {exc}")
        return 1
    problems.extend(verify_manifest(client, pr, config, pr_tag, base_manifest))
    if client.tag_sha(config["toolchain_repo"], pr_tag) is None:
        problems.append(
            f"Lean tag {pr_tag} does not exist in {config['toolchain_repo']}"
        )
    mathlib = next(d for d in config["deps"] if d["name"] == "mathlib")
    sha = client.tag_sha(mathlib["repo"], pr_tag)
    if sha and client.successful_master_build_run(mathlib["repo"], sha) is None:
        problems.append(f"mathlib {pr_tag} has no successful master-push build (cache unpublished)")
    if problems:
        print("guard: FAIL")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print(f"guard: PASS - pinned bump {base_tag} -> {pr_tag} validated")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p_select = sub.add_parser("select", help="select the next pinned release target")
    p_select.add_argument("--target", default="")
    p_select.add_argument("--allow-rc", action="store_true")
    p_select.set_defaults(func=cmd_select)
    p_prepare = sub.add_parser(
        "prepare", help="apply the bump to the working tree and verify it (no commit/push)")
    p_prepare.add_argument("target")
    p_prepare.add_argument("--allow-rc", action="store_true")
    p_prepare.set_defaults(func=cmd_prepare)
    p_stage = sub.add_parser(
        "stage-prepared",
        help="stage the prepared files into a directory for transfer to the publish job")
    p_stage.add_argument("--dest", required=True)
    p_stage.set_defaults(func=cmd_stage_prepared)
    p_verify = sub.add_parser(
        "verify-staged",
        help="verify a staged tree holds only the prepared files")
    p_verify.add_argument("--dir", required=True)
    p_verify.set_defaults(func=cmd_verify_staged)
    p_finish = sub.add_parser(
        "finish", help="commit, push, and open the PR for a prepared tree (App token)")
    p_finish.add_argument("target")
    p_finish.add_argument("--allow-rc", action="store_true")
    p_finish.set_defaults(func=cmd_finish)
    p_validate = sub.add_parser(
        "validate-prepared",
        help="semantically revalidate an overlaid prepared tree (before minting any write credential)")
    p_validate.add_argument("target")
    p_validate.add_argument("--allow-rc", action="store_true")
    p_validate.set_defaults(func=cmd_validate_prepared)
    p_mg = sub.add_parser(
        "merge-group-pr",
        help="print the PR number for a merge-group head ref")
    p_mg.add_argument("head_ref")
    p_mg.set_defaults(func=cmd_merge_group_pr)
    p_guard = sub.add_parser("guard", help="validate a pin-change PR")
    p_guard.add_argument("--base", required=True)
    p_guard.add_argument("--merge-base", required=True)
    p_guard.add_argument("--pr", required=True)
    p_guard.add_argument("--changed-files", required=True)
    p_guard.set_defaults(func=cmd_guard)
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
