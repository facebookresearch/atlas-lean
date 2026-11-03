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
           prepared tree, push it via a credential helper that reads the
           token from $APP_TOKEN (the token never appears in argv, in the
           push URL, or in command errors; the checkout never persists
           the App token), and open the bump PR. Reconciles an existing branch: an open PR
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
           pr-<number>-...) to its PR number. Legacy helper retained for
           compatibility; the guard's merge_group run no longer uses it --
           it derives the changed-file list from the complete base-to-group
           compare diff instead (see bump-guard.yml), so a merge group
           holding several PRs cannot hide a pin/guard change from a PR
           other than the first one parsed from the head ref.
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
           tag/SHAs; configured doc files match the base file with the
           new tag applied (a pin-change PR cannot omit, revert, or
           arbitrarily edit them); Mathlib@tag has a successful
           master-push build (so its oleans are published to the cache).

Nothing here tracks nightly, master, last-known-good, or first-known-bad
commits. A `-rc` tag is accepted only via an explicit manual dispatch with
--allow-rc, and then only onto a bump-pinned-rc/ branch.
"""

from __future__ import annotations

import argparse
import base64
import copy
import difflib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path, PurePosixPath

FINAL_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)$")
RC_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)-rc(\d+)$")
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
PIN_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
# Guard code: a pin-change PR must never touch these. pinned_deps.json
# is deliberately NOT in this list: it is data, and a same-pin PR may
# extend it monotonically (add a dependency at the current pin) so the
# config stays in sync with the lakefile. Monotonic extension is checked
# separately by check_config_extension: dependencies may only be added,
# never removed or repointed.
# The test module is deliberately NOT in this list either: adding a
# dependency requires updating its hardcoded fixtures in the same PR.
# Tests are not enforcement: the guard run executes base code, and a PR
# that weakens its own tests still faces the guard's independent pin
# validation plus normal review.
GUARD_FILES = (
    ".github/workflows/bump-guard.yml",
    ".github/workflows/bump-pinned-release.yml",
    "scripts/bump/pinned_bump.py",
)
CONFIG_FILE = "scripts/bump/pinned_deps.json"


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


def bump_branch(target: str) -> str:
    """Branch for a bump PR, chosen from the target's syntax, never from
    the --allow-rc flag: an -rc target goes on bump-pinned-rc/, every
    other version tag on bump-pinned/. Deriving the branch from the flag
    published a final release onto an -rc branch whenever --allow-rc
    was set with an empty (auto-selected, final) target."""
    if RC_RE.fullmatch(target):
        return f"bump-pinned-rc/{target}"
    return f"bump-pinned/{target}"


def _require_explicit_rc_target(target: str, *, allow_rc: bool) -> None:
    """Fail when --allow-rc is set without an explicit -rc target.

    --allow-rc is permission to accept one explicitly named -rc target,
    not a mode: with an empty target the selector would otherwise pick
    the newest final release, and with a final target the run would
    publish a final release as if it were a preview."""
    if allow_rc and RC_RE.fullmatch(target) is None:
        raise ValueError(
            "--allow-rc requires an explicit -rc target "
            f"(got {target!r}); auto-selection and final targets do not "
            "go on an -rc branch"
        )


_CONFIG_KEYS = {"toolchain_repo", "deps", "doc_replacements", "pin_policy", "migration_ledgers"}
_DEP_KEYS = {"name", "repo"}
_DOC_REPLACEMENT_KEYS = {"path", "pattern", "replacement"}
_PIN_POLICY_KEYS = {"path", "replacements"}
_PIN_REPLACEMENT_KEYS = {"pattern", "replacement"}


def _is_safe_relative_path(value: object) -> bool:
    """A config path must stay inside the repo and be safely downloadable.

    Relative, no .., non-empty, and none of ? # & \\ % or control
    characters: those would let a PR-controlled path alter the download
    URL's query string (selecting a different file) or smuggle encoded
    delimiters past the destination check. A path failing this can never
    be downloaded by the guard workflow, so the schema rejects it rather
    than letting it merge into an entry the monotonic policy then
    blocks removing (a permanent brick).
    """
    if not isinstance(value, str) or not value:
        return False
    if any(ord(c) < 32 or ord(c) == 127 for c in value):
        return False
    if any(c in value for c in "?#&\\%"):
        return False
    parts = PurePosixPath(value).parts
    return not value.startswith("/") and ".." not in parts


def validate_config_schema(config: dict, path: Path) -> None:
    """Validate the complete pinned_deps.json schema.

    Partial validation here bricked the workflow: a malformed
    doc_replacements entry merged into the base config made the guard
    workflow's own `e["path"]` read raise before the guard ran, blocking
    every subsequent PR including a repair PR. Every field the guard,
    the bot, or the workflow reads is validated, unknown keys are
    rejected (config is bot-executed; every key must mean something
    the code understands), and paths must be repo-relative.
    """
    if not isinstance(config, dict):
        raise ValueError(f"bad config in {path}: expected an object")
    unknown = sorted(set(config) - _CONFIG_KEYS)
    if unknown:
        raise ValueError(f"bad config in {path}: unknown top-level keys {unknown}")
    toolchain_repo = config.get("toolchain_repo")
    if not isinstance(toolchain_repo, str) or not toolchain_repo:
        raise ValueError(f"bad config in {path}: toolchain_repo must be a non-empty string")
    if not isinstance(config.get("deps"), list):
        raise ValueError(f"bad config in {path}: deps must be a list")
    for dep in config["deps"]:
        if not isinstance(dep, dict) or sorted(set(dep) - _DEP_KEYS):
            raise ValueError(f"bad dep entry in {path}: {dep!r}")
        if not isinstance(dep.get("name"), str) or not dep.get("name"):
            raise ValueError(f"bad dep entry in {path}: {dep!r}")
        if not isinstance(dep.get("repo"), str) or not dep.get("repo"):
            raise ValueError(f"bad dep entry in {path}: {dep!r}")
    for entry in config.get("doc_replacements", []):
        if not isinstance(entry, dict) or sorted(set(entry) - _DOC_REPLACEMENT_KEYS):
            raise ValueError(f"bad doc_replacements entry in {path}: {entry!r}")
        for key in ("path", "pattern", "replacement"):
            if not isinstance(entry.get(key), str):
                raise ValueError(
                    f"bad doc_replacements entry in {path}: {key} must be a string: {entry!r}"
                )
        if not entry["pattern"]:
            raise ValueError(f"bad doc_replacements entry in {path}: empty pattern: {entry!r}")
        if not _is_safe_relative_path(entry["path"]):
            raise ValueError(
                f"bad doc_replacements entry in {path}: unsafe path {entry['path']!r}"
            )
    pin_policy = config.get("pin_policy")
    if pin_policy is not None:
        if not isinstance(pin_policy, dict) or sorted(set(pin_policy) - _PIN_POLICY_KEYS):
            raise ValueError(f"bad pin_policy in {path}: {pin_policy!r}")
        if not _is_safe_relative_path(pin_policy.get("path")):
            raise ValueError(f"bad pin_policy in {path}: unsafe path {pin_policy.get('path')!r}")
        if not isinstance(pin_policy.get("replacements"), list):
            raise ValueError(f"bad pin_policy in {path}: replacements must be a list")
        for replacement in pin_policy["replacements"]:
            if not isinstance(replacement, dict) or sorted(
                set(replacement) - _PIN_REPLACEMENT_KEYS
            ):
                raise ValueError(f"bad pin_policy replacement in {path}: {replacement!r}")
            for key in ("pattern", "replacement"):
                if not isinstance(replacement.get(key), str):
                    raise ValueError(
                        f"bad pin_policy replacement in {path}: {key} must be a string: "
                        f"{replacement!r}"
                    )
            if not replacement["pattern"]:
                raise ValueError(
                    f"bad pin_policy replacement in {path}: empty pattern: {replacement!r}"
                )
    for ledger in config.get("migration_ledgers", []):
        if not _is_safe_relative_path(ledger):
            raise ValueError(
                f"bad migration ledger in {path}: unsafe path {ledger!r}"
            )


def load_config(root: Path) -> dict:
    path = Path(__file__).resolve().parent / "pinned_deps.json"
    with open(path, encoding="utf-8") as f:
        config = json.load(f)
    validate_config_schema(config, path)
    return config


def load_config_file(path: Path) -> dict:
    """Parse a pinned_deps.json at an explicit path (PR data, not code).

    Used by the guard to read the PR tree's config: the PR may extend it,
    so the base code's config alone cannot describe the PR tree.
    """
    with open(path, encoding="utf-8") as f:
        config = json.load(f)
    validate_config_schema(config, path)
    return config


def _mentions_dep(entry: dict, dep_name: str) -> bool:
    text = json.dumps(entry, sort_keys=True)
    return dep_name in text


def check_config_extension(
    base_config: dict, pr_config: dict,
    allow_removed_patterns: frozenset[str] | None = None,
) -> list[str]:
    """Validate that a PR's config only extends the base config.

    Allowed: adding a dependency at the current pin (name + repo), adding
    doc/pin-policy replacements, adding migration ledgers, and removing a
    replacement rule whose pattern is in allow_removed_patterns (a rule
    the forward simulation shows cannot apply at the next bump: keeping
    it bricks the bump, so removing it is a repair, not a weakening).
    Never allowed: changing the toolchain repo, repointing an existing
    dependency at another repo, removing a dependency, or removing/
    changing any other entry (that could silently weaken future bump
    validation). Dependency removal has no guarded path here: it needs
    a guard-code change with its own review first, so a same-pin PR can
    never silently drop a pinned dependency. The removed-dep carve-outs
    below only keep the failure message focused on the removal itself.
    A config change in a bump PR is rejected separately by cmd_guard:
    extension must land in a same-pin PR first.
    """
    problems: list[str] = []
    if pr_config.get("toolchain_repo") != base_config.get("toolchain_repo"):
        problems.append(
            "pinned_deps.json: toolchain_repo changed; the config may only gain entries"
        )
    base_deps = {d["name"]: d for d in base_config.get("deps", [])}
    pr_deps = {d["name"]: d for d in pr_config.get("deps", [])}
    if len(pr_deps) != len(pr_config.get("deps", [])):
        problems.append("pinned_deps.json: duplicate dependency names")
    removed_deps = set(base_deps) - set(pr_deps)
    if removed_deps:
        problems.append(
            "pinned_deps.json: dependencies removed "
            f"({sorted(removed_deps)}); the config may only gain deps, never drop one"
        )
    for name, dep in base_deps.items():
        if name in pr_deps and pr_deps[name] != dep:
            problems.append(
                f"pinned_deps.json: pinned dep {name} changed repo; "
                "the config may only gain new deps, never repoint one"
            )
    for entry in base_config.get("doc_replacements", []):
        if entry not in pr_config.get("doc_replacements", []):
            if allow_removed_patterns and entry.get("pattern") in allow_removed_patterns:
                continue  # repair: the rule cannot apply at the next bump
            if not any(_mentions_dep(entry, d) for d in removed_deps):
                problems.append(
                    "pinned_deps.json: doc_replacements entry removed or changed; "
                    "only additions (or entries mentioning a removed dep) are allowed"
                )
    base_pp = base_config.get("pin_policy")
    pr_pp = pr_config.get("pin_policy")
    if base_pp is not None:
        if pr_pp is None or pr_pp.get("path") != base_pp.get("path"):
            problems.append(
                "pinned_deps.json: pin_policy removed or repointed; only additions allowed"
            )
        else:
            for replacement in base_pp.get("replacements", []):
                if replacement not in pr_pp.get("replacements", []):
                    if allow_removed_patterns and replacement.get("pattern") in allow_removed_patterns:
                        continue  # repair: the rule cannot apply at the next bump
                    if not any(_mentions_dep(replacement, d) for d in removed_deps):
                        problems.append(
                            "pinned_deps.json: pin_policy replacement removed or changed; "
                            "only additions (or entries mentioning a removed dep) are allowed"
                        )
    # migration_ledgers must be unchanged, not merely append-only:
    # apply_pin_edits requires exactly two entries, so a third ledger
    # passing the guard would disable all subsequent automated bumps.
    # Adding a ledger needs the ledger consumers generalized first.
    if pr_config.get("migration_ledgers", []) != base_config.get("migration_ledgers", []):
        problems.append(
            "pinned_deps.json: migration_ledgers changed; the field must stay "
            "unchanged (apply_pin_edits supports exactly two entries)"
        )
    return problems


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
    consistent. This checks pins and content hashes only, not whether the
    named Mathlib APIs still exist at the new pin; that is checked
    separately by verify_apis_exist_at_pin (a pin pointer is not audit
    evidence that the API still exists, and the repo's Lean build does
    not reference these JSON pointers at all)."""
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


def expected_repinned_ledgers(
    ledger: dict, checks: dict, *, old_mathlib: str, old_lean: str,
    new_mathlib: str, new_lean: str,
) -> tuple[dict, dict]:
    """The intended (ledger, checks) pair after re-pinning a base pair.

    Only the pins, the Mathlib.* API revisions, and the hashes that bind
    those fields move; every other field (records, migration status,
    gates, legacy declarations, ...) is copied verbatim from the base
    pair. The result is the exact expected content for a re-pinned pair,
    so validating a prepared/guarded pair means comparing it to this
    derivation, not just re-checking pins/hashes (which would accept a
    pair with replaced records or a changed migration status as long as
    the pin fields were kept). Raises ValueError when the base pair is
    inconsistent at the old pins or the derived pair is inconsistent at
    the new pins.
    """
    pre = check_migration_ledger_pins(
        ledger, checks, mathlib_sha=old_mathlib, lean_tag=old_lean
    )
    if pre:
        raise ValueError(
            "cannot re-pin migration ledgers: base pair is inconsistent: "
            + "; ".join(pre)
        )
    if old_mathlib == new_mathlib and old_lean == new_lean:
        return copy.deepcopy(ledger), copy.deepcopy(checks)
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
    post = check_migration_ledger_pins(
        new_ledger, new_checks, mathlib_sha=new_mathlib, lean_tag=new_lean
    )
    if post:
        raise ValueError(
            "cannot re-pin migration ledgers: derived pair is inconsistent: "
            + "; ".join(post)
        )
    return new_ledger, new_checks


def check_ledgers_match_expected(
    prepared_ledger: dict, prepared_checks: dict, *, base_ledger: dict,
    base_checks: dict, old_mathlib: str, old_lean: str, new_mathlib: str,
    new_lean: str,
) -> list[str]:
    """Problems when a candidate (ledger, checks) pair is not exactly the
    re-pinned derivation of the base pair. Parsed-JSON (structural)
    equality: formatting may differ, content may not. Any change outside
    the pin/API-revision/hash updates -- replaced records, a changed
    migration status, edited gates, ... -- is a problem, even when the
    pin fields and hashes are self-consistent."""
    try:
        expected_ledger, expected_checks = expected_repinned_ledgers(
            base_ledger, base_checks, old_mathlib=old_mathlib,
            old_lean=old_lean, new_mathlib=new_mathlib, new_lean=new_lean,
        )
    except ValueError as exc:
        return [f"cannot derive expected migration ledgers from base: {exc}"]
    problems: list[str] = []
    if prepared_ledger != expected_ledger:
        problems.append(
            "migration ledger differs from the base ledger with only the "
            "pin/API-revision/hash updates applied (a non-pin field changed)"
        )
    if prepared_checks != expected_checks:
        problems.append(
            "migration checks differ from the base checks with only the "
            "pin/API-revision/hash updates applied (a non-pin field changed)"
        )
    return problems


def _strip_lean_comments_and_strings(source: str) -> str:
    """Source with comments and string/char literals blanked (newlines kept).

    A `-- theorem N1` line, a `/- theorem N1 -/` block, or a string
    containing that text is not a declaration. Block comments nest in
    Lean. A `'` is a char literal only when it matches `'x'` / `'\\n'`
    etc.; a trailing prime in `smul_tmul'` is part of the identifier
    and is left alone."""
    out: list[str] = []
    i, n = 0, len(source)
    while i < n:
        ch, nxt = source[i], source[i + 1] if i + 1 < n else ""
        if ch == '"':
            out.append(" ")
            i += 1
            while i < n and source[i] != '"':
                if source[i] == "\\" and i + 1 < n:
                    out.append("\n" if source[i] == "\n" else " ")
                    i += 1
                    out.append("\n" if source[i] == "\n" else " ")
                    i += 1
                    continue
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
            if i < n:
                out.append(" ")
                i += 1
            continue
        if ch == "'" and re.match(r"'(?:\\.|[^'\\])'", source[i:]):
            out.append("   " if source[i + 1] != "\\" else "    ")
            i += 3 if source[i + 1] != "\\" else 4
            continue
        if ch == "-" and nxt == "-":
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            while i < n and depth > 0:
                if source[i] == "/" and i + 1 < n and source[i + 1] == "-":
                    depth += 1
                    out.append("  ")
                    i += 2
                elif source[i] == "-" and i + 1 < n and source[i + 1] == "/":
                    depth -= 1
                    out.append("  ")
                    i += 2
                else:
                    out.append("\n" if source[i] == "\n" else " ")
                    i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


# One token scanner, in source order, so `namespace` / `end` / `section`
# / `mutual` blocks nest correctly around the declarations inside them.
_TOKEN_RE = re.compile(
    # namespace / end arguments stay on the same line: `\s+` would let a
    # bare `end` at end-of-line swallow the next line's `end` as its
    # argument (`end\nend Wanted` -> endname "end").
    r"\bnamespace[ \t]+(?P<ns>[A-Za-z_][\w\'.]*)"
    r"|\bsection\b"
    r"|\bmutual\b"
    r"|\bend(?:[ \t]+(?P<endname>[A-Za-z_][\w\'.]*))?"
    r"|\b(?:theorem|lemma|def|abbrev|irreducible_def|structure|class|inductive|axiom|constant|opaque"
    # Instances may carry a parenthesized priority before the name:
    # `instance (priority := 100) uniqueFactorizationMonoid : ...`.
    r"|instance(?:\s*\([^)]*\))*)"
    r"\s+(?P<decl>[A-Za-z_][\w\'.]*)"
)


def _declared_qualified_names(source: str) -> set[str]:
    """Fully qualified names declared in Lean source text.

    `theorem N1` inside `namespace Wanted` declares `Wanted.N1`, not
    `N1`; `theorem Other.N1` at top level declares `Other.N1`, not
    `Wanted.N1`. Matching on short names let either pass for a ledger
    pointer to `Wanted.N1`. A `_root_.`-prefixed name is absolute and
    ignores the enclosing namespace; other names are prefixed with the
    enclosing namespace path, as Lean resolves them."""
    cleaned = _strip_lean_comments_and_strings(source)
    # Each block is ("namespace", components) or ("section", []).
    blocks: list[tuple[str, list[str]]] = []
    declared: set[str] = set()
    for match in _TOKEN_RE.finditer(cleaned):
        if match.group("ns") is not None:
            blocks.append(("namespace", match.group("ns").split(".")))
        elif match.group("endname") is not None:
            endname = match.group("endname")
            for idx in range(len(blocks) - 1, -1, -1):
                if blocks[idx][0] == "namespace" and ".".join(blocks[idx][1]) == endname:
                    del blocks[idx:]
                    break
            else:
                if blocks and blocks[-1][0] == "section":
                    blocks.pop()
        elif match.group(0) in ("section", "mutual"):
            blocks.append(("section", []))
        elif match.group(0).strip() == "end" or match.group(0) == "end":
            if blocks:
                blocks.pop()
        elif match.group("decl") is not None:
            name = match.group("decl")
            if name.startswith("_root_."):
                declared.add(name[len("_root_."):])
            else:
                prefix = [c for _, comps in blocks for c in comps]
                declared.add(".".join(prefix + [name]) if prefix else name)
        # Bare `end` is matched by the `end` alternative above with no
        # endname; it falls into the `match.group(0) == "end"` branch.
    return declared


def _declared_short_names(source: str) -> set[str]:
    """Short (last-component) names declared in Lean source text."""
    return {name.split(".")[-1] for name in _declared_qualified_names(source)}


def verify_apis_exist_at_pin(
    client, ledger: dict, checks: dict, *, mathlib_sha: str,
    mathlib_repo: str,
) -> list[str]:
    """Problems for Mathlib.* destination/triage APIs that no longer name
    a declaration in their listed module file at ``mathlib_sha``.

    The ledger's ``revision`` fields are pin pointers for unverified
    candidates (scope ``unverified``, per the ledger README), not audit
    evidence: advancing them to a new SHA must not record a candidate
    whose API was removed or renamed at that SHA. Each listed module
    file is fetched at the exact SHA and the API's fully qualified name
    must be declared in it, with comments/strings stripped and the
    enclosing `namespace` blocks tracked: `Wanted.N1` passes on
    `namespace Wanted` + `theorem N1`, but not on `Other.N1`, on
    `namespace Other` + `theorem N1`, or on a comment mentioning it.
    This is source-declaration evidence at the pinned SHA, not a
    compiler proof (a same-named declaration still passes); it fails
    closed on any fetch error. MathlibExt.* APIs are not advanced by a
    bump -- they stay at the frozen base -- so they are not checked
    here. Unnamed instances (``name`` is null) are checked only for
    module-file existence.
    """
    wanted: dict[str, list[str | None]] = {}
    for api in ledger.get("destination_apis", []):
        module = api.get("module", "")
        if module.startswith("Mathlib."):
            wanted.setdefault(module, []).append(api.get("name"))
    for api in checks.get("triage_apis", []):
        module = api.get("module", "")
        if module.startswith("Mathlib."):
            wanted.setdefault(module, []).append(api.get("name"))
    problems: list[str] = []
    for module in sorted(wanted):
        path = module.replace(".", "/") + ".lean"
        try:
            source = client.contents(mathlib_repo, path, mathlib_sha).decode(
                "utf-8", errors="replace"
            )
        except Exception as exc:  # noqa: BLE001 - fail closed on any fetch error
            problems.append(
                f"cannot fetch {module} at {mathlib_sha}: {exc}"
            )
            continue
        declared = _declared_qualified_names(source)
        for name in wanted[module]:
            if name is None:
                continue
            if name not in declared:
                problems.append(
                    f"Mathlib API {name} is not declared in {module} at "
                    f"{mathlib_sha} (removed or renamed upstream)"
                )
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

    Advancing the revisions is a pin-pointer update only: whether the
    APIs still exist at the new SHA is verified separately by
    verify_apis_exist_at_pin in prepare / validate / guard, never by
    this rewrite.
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
    new_ledger, new_checks = expected_repinned_ledgers(
        ledger, checks, old_mathlib=old_mathlib, old_lean=old_lean,
        new_mathlib=new_mathlib, new_lean=new_lean,
    )
    if old_mathlib == new_mathlib and old_lean == new_lean:
        return []
    mathlib_apis = [
        api for api in new_ledger.get("destination_apis", [])
        if api.get("module", "").startswith("Mathlib.")
    ]
    mathlib_triage = [
        api for api in new_checks.get("triage_apis", [])
        if api.get("module", "").startswith("Mathlib.")
    ]
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
    # Duplicate names must fail here, not in one caller: current_tag
    # stores revs in a dict where the last duplicate wins, and the
    # same-pin/config-only paths never call normalized_lakefile (the
    # only other duplicate check). A shadowed entry (e.g. mathlib at
    # v9.99.99 before the real v4.35.0 entry) otherwise passes the guard.
    # Malformed entries must fail cleanly (ValueError, caught by the
    # guard) rather than crashing later on .get (AttributeError):
    # every [[require]] is a table with a string name.
    for entry in requires:
        if not isinstance(entry, dict) or not isinstance(entry.get("name"), str):
            raise ValueError(
                "lakefile.toml [[require]] entries must be tables with a string name"
            )
    names = [entry.get("name") for entry in requires if isinstance(entry, dict)]
    dups = sorted({n for n in names if names.count(n) > 1})
    if dups:
        raise ValueError(f"lakefile.toml has duplicate [[require]] names: {dups}")
    return requires


def check_lakefile_sources(
    base: Path, pr: Path, base_config: dict, pr_config: dict, tag: str,
) -> list[str]:
    """Same-pin lakefile check: names and revs are not enough.

    Existing requires must be unchanged except rev: scope/git/path (or
    any other field) repointing would fetch different code on the next
    `lake update` while names and revs still match. New requires must
    use an explicit `git` URL equal to the configured repo. A `scope`
    is NOT accepted for a new dependency: scope alone proves only the
    organization, not the exact repository -- a scoped Physlib with
    scope leanprover-community could resolve (via the package registry)
    to a different repo than the configured one, while the
    author-controlled manifest is made consistent with the configured
    repo. The guard cannot resolve scoped packages exactly, so new
    dependencies must state their repository explicitly; existing
    scoped requires are grandfathered by the unchanged-entry check.
    `path` (local, unpinned) or a sourceless require is rejected. The
    bump path does not need this: normalized_lakefile compares the
    whole document there.
    """
    problems: list[str] = []
    try:
        base_reqs = {e["name"]: e for e in lakefile_requires(base)}
        pr_reqs = {e["name"]: e for e in lakefile_requires(pr)}
    except ValueError as exc:
        return [str(exc)]
    pr_deps = {d["name"]: d for d in pr_config["deps"]}
    for name, entry in base_reqs.items():
        pr_entry = pr_reqs.get(name)
        if pr_entry is None:
            continue  # removal is caught by the require-names check
        if dict(entry, rev=tag) != dict(pr_entry, rev=tag):
            problems.append(
                f"lakefile.toml require {name} changed fields other than rev "
                f"(base {dict(entry, rev=tag)} vs PR {dict(pr_entry, rev=tag)}); "
                "a source change needs a guard-code change with its own review"
            )
    for name, entry in pr_reqs.items():
        if name in base_reqs:
            continue
        dep = pr_deps.get(name)
        if dep is None:
            continue  # caught by the require-names check
        if "path" in entry:
            problems.append(
                f"lakefile.toml require {name} uses a local path; "
                "path dependencies are unpinned and not allowed"
            )
        elif "scope" in entry:
            problems.append(
                f"lakefile.toml require {name} uses scope {entry['scope']!r}; "
                "new dependencies must use an explicit git URL matching the "
                f"configured repo {dep['repo']!r} (scope proves only the org, "
                "not the exact repository)"
            )
        elif "git" in entry:
            url = str(entry["git"]).rstrip("/").removesuffix(".git")
            if url != f"https://github.com/{dep['repo']}":
                problems.append(
                    f"lakefile.toml require {name} git {entry['git']!r} != "
                    f"configured repo {dep['repo']!r}"
                )
        else:
            problems.append(
                f"lakefile.toml require {name} has no git source; "
                "its origin cannot be verified against the configured repo"
            )
    return problems


_PLACEHOLDER_RE = re.compile(r"\{([^{}]*)\}")


def _validate_replacement_placeholders(entry: dict, dep_names: set[str], groups: int) -> list[str]:
    """Every {…} in a replacement must resolve at bump time.

    {target} and {sha:NAME} (NAME a configured dep) are resolved by
    apply_replacements_to_text; {gN} is resolved only for N up to the
    pattern's group count (a larger N stays literal in the output, a
    silent misfire). Anything else passes through literally, so it is
    rejected: a replacement rule must mean exactly what it says.
    """
    problems: list[str] = []
    for placeholder in _PLACEHOLDER_RE.findall(entry["replacement"]):
        if placeholder == "target":
            continue
        if placeholder.startswith("sha:"):
            if placeholder[4:] not in dep_names:
                problems.append(
                    f"replacement {entry['replacement']!r} references unknown dep "
                    f"{placeholder[4:]!r} in {{sha:…}}"
                )
            continue
        if placeholder.startswith("g") and placeholder[1:].isdigit():
            # Canonical form only: {g01} passes the numeric check but
            # apply_replacements_to_text substitutes exactly {g1}, so
            # {g01} would stay literal in the output.
            if placeholder[1:] != str(int(placeholder[1:])) or int(placeholder[1:]) > groups:
                problems.append(
                    f"replacement {entry['replacement']!r} references {{{placeholder}}}; "
                    "group placeholders must be canonical ({g1}, not {g01}) "
                    f"and within the pattern's {groups} groups"
                )
            continue
        problems.append(
            f"replacement {entry['replacement']!r} has unknown placeholder "
            f"{{{placeholder}}}"
        )
    return problems


def _forward_tag(tag: str) -> str | None:
    """A synthetic next-tag for forward validation: every component bumped.

    Current-tag simulation passes over-specific rules: with target == the
    current tag, the generic rules are identity transforms, so a literal
    `v4\\.35\\.0` rule still matches. At the real next bump the generic
    rules rewrite the text first and the literal rule finds nothing.
    Simulating with every component bumped (v4.35.0 -> v5.36.1) catches
    any rule that hardcodes a current-tag component, while tag-agnostic
    rules (version/SHA classes) still match.
    """
    m = FINAL_RE.match(tag)
    if not m:
        return None
    return f"v{int(m.group(1)) + 1}.{int(m.group(2)) + 1}.{int(m.group(3)) + 1}"


_LITERAL_VERSION_RE = re.compile(r"v\d+\.\d+(?:\.\d+)?")
_LITERAL_SHA_RE = re.compile(r"[0-9a-f]{40}")


def _validate_replacement_literals(entry: dict) -> list[str]:
    """A replacement must not hardcode a version or SHA as literal text.

    {target} / {sha:NAME} / {gN} placeholders are the only way to emit
    versions and SHAs. A literal v4.35.0 or 40-hex SHA in a replacement
    goes stale at the next bump (and, listed after the generic rules,
    actively reverts their output to the old tag).
    """
    stripped = _PLACEHOLDER_RE.sub("", entry["replacement"])
    problems: list[str] = []
    m = _LITERAL_VERSION_RE.search(stripped)
    if m:
        problems.append(
            f"replacement {entry['replacement']!r} hardcodes version {m.group(0)!r}; "
            "use {target} instead"
        )
    m = _LITERAL_SHA_RE.search(stripped)
    if m:
        problems.append(
            f"replacement {entry['replacement']!r} hardcodes SHA {m.group(0)!r}; "
            "use {sha:NAME} instead"
        )
    return problems


def _written_regions(original: str, current: str) -> list[tuple[int, int]]:
    """(start, end) spans of `current` that differ from `original`."""
    matcher = difflib.SequenceMatcher(a=original, b=current, autojunk=False)
    return [
        (b_start, b_end)
        for tag, _, _, b_start, b_end in matcher.get_opcodes()
        if tag != "equal"
    ]


def _rule_interferes(pattern: str, text: str, written: list[tuple[int, int]]) -> bool:
    """True if the pattern matches text an earlier rule already wrote.

    An added rule operating on an earlier rule's output can undo it
    while every regex still matches (e.g. rewriting the generic rule's
    forward tag back to the old tag, or scrambling version components).
    Added rules must match original text, not earlier rules' outputs.
    """
    try:
        rx = re.compile(pattern)
    except re.error:
        return False  # compile errors are reported elsewhere
    return any(
        m.start() < end and start < m.end()
        for m in rx.finditer(text)
        for (start, end) in written
    )


def _failing_rule_patterns(
    entries: list[dict], text: str, target: str, shas: dict[str, str],
    dep_names: set[str],
) -> set[str]:
    """Patterns of entries that cannot apply, in list order.

    Covers per-entry failures (invalid regex, bad placeholders) plus the
    first sequential-simulation failure, attributed to its entry via
    the error message (which names the failing pattern / replacement).
    Later entries are untested after a failure: a repair PR removes one
    broken rule at a time, and sequential repairs converge.
    """
    failed: set[str] = set()
    for entry in entries:
        if _static_rule_problems(entry, dep_names):
            failed.add(entry["pattern"])
    try:
        apply_replacements_to_text(text, entries, target, shas)
    except ValueError as exc:
        msg = str(exc)
        for entry in entries:
            if repr(entry["pattern"]) in msg or repr(entry["replacement"]) in msg:
                failed.add(entry["pattern"])
    except re.error:
        pass  # attributed via the per-entry compile above
    return failed


def _resolve_shas(client: GitHub, deps: list[dict], tag: str) -> tuple[dict[str, str], list[str]]:
    shas: dict[str, str] = {}
    problems: list[str] = []
    for dep in deps:
        sha = client.tag_sha(dep["repo"], tag)
        if sha is None:
            problems.append(f"could not resolve tag SHA for {dep['name']} {tag}")
        else:
            shas[dep["name"]] = sha
    return shas, problems


def _static_rule_problems(entry: dict, dep_names: set[str]) -> list[str]:
    """Per-entry static checks: compiles, placeholders, no hardcoded literals."""
    problems: list[str] = []
    problems.extend(_validate_replacement_literals(entry))
    try:
        groups = re.compile(entry["pattern"]).groups
    except re.error as exc:
        problems.append(f"replacement pattern {entry['pattern']!r} is not a valid regex: {exc}")
        return problems
    problems.extend(_validate_replacement_placeholders(entry, dep_names, groups))
    return problems


def _simulate_file_rules(
    entries: list[dict], base_entries: list[dict], original: str,
    targets: list[str], shas: dict[str, str], dep_names: set[str],
    label: str,
) -> list[str]:
    """Validate one file's rule list at every target tag.

    Static checks run for every entry. Rules then apply one at a time,
    in order (exactly apply_replacements_to_text's semantics): before
    applying an ADDED rule, its pattern must not match text an earlier
    rule already wrote -- an added rule operating on earlier output can
    undo it while every regex still matches.
    """
    problems: list[str] = []
    for entry in entries:
        for problem in _static_rule_problems(entry, dep_names):
            problems.append(f"{label}: {problem}")
    for target in targets:
        text = original
        for entry in entries:
            is_added = entry not in base_entries
            if is_added and _rule_interferes(
                entry["pattern"], text, _written_regions(original, text)
            ):
                problems.append(
                    f"{label} rule {entry['pattern']!r} matches text an earlier "
                    f"rule already wrote at tag {target}; added rules must match "
                    "original text, not earlier rules' outputs"
                )
            try:
                text = apply_replacements_to_text(text, [entry], target, shas)
            except (ValueError, re.error) as exc:
                problems.append(f"{label} rule {entry['pattern']!r} does not apply: {exc}")
                break
    return problems


def validate_replacement_rules(
    base_config: dict, pr_config: dict, pr: Path, tag: str, client: GitHub,
) -> list[str]:
    """Validate replacement rules against the PR tree, now and forward.

    A rule that cannot apply bricks the next bump
    (apply_replacements_to_text raises on an invalid regex, a zero
    match, or an unresolved {sha:…}), and the monotonic policy then
    blocks removing or changing it. Each affected file is simulated
    with its full per-file rule list, in order, at the current tag AND
    at a synthetic forward tag: current-tag-only simulation passes
    over-specific rules (with target == the current tag, the generic
    rules are identity transforms, so a literal `v4\\.35\\.0` rule
    still matches; at the real next bump the generic rules rewrite
    the text first and it finds nothing). SHAs are resolved at the
    current tag for both simulations (SHA patterns are tag-agnostic).
    Static failures (bad placeholders, hardcoded literals, invalid
    regexes) are reported for every entry, added or kept.
    """
    problems: list[str] = []
    dep_names = {d["name"] for d in pr_config["deps"]}
    shas, problems = _resolve_shas(client, pr_config["deps"], tag)
    if problems:
        return problems
    targets = [tag]
    forward = _forward_tag(tag)
    if forward is not None:
        targets.append(forward)
    # Per file, with only that file's entries: entries for other files
    # must not be expected to match this one.
    base_by_path: dict[str, list[dict]] = {}
    for entry in base_config.get("doc_replacements", []):
        base_by_path.setdefault(entry["path"], []).append(entry)
    by_path: dict[str, list[dict]] = {}
    for entry in pr_config.get("doc_replacements", []):
        by_path.setdefault(entry["path"], []).append(entry)
    for path in sorted(by_path):
        file = pr / path
        if not file.is_file():
            problems.append(
                f"doc replacements target {path!r}, which is not in the PR tree"
            )
            continue
        problems.extend(_simulate_file_rules(
            by_path[path], base_by_path.get(path, []),
            file.read_text(encoding="utf-8"), targets, shas, dep_names,
            f"doc replacements for {path}",
        ))
    base_pp = base_config.get("pin_policy") or {}
    pr_pp = pr_config.get("pin_policy") or {}
    if pr_pp:
        file = pr / pr_pp["path"]
        if not file.is_file():
            problems.append(
                f"pin-policy file {pr_pp['path']!r} is not in the PR tree"
            )
        else:
            problems.extend(_simulate_file_rules(
                pr_pp.get("replacements", []), base_pp.get("replacements", []),
                file.read_text(encoding="utf-8"), targets, shas, dep_names,
                "pin-policy replacements",
            ))
    return problems


def repairable_rule_patterns(
    base_config: dict, base: Path, tag: str, client: GitHub,
) -> set[str]:
    """Patterns of base rules demonstrably broken at the next bump.

    A rule the forward simulation shows cannot apply may be removed:
    keeping it bricks the next bump, and removing it is a repair, not a
    weakening. Only the first failing rule per file is attributed (see
    _failing_rule_patterns); removing a rule whose pattern is not in
    this set stays rejected.

    Eligibility is computed against the TRUSTED BASE tree, never the PR
    tree: deriving it from PR-controlled contents would let a PR delete
    an assertion and its rule together, then claim the rule is broken
    against its own edited file.
    """
    forward = _forward_tag(tag)
    if forward is None:
        return set()
    shas, problems = _resolve_shas(client, base_config["deps"], tag)
    if problems:
        return set()
    dep_names = {d["name"] for d in base_config["deps"]}
    repairable: set[str] = set()
    by_path: dict[str, list[dict]] = {}
    for entry in base_config.get("doc_replacements", []):
        by_path.setdefault(entry["path"], []).append(entry)
    for path, entries in by_path.items():
        file = base / path
        if not file.is_file():
            continue
        repairable |= _failing_rule_patterns(
            entries, file.read_text(encoding="utf-8"), forward, shas, dep_names
        )
    base_pp = base_config.get("pin_policy") or {}
    if base_pp:
        file = base / base_pp["path"]
        if file.is_file():
            repairable |= _failing_rule_patterns(
                base_pp.get("replacements", []),
                file.read_text(encoding="utf-8"), forward, shas, dep_names,
            )
    return repairable


def config_paths_for(kind: str, base_config: dict, pr_config: dict) -> list[str]:
    """Config-derived download paths for the guard workflow.

    The workflow needs the union of base + PR doc / pin-policy paths
    (a same-pin PR may configure new ones), ledgers base-only (the
    guard requires them unchanged). Reads are defensive: a malformed
    entry is skipped, never raised -- the guard itself validates the
    schema and fails loudly, and the workflow must reach it.
    """
    # Paths are filtered to download-safe ones here: this reader is
    # deliberately defensive (no schema validation), and its output
    # feeds the workflow's downloads. An unsafe PR path is dropped, and
    # the guard then fails closed on the missing file.
    def policy_paths(config: dict) -> list[str]:
        pp = config.get("pin_policy") if isinstance(config.get("pin_policy"), dict) else {}
        p = pp.get("path")
        return [p] if _is_safe_relative_path(p) else []

    def doc_paths(config: dict) -> list[str]:
        reps = config.get("doc_replacements")
        reps = reps if isinstance(reps, list) else []
        seen: list[str] = []
        for e in reps:
            if _is_safe_relative_path(e.get("path") if isinstance(e, dict) else None) \
                    and e.get("path") not in seen:
                seen.append(e.get("path"))
        return seen

    def ledger_paths(config: dict) -> list[str]:
        led = config.get("migration_ledgers")
        return [x for x in led if _is_safe_relative_path(x)] if isinstance(led, list) else []

    if kind == "policy":
        out = []
        for p in policy_paths(base_config) + policy_paths(pr_config):
            if p not in out:
                out.append(p)
        return out
    if kind == "doc":
        out = []
        for p in doc_paths(base_config) + doc_paths(pr_config):
            if p not in out:
                out.append(p)
        return out
    if kind == "ledger":
        return ledger_paths(base_config)
    raise ValueError(f"unknown config-paths kind: {kind!r}")


def cmd_config_paths(args: argparse.Namespace) -> int:
    try:
        base_config = load_config(Path("."))
    except (OSError, ValueError, json.JSONDecodeError):
        base_config = {}
    pr_config: dict = {}
    if args.pr_config:
        try:
            with open(args.pr_config, encoding="utf-8") as f:
                pr_config = json.load(f)
            if not isinstance(pr_config, dict):
                pr_config = {}
        except (OSError, ValueError, json.JSONDecodeError):
            pr_config = {}
    print(" ".join(config_paths_for(args.kind, base_config, pr_config)))
    return 0


def current_tag(root: Path, config: dict) -> str:
    """The single tag all pinned pins must agree on, or an error."""
    toolchain = toolchain_tag(root)
    revs = {}
    wanted = {dep["name"] for dep in config["deps"]}
    for entry in lakefile_requires(root):
        if entry.get("name") in wanted:
            rev = entry.get("rev")
            if not isinstance(rev, str):
                raise ValueError(
                    f"lakefile.toml require {entry.get('name')!r} has a non-string rev: {rev!r}"
                )
            revs[entry["name"]] = rev
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
    if allow_rc and not manual:
        return (
            "", None,
            "--allow-rc requires an explicit -rc target; auto-selection "
            "only picks final releases",
        )
    if allow_rc and manual:
        _require_explicit_rc_target(manual, allow_rc=allow_rc)
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


def _manifest_packages(manifest: dict) -> list:
    packages = manifest.get("packages", [])
    if not isinstance(packages, list):
        raise ValueError("lake-manifest.json packages must be a list")
    for pkg in packages:
        if not isinstance(pkg, dict) or not isinstance(pkg.get("name"), str):
            raise ValueError(
                "lake-manifest.json packages must be tables with a string name"
            )
    return packages


def direct_entries(manifest: dict) -> dict[str, dict]:
    return {
        pkg["name"]: pkg
        for pkg in _manifest_packages(manifest)
        if not pkg.get("inherited", False)
    }


def check_no_duplicate_packages(manifest: dict, label: str) -> list[str]:
    names = [pkg.get("name") for pkg in _manifest_packages(manifest)]
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
        # These hold for every direct entry, including one the base tree
        # does not have (a newly added dependency has no base entry to
        # compare against, so it must be checked on its own: a new dep
        # pointing at a fork URL or a subdirectory must fail here).
        expected_url = f"https://github.com/{dep['repo']}"
        if entry.get("type") != "git":
            problems.append(f"{name}: type {entry.get('type')!r} != 'git'")
        if entry.get("url", "").rstrip("/").removesuffix(".git") != expected_url:
            problems.append(f"{name}: url {entry.get('url')!r} != {expected_url!r}")
        if entry.get("subDir") is not None:
            problems.append(f"{name}: subDir must be null")
        if entry.get("manifestFile") != "lake-manifest.json":
            problems.append(f"{name}: manifestFile must be lake-manifest.json")
        if entry.get("configFile") not in {"lakefile.lean", "lakefile.toml"}:
            problems.append(f"{name}: configFile must be lakefile.lean or lakefile.toml")
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


def _redact(text: str, secrets) -> str:
    for secret in secrets:
        if secret:
            text = text.replace(secret, "[redacted]")
    return text


def run(cmd: list[str], *, cwd: Path | None = None, env: dict | None = None,
        redact=()) -> str:
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True)
    if result.returncode != 0:
        display = _redact(" ".join(cmd), redact)
        stderr = _redact(result.stderr.strip(), redact)
        raise RuntimeError(f"{display} failed: {stderr}")
    return result.stdout.strip()


def push_branch(repo: str, branch: str, token: str) -> None:
    """Push HEAD to ``branch`` without the token in argv or error output.

    The token reaches git only through ``$APP_TOKEN`` in the child env,
    read by a credential helper that answers ``get`` requests only
    (``store``/``erase`` are ignored). The push URL carries no
    credentials, so neither the process command line nor git's stderr
    can expose the token; ``redact`` is defense-in-depth for any
    command error that echoes secret-bearing arguments.
    """
    helper = (
        "!f() { if [ \"$1\" = get ]; then cat >/dev/null; "
        "printf 'username=%s\\npassword=%s\\n' 'x-access-token' \"$APP_TOKEN\"; fi; }; f"
    )
    env = {**os.environ, "APP_TOKEN": token}
    run(
        ["git", "-c", f"credential.helper={helper}", "push",
         f"https://github.com/{repo}.git", f"HEAD:refs/heads/{branch}"],
        env=env, redact=(token,),
    )


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
        ledgers = config.get("migration_ledgers") or []
        if ledgers:
            ledger_rel, checks_rel = _migration_ledger_paths(config)
            prepared_ledger = json.loads(
                (root / ledger_rel).read_text(encoding="utf-8"))
            prepared_checks = json.loads(
                (root / checks_rel).read_text(encoding="utf-8"))
            mathlib = next(
                d for d in config["deps"] if d["name"] == "mathlib")
            try:
                problems.extend(verify_apis_exist_at_pin(
                    client, prepared_ledger, prepared_checks,
                    mathlib_sha=shas["mathlib"],
                    mathlib_repo=mathlib["repo"],
                ))
            except Exception as exc:  # noqa: BLE001 - fail closed on any verification error
                problems.append(f"migration API existence check failed: {exc}")
    except (ValueError, RuntimeError) as exc:
        print(f"prepare: FAIL - {exc}", file=sys.stderr)
        return 1
    if problems:
        print("prepare: FAIL - verification failed after lake update:")
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
    pin-policy file, the doc replacements, and the migration ledgers
    (exactly the base pair re-pinned, plus Mathlib API existence at
    the prepared SHA). A compromised prepare step that rewrites a
    whitelisted file to arbitrary contents fails here, before any
    write credential exists, even though the filenames are unchanged.
    """
    problems: list[str] = []
    if allow_rc and RC_RE.fullmatch(target) is None:
        return [
            "--allow-rc requires an explicit -rc target "
            f"(got {target!r}); auto-selection and final targets do not "
            "go on an -rc branch"
        ]
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

    # Migration ledgers: exactly the base pair re-pinned to the prepared
    # manifest pins -- a pin-consistent pair with replaced records or a
    # changed migration status must fail here -- and every Mathlib API
    # pointer must still name a declaration at the prepared Mathlib SHA.
    # The base pair comes from the trusted base tree, like the manifest
    # and lakefile above; the base manifest/toolchain give the old pins.
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
            base_ledger = json.loads(base_text(ledger_rel))
            base_checks = json.loads(base_text(checks_rel))
            base_manifest_obj = json.loads(base_text("lake-manifest.json"))
            base_mathlib = next(
                p["rev"] for p in base_manifest_obj["packages"]
                if p["name"] == "mathlib"
            )
            base_toolchain = base_text("lean-toolchain").strip()
            problems.extend(check_ledgers_match_expected(
                prepared_ledger, prepared_checks,
                base_ledger=base_ledger, base_checks=base_checks,
                old_mathlib=base_mathlib, old_lean=base_toolchain,
                new_mathlib=prepared_mathlib,
                new_lean=f"leanprover/lean4:{target}",
            ))
            mathlib_dep = next(
                d for d in config["deps"] if d["name"] == "mathlib")
            try:
                problems.extend(verify_apis_exist_at_pin(
                    client, prepared_ledger, prepared_checks,
                    mathlib_sha=prepared_mathlib,
                    mathlib_repo=mathlib_dep["repo"],
                ))
            except Exception as exc:  # noqa: BLE001 - fail closed
                problems.append(f"migration API existence check failed: {exc}")
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
    branch = bump_branch(target)
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
            push_branch(client.repo, branch, app_token)
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
    try:
        base_config = load_config(base)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        # A malformed base config fails loudly here instead of bricking
        # the workflow (whose config reads are defensive, so it reaches
        # this point). Repairing it needs a branch-protection bypass:
        # every guard run fails until the base config is fixed.
        print(f"guard: FAIL - base {CONFIG_FILE} is malformed: {exc}")
        return 1
    client = GitHub()
    changed = {
        line.strip() for line in Path(args.changed_files).read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    # Guard-code changes are fine on their own (the running script is base
    # code, and the change itself gets normal review), but a PR that also
    # changes pins or config must not touch guard code: the weakened code
    # would become the base for the next validation.
    if changed & set(GUARD_FILES) and (changed & (set(PIN_FILES) | {CONFIG_FILE})):
        print("guard: FAIL - a pin/config-change PR must not touch the guard code or the bump workflow")
        return 1
    # The config is validated even when no pin file changed: otherwise a
    # PR touching only pinned_deps.json would sail through the old
    # pin-files-only early return and could repoint/remove a dependency
    # or weaken a replacement unexamined. A PR tree that predates the
    # config file (and does not touch it) is treated as base-config.
    problems: list[str] = []
    pr_config_path = pr / CONFIG_FILE
    if CONFIG_FILE in changed:
        if not pr_config_path.is_file():
            print(f"guard: FAIL - {CONFIG_FILE} was deleted")
            return 1
        try:
            pr_config = load_config_file(pr_config_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            print(f"guard: FAIL - cannot read PR {CONFIG_FILE}: {exc}")
            return 1
        # Repair allowance: a base rule the forward simulation shows
        # cannot apply at the next bump may be removed. Computed from
        # the base tree's tag (the PR's tag is not trusted yet).
        repairable: frozenset[str] = frozenset()
        try:
            early_tag = current_tag(base, base_config)
        except ValueError:
            early_tag = None  # tag errors surface again below
        if early_tag is not None:
            repairable = frozenset(
                repairable_rule_patterns(base_config, base, early_tag, client)
            )
        problems.extend(
            check_config_extension(base_config, pr_config, repairable)
        )
    elif pr_config_path.is_file():
        try:
            pr_config = load_config_file(pr_config_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            print(f"guard: FAIL - cannot read PR {CONFIG_FILE}: {exc}")
            return 1
        if pr_config != base_config:
            problems.append(
                f"{CONFIG_FILE} differs from base but is not in the changed-file list; "
                "failing closed (enumeration inconsistency)"
            )
    else:
        pr_config = base_config
    if not (changed & set(PIN_FILES)):
        # Config-only (or unrelated) PR: still check the require-names
        # invariant, so a config-only dependency addition without the
        # lakefile half fails instead of silently drifting the config.
        try:
            base_req_names = {e.get("name") for e in lakefile_requires(base)}
            pr_req_names = {e.get("name") for e in lakefile_requires(pr)}
        except ValueError as exc:
            print(f"guard: FAIL - {exc}")
            return 1
        if base_req_names != {d["name"] for d in base_config["deps"]}:
            problems.append("base lakefile requires do not match base pinned_deps.json")
        if pr_req_names != {d["name"] for d in pr_config["deps"]}:
            problems.append(
                "PR lakefile requires do not match PR pinned_deps.json; "
                "extend the config in the same PR when adding a dependency"
            )
        # Defense in depth: the lakefile is not in the changed list here,
        # so base and PR lakefiles should agree; a source repoint hiding
        # behind a wrong changed list must still fail.
        try:
            base_tag_only = current_tag(base, base_config)
        except ValueError as exc:
            problems.append(str(exc))
        else:
            problems.extend(
                check_lakefile_sources(base, pr, base_config, pr_config, base_tag_only)
            )
            # Added replacement rules must already work against the PR
            # tree; a broken rule bricks the next bump and the monotonic
            # policy then blocks repairing it.
            problems.extend(
                validate_replacement_rules(base_config, pr_config, pr, base_tag_only, client)
            )
        if problems:
            print("guard: FAIL")
            for problem in problems:
                print(f"  - {problem}")
            return 1
        print("guard: PASS - no pin files changed"
              + ("; config extension validated" if CONFIG_FILE in changed else ""))
        return 0
    # The lakefile's requires must match the config's deps at both ends.
    # This is what makes a same-pin dependency addition well-defined: the
    # PR must extend pinned_deps.json in the same PR that adds the require,
    # so the config never drifts from the lakefile.
    try:
        base_req_names = {e.get("name") for e in lakefile_requires(base)}
        pr_req_names = {e.get("name") for e in lakefile_requires(pr)}
    except ValueError as exc:
        print(f"guard: FAIL - {exc}")
        return 1
    if base_req_names != {d["name"] for d in base_config["deps"]}:
        problems.append(
            "base lakefile requires do not match base pinned_deps.json "
            f"({sorted(base_req_names)} vs {sorted(d['name'] for d in base_config['deps'])})"
        )
    if pr_req_names != {d["name"] for d in pr_config["deps"]}:
        problems.append(
            "PR lakefile requires do not match PR pinned_deps.json; "
            "extend the config in the same PR when adding a dependency "
            f"({sorted(pr_req_names)} vs {sorted(d['name'] for d in pr_config['deps'])})"
        )
    try:
        base_tag = current_tag(base, base_config)
        pr_tag = current_tag(pr, pr_config)
    except ValueError as exc:
        print(f"guard: FAIL - {exc}")
        return 1
    if version_key(pr_tag) < version_key(base_tag):
        problems.append(f"PR tag {pr_tag} is older than base tag {base_tag} (downgrade)")
        print("guard: FAIL")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    try:
        base_manifest = load_manifest(base)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"guard: FAIL - cannot read base manifest: {exc}")
        return 1
    if version_key(pr_tag) == version_key(base_tag):
        # Same-pin change (e.g. adding a dependency/library at the current
        # pin, doc edits, a restructured pin-policy file, ledger content
        # changes). Only the pins themselves are guarded: the toolchain
        # must still be the base toolchain, and the manifest must be
        # exactly derived from the effective deps at the base tag.
        # Bump-only checks are skipped: pin-policy/doc/ledger exact
        # re-pin checks would forbid legitimate same-pin restructuring,
        # and the pin-policy file is self-validating in CI
        # (check_lake_surface.py fails preflight if its constants disagree
        # with the manifest) while the ledger validator covers ledgers.
        _ = merge_base
        if (pr / "lean-toolchain").read_text(encoding="utf-8").strip() != (
            base / "lean-toolchain"
        ).read_text(encoding="utf-8").strip():
            problems.append("same-pin change must not change lean-toolchain")
        # Existing requires must keep their source fields (scope/git/path):
        # names and revs alone would let a scope repoint to an attacker's
        # fork pass.
        problems.extend(
            check_lakefile_sources(base, pr, base_config, pr_config, base_tag)
        )
        # Added replacement rules must already work against the PR tree;
        # a broken rule bricks the next bump and the monotonic policy
        # then blocks repairing it. Also catches doc edits in this PR
        # that break an existing rule's match.
        problems.extend(
            validate_replacement_rules(base_config, pr_config, pr, base_tag, client)
        )
        try:
            problems.extend(verify_manifest(client, pr, pr_config, base_tag, base_manifest))
        except (OSError, ValueError) as exc:
            problems.append(f"PR manifest is unreadable or malformed: {exc}")
        if client.tag_sha(base_config["toolchain_repo"], base_tag) is None:
            problems.append(
                f"Lean tag {base_tag} does not exist in {base_config['toolchain_repo']}"
            )
        if problems:
            print("guard: FAIL")
            for problem in problems:
                print(f"  - {problem}")
            return 1
        print(f"guard: PASS - same-pin change at {base_tag} validated")
        return 0
    # Bump: pr_tag > base_tag. The config must be unchanged here: an
    # extension belongs in a same-pin PR first, so the bump validates
    # against exactly the config it was prepared from.
    if pr_config != base_config:
        problems.append(
            "pinned_deps.json changed in a bump PR; extend the config in a "
            "same-pin PR first, then bump"
        )
    config = base_config
    if not is_final(pr_tag):
        problems.append(f"PR tag {pr_tag!r} is not a final release tag")
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
    shas = None
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
    # Doc replacements: exactly the base file with the configured
    # replacements applied for the new tag, as validate_prepared_contents
    # checks the prepared tree. A pin-change PR that omits, reverts, or
    # arbitrarily edits a configured doc file must fail here, not pass
    # on the strength of the pin files alone. A doc file missing from
    # the PR tree, or present in the PR tree but not the base tree,
    # fails closed: there is no base text to derive the expected file
    # from, or the PR deleted a file the bump is supposed to update.
    by_path: dict[str, list[dict]] = {}
    for entry in config.get("doc_replacements", []):
        by_path.setdefault(entry["path"], []).append(entry)
    for path, entries in by_path.items():
        try:
            base_file = base / path
            pr_file = pr / path
            if not base_file.is_file() and not pr_file.is_file():
                continue
            if not base_file.is_file():
                problems.append(
                    f"{path} is present in the PR tree but not the base "
                    "tree; cannot derive its expected bumped contents"
                )
                continue
            if not pr_file.is_file():
                problems.append(
                    f"{path} is missing from the PR tree; "
                    "the bump must update it, not delete it"
                )
                continue
            if shas is None:
                shas = resolve_shas(client, config, pr_tag)
            expected = base_file.read_text(encoding="utf-8")
            for entry in entries:
                expected = apply_replacements_to_text(
                    expected, [entry], pr_tag, shas
                )
            if pr_file.read_text(encoding="utf-8") != expected:
                problems.append(
                    f"{path} does not match the base file with the "
                    "new tag applied (missing update, revert, or an "
                    "unrelated edit)"
                )
        except (ValueError, OSError) as exc:
            problems.append(f"doc validation failed for {path}: {exc}")
    # Migration ledgers: if either tree carries them, the PR tree's pair
    # must be exactly the base pair re-pinned to the PR's pins -- a
    # pin-consistent pair with replaced records or a changed migration
    # status must fail here, not just a stale-pin pair -- and every
    # Mathlib API pointer must still name a declaration at the PR's
    # Mathlib SHA. Otherwise the bump PR leaves the migration validator
    # failing on stale pins, or records audit pointers that no longer
    # name an upstream declaration.
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
            base_manifest_for_ledgers = load_manifest(base)
            base_mathlib = next(
                p["rev"] for p in base_manifest_for_ledgers["packages"]
                if p["name"] == "mathlib"
            )
            base_toolchain = (base / "lean-toolchain").read_text(
                encoding="utf-8").strip()
            base_ledger = json.loads(
                (base / ledger_rel).read_text(encoding="utf-8"))
            base_checks = json.loads(
                (base / checks_rel).read_text(encoding="utf-8"))
            problems.extend(check_ledgers_match_expected(
                pr_ledger, pr_checks,
                base_ledger=base_ledger, base_checks=base_checks,
                old_mathlib=base_mathlib, old_lean=base_toolchain,
                new_mathlib=pr_mathlib,
                new_lean=f"leanprover/lean4:{pr_tag}",
            ))
            mathlib_dep = next(
                d for d in config["deps"] if d["name"] == "mathlib")
            try:
                problems.extend(verify_apis_exist_at_pin(
                    client, pr_ledger, pr_checks,
                    mathlib_sha=pr_mathlib,
                    mathlib_repo=mathlib_dep["repo"],
                ))
            except Exception as exc:  # noqa: BLE001 - fail closed
                problems.append(f"migration API existence check failed: {exc}")
        except (OSError, json.JSONDecodeError, KeyError, StopIteration, ValueError) as exc:
            problems.append(f"migration ledgers are unreadable or inconsistent: {exc}")
    _ = merge_base
    try:
        base_manifest = load_manifest(base)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"guard: FAIL - cannot read base manifest: {exc}")
        return 1
    try:
        problems.extend(verify_manifest(client, pr, config, pr_tag, base_manifest))
    except (OSError, ValueError) as exc:
        problems.append(f"PR manifest is unreadable or malformed: {exc}")
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
    p_paths = sub.add_parser(
        "config-paths", help="print union config-derived download paths for the guard workflow")
    p_paths.add_argument("--kind", choices=["policy", "doc", "ledger"], required=True)
    p_paths.add_argument("--pr-config", default="")
    p_paths.set_defaults(func=cmd_config_paths)
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
