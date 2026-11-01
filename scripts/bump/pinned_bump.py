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
    return sorted(set(files))


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


def _is_superseded_candidate(pr: dict, repo: str, branch: str) -> bool:
    """True if `pr` is a same-repo bump PR on an older target branch: the
    head repository must match, so a fork PR reusing a `bump-pinned/`
    branch name is never closed as superseded."""
    head = pr.get("head") or {}
    ref = head.get("ref", "")
    return (
        ref.startswith("bump-pinned/")
        and ref != branch
        and (head.get("repo") or {}).get("full_name") == repo
    )


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
        return self.api(f"repos/{self.repo}/pulls/{number}/commits?per_page=100")

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
    """Edit toolchain, lakefile revs, doc + pin-policy version lines."""
    shas = shas or {}
    changed: list[str] = []
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
    resolve_shas(client, config, target)
    mathlib = next(d for d in config["deps"] if d["name"] == "mathlib")
    sha = client.tag_sha(mathlib["repo"], target)
    if sha and client.successful_master_build_run(mathlib["repo"], sha) is None:
        raise ValueError(f"mathlib {target} has no successful master-push build")
    head_toolchain = run(["git", "show", "HEAD:lean-toolchain"]).strip()
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
        if not _is_superseded_candidate(pr, client.repo, branch):
            continue
        head = (pr.get("head") or {}).get("ref", "")
        commits = client.pr_commits(pr["number"])
        authors = {(c.get("author") or {}).get("login", "") for c in commits}
        if authors and all(a.endswith("[bot]") for a in authors):
            client.close_pr(
                pr["number"],
                f"Superseded by the bump to {target}: this PR is bot-only, "
                "so it is safe to close. A PR with human repair commits is never closed here.",
            )
            print(f"closed superseded bot-only bump PR #{pr['number']}")
        else:
            print(f"leaving {head} (#{pr['number']}) alone: it has non-bot commits")
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
