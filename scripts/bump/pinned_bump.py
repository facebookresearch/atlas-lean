#!/usr/bin/env python3
"""Pinned-release-only Lean/Mathlib bump automation.

One module, three entry points (see .github/workflows/bump-pinned-release.yml
and bump-guard.yml):

  select   Credential-free. Pick the next final release tag shared by every
           pinned dependency (Lean, Mathlib, CSLib, plus Physlib/repl where
           configured), or print an empty target. Never writes anything and
           never sees the App secret. Adapted from TauCeti's select/publish
           split: the selector cannot push, the publisher never executes
           upstream code.
  publish  App-token only. Apply the selected tag to lean-toolchain,
           lakefile.toml, README/BACKPORTS version lines, run `lake update`,
           verify the manifest, and open the bump PR. If the bump branch
           already exists it is left alone: it may already contain human
           repair commits (CSLib #1172 shape), and the bot must not rewrite
           them. No auto-merge: a human merges after CI green plus repairs.
  guard    Run on every PR touching the pin files, from trusted base code
           (pull_request_target). Validates a pin-change PR without building
           it or running any PR code. Adapted from TauCeti's check-bump.sh:
           lakefile changes only in pinned revs, all to one final tag;
           toolchain matches that tag; every direct manifest entry has
           inputRev == tag and rev == that dep's tag SHA; the transitive
           manifest is exactly the union of the deps' manifests at the tag;
           Mathlib@tag has a successful master-push build (so its oleans
           are published to the cache).

Nothing here tracks nightly, master, last-known-good, or first-known-bad
commits. A `-rc` tag is accepted only via an explicit manual dispatch with
--allow-rc, and then only onto a bump-pinned-rc/ branch.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

FINAL_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)$")
RC_RE = re.compile(r"^v(\d+)\.(\d+)\.(\d+)-rc(\d+)$")
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
PIN_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")


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


def toolchain_tag(root: Path) -> str:
    text = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    prefix = "leanprover/lean4:"
    if not text.startswith(prefix):
        raise ValueError(f"unexpected lean-toolchain content: {text!r}")
    return text[len(prefix):]


def lakefile_requires(root: Path) -> list[dict]:
    with open(root / "lakefile.toml", "rb") as f:
        data = tomllib.load(f)
    requires = data.get("require", [])
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


def apply_pin_edits(root: Path, config: dict, current: str, target: str) -> list[str]:
    """Edit toolchain, lakefile revs, and doc version lines. Return changed files."""
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
        replacement = entry["replacement"].replace("{target}", target)
        new_content, count = re.subn(entry["pattern"], replacement, content)
        if count == 0:
            raise ValueError(
                f"doc replacement pattern {entry['pattern']!r} did not match {entry['path']}"
            )
        if new_content != content:
            path.write_text(new_content, encoding="utf-8")
            changed.append(entry["path"])
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


def verify_manifest(
    client: GitHub, root: Path, config: dict, target: str
) -> list[str]:
    """Check direct + transitive manifest entries against deps@target."""
    problems: list[str] = []
    manifest = load_manifest(root)
    direct = direct_entries(manifest)
    wanted = {dep["name"]: dep for dep in config["deps"]}
    if set(direct) != set(wanted):
        problems.append(
            f"direct manifest entries {sorted(direct)} != pinned deps {sorted(wanted)}"
        )
    for name, dep in wanted.items():
        entry = direct.get(name)
        if entry is None:
            continue
        sha = client.tag_sha(dep["repo"], target)
        if sha is None:
            problems.append(f"could not resolve tag SHA for {name} {target}")
            continue
        if entry.get("inputRev") != target:
            problems.append(f"{name}: inputRev {entry.get('inputRev')!r} != {target!r}")
        if entry.get("rev") != sha:
            problems.append(f"{name}: rev {entry.get('rev')!r} != tag SHA {sha}")
        expected_url = f"https://github.com/{dep['repo']}"
        if entry.get("url", "").rstrip("/").removesuffix(".git") != expected_url:
            problems.append(f"{name}: url {entry.get('url')!r} != {expected_url!r}")
    # Transitive entries must be exactly the union of the deps' manifests.
    expected: dict[str, dict] = {}
    for name, dep in wanted.items():
        sha = client.tag_sha(dep["repo"], target)
        if not sha:
            continue
        upstream = json.loads(client.contents(dep["repo"], "lake-manifest.json", sha))
        for pkg in upstream.get("packages", []):
            if pkg.get("name") in wanted:
                continue
            expected.setdefault(pkg["name"], dict(pkg, inherited=True))
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


def cmd_publish(args: argparse.Namespace) -> int:
    root = Path.cwd()
    config = load_config(root)
    client = GitHub()
    current = current_tag(root, config)
    target = args.target
    if not is_version_tag(target, allow_rc=args.allow_rc):
        print(f"error: target {target!r} is not a version tag", file=sys.stderr)
        return 2
    if version_key(target) <= version_key(current):
        print(f"error: target {target} is not newer than current {current}", file=sys.stderr)
        return 2
    branch = f"bump-pinned-rc/{target}" if args.allow_rc else f"bump-pinned/{target}"
    remote = run(["git", "ls-remote", "--heads", "origin", branch])
    if remote:
        print(f"branch {branch} already exists; leaving it alone (repairs may be in progress)")
        return 0
    # Close superseded bot-only bump PRs for older targets.
    for pr in client.open_prs():
        head = (pr.get("head") or {}).get("ref", "")
        if not head.startswith("bump-pinned/") or head == branch:
            continue
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
    changed = apply_pin_edits(root, config, current, target)
    print(f"edited: {', '.join(changed)}")
    run(["lake", "update"], cwd=root)
    changed.append("lake-manifest.json")
    problems = verify_manifest(client, root, config, target)
    if problems:
        print("manifest verification failed after lake update:", file=sys.stderr)
        for problem in problems:
            print(f"  - {problem}", file=sys.stderr)
        return 1
    bot_name = os.environ.get("BUMP_BOT_NAME") or "bump-pinned-release[bot]"
    bot_email = os.environ.get("BUMP_BOT_NAME_EMAIL") or (
        "bump-pinned-release[bot]@users.noreply.github.com"
    )
    run(["git", "config", "user.name", bot_name])
    run(["git", "config", "user.email", bot_email])
    run(["git", "add"] + sorted(set(changed)))
    run(["git", "commit", "-m", f"Bump pinned Lean/Mathlib to {target}"])
    run(["git", "push", "origin", f"HEAD:refs/heads/{branch}"])
    rows = []
    for dep in config["deps"]:
        rows.append(
            f"| {dep['name']} | `{current}` | `{target}` | "
            f"{client.tag_sha(dep['repo'], target)} |"
        )
    body = (
        f"Bump the pinned Lean/Mathlib release from `{current}` to `{target}`.\n\n"
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
    run([
        "gh", "pr", "create", "--repo", client.repo, "--base", "main",
        "--head", branch, "--title", f"Bump pinned Lean/Mathlib to {target}",
        "--body-file", str(body_file),
    ])
    print(f"opened bump PR on {branch}")
    return 0


def cmd_select(args: argparse.Namespace) -> int:
    root = Path.cwd()
    config = load_config(root)
    client = GitHub()
    try:
        target, run_id, reason = select_target(
            client, root, config,
            manual=args.target or "", allow_rc=args.allow_rc,
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
    if changed & {".github/workflows/bump-guard.yml", "scripts/bump/pinned_bump.py",
                  "scripts/bump/pinned_deps.json"}:
        print("guard: FAIL - a pin-change PR must not touch the guard or its config")
        return 1
    if changed & {".github/workflows/bump-pinned-release.yml"}:
        print("guard: FAIL - a pin-change PR must not touch the bump workflow")
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
    base_reqs = {e["name"]: e for e in lakefile_requires(base)}
    pr_reqs = {e["name"]: e for e in lakefile_requires(pr)}
    if set(base_reqs) != set(pr_reqs):
        problems.append(f"lakefile require names changed: {sorted(base_reqs)} -> {sorted(pr_reqs)}")
    for name in sorted(set(base_reqs) & set(pr_reqs)):
        diff = sorted(
            k for k in set(base_reqs[name]) | set(pr_reqs[name])
            if k != "rev" and base_reqs[name].get(k) != pr_reqs[name].get(k)
        )
        if diff:
            problems.append(f"lakefile {name} changed fields other than rev: {diff}")
        if pr_reqs[name].get("rev") != pr_tag and name in {d["name"] for d in config["deps"]}:
            problems.append(f"lakefile {name} rev {pr_reqs[name].get('rev')!r} != PR tag {pr_tag!r}")
    # The PR's own delta (vs merge-base) must not change pin files the PR does
    # not claim: if the PR tag differs from the merge-base tag, the tag above
    # already validates the full jump.
    _ = merge_base
    problems.extend(verify_manifest(client, pr, config, pr_tag))
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
    p_publish = sub.add_parser("publish", help="publish the bump PR for a selected target")
    p_publish.add_argument("target")
    p_publish.add_argument("--allow-rc", action="store_true")
    p_publish.set_defaults(func=cmd_publish)
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
