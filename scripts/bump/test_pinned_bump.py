#!/usr/bin/env python3
"""Unit tests for pinned_bump.py. No network, no git, no Lake. Run:
python3 scripts/bump/test_pinned_bump.py
"""

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import pinned_bump
from pinned_bump import GitHub, apply_pin_edits, current_tag, load_config, select_target

CONFIG = {
    "toolchain_repo": "leanprover/lean4",
    "deps": [
        {"name": "mathlib", "repo": "leanprover-community/mathlib4"},
        {"name": "cslib", "repo": "leanprover/cslib"},
    ],
    "doc_replacements": [
        {"path": "README.md", "pattern": "Lean-v[0-9]+\\.[0-9]+\\.[0-9]+",
         "replacement": "Lean-{target}"},
        {"path": "README.md", "pattern": 'alt="Lean v[0-9]+\\.[0-9]+\\.[0-9]+"',
         "replacement": 'alt="Lean {target}"'},
    ],
}

SHAS = {
    ("leanprover/lean4", "v4.35.0"): "1" * 40,
    ("leanprover/lean4", "v4.36.0"): "2" * 40,
    ("leanprover-community/mathlib4", "v4.35.0"): "3" * 40,
    ("leanprover-community/mathlib4", "v4.36.0"): "4" * 40,
    ("leanprover/cslib", "v4.35.0"): "5" * 40,
    ("leanprover/cslib", "v4.36.0"): "6" * 40,
    ("leanprover-community/physlib", "v4.35.0"): "7" * 40,
    ("leanprover-community/physlib", "v4.36.0"): "8" * 40,
    ("leanprover-community/repl", "v4.35.0"): "9" * 40,
    ("leanprover-community/repl", "v4.36.0"): "a" * 40,
}

BATTERIES = {
    "name": "batteries", "type": "git",
    "url": "https://github.com/leanprover-community/batteries",
    "rev": "b" * 40, "inputRev": "main", "inherited": False,
    "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json",
}
QQ = {
    "name": "Qq", "type": "git",
    "url": "https://github.com/leanprover-community/quote4",
    "rev": "c" * 40, "inputRev": "master", "inherited": False,
    "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json",
}


def upstream_manifest(names):
    pkgs = []
    if "batteries" in names:
        pkgs.append(dict(BATTERIES))
    if "Qq" in names:
        pkgs.append(dict(QQ))
    return {"version": "1.3.0", "packages": pkgs}


class FakeGitHub(GitHub):
    def __init__(self, *, tags, run_id=123, upstream=None):
        super().__init__(repo="example/repo")
        self._tags = tags
        self._run_id = run_id
        self._upstream = upstream or {}

    def tags(self, slug):
        return [{"name": t, "commit": {"sha": SHAS[(slug, t)]}} for t in self._tags.get(slug, [])]

    def tag_sha(self, slug, tag):
        return SHAS.get((slug, tag))

    def successful_master_build_run(self, slug, sha):
        return self._run_id

    def contents(self, slug, path, ref):
        return json.dumps(self._upstream[(slug, ref)]).encode()

    def open_prs(self):
        return []

    def pr_commits(self, number):
        return []

    def close_pr(self, number, comment):
        raise AssertionError("close_pr should not be called in these tests")


def write_tree(root: Path, tag: str, *, tamper_toolchain=False, tamper_transitive=False):
    (root / "lean-toolchain").write_text(
        f"leanprover/lean4:{'v4.35.0' if tamper_toolchain else tag}\n")
    requires = "\n".join(
        '[[require]]\nname = "%s"\nrev = "%s"' % (d["name"], tag) for d in CONFIG["deps"]
    )
    (root / "lakefile.toml").write_text('name = "fixture"\n\n' + requires + "\n")
    (root / "README.md").write_text(
        'badge Lean-v4.35.0 <img alt="Lean v4.35.0" /> end\n')
    (root / "BACKPORTS.md").write_text("The repository now pins Mathlib and Lean `v4.35.0`.\n")
    direct = []
    for dep in CONFIG["deps"]:
        direct.append({
            "name": dep["name"], "type": "git",
            "url": f"https://github.com/{dep['repo']}",
            "rev": SHAS[(dep["repo"], tag)], "inputRev": tag, "inherited": False,
            "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json",
        })
    transitive = [dict(BATTERIES, inherited=True), dict(QQ, inherited=True)]
    if tamper_transitive:
        transitive[0] = dict(transitive[0], rev="d" * 40)
    (root / "lake-manifest.json").write_text(
        json.dumps({"version": "1.3.0", "packages": direct + transitive}, indent=1))


class SelectTests(unittest.TestCase):
    def test_noop_when_a_dep_has_no_new_tag(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_tree(root, "v4.35.0")
            client = FakeGitHub(tags={
                "leanprover/lean4": ["v4.35.0", "v4.36.0"],
                "leanprover-community/mathlib4": ["v4.35.0", "v4.36.0"],
                "leanprover/cslib": ["v4.35.0"],  # no v4.36.0 yet
            })
            target, _, reason = select_target(client, root, CONFIG)
            self.assertEqual(target, "")
            self.assertIn("cslib", reason)

    def test_selects_newest_tag_present_everywhere_with_cache(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_tree(root, "v4.35.0")
            client = FakeGitHub(tags={slug: ["v4.35.0", "v4.36.0"] for slug in [
                "leanprover/lean4", "leanprover-community/mathlib4",
                "leanprover/cslib"]})
            target, run_id, _ = select_target(client, root, CONFIG)
            self.assertEqual(target, "v4.36.0")
            self.assertEqual(run_id, 123)

    def test_noop_when_cache_unpublished(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_tree(root, "v4.35.0")
            client = FakeGitHub(
                tags={slug: ["v4.35.0", "v4.36.0"] for slug in [
                    "leanprover/lean4", "leanprover-community/mathlib4",
                    "leanprover/cslib"]},
                run_id=None)
            target, _, _ = select_target(client, root, CONFIG)
            self.assertEqual(target, "")

    def test_manual_rc_rejected_without_allow_rc(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_tree(root, "v4.35.0")
            client = FakeGitHub(tags={})
            with self.assertRaises(ValueError):
                select_target(client, root, CONFIG, manual="v4.36.0-rc1", allow_rc=False)


class EditTests(unittest.TestCase):
    def test_apply_pin_edits(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_tree(root, "v4.35.0")
            changed = apply_pin_edits(root, CONFIG, "v4.35.0", "v4.36.0")
            self.assertEqual(current_tag(root, CONFIG), "v4.36.0")
            self.assertIn("Lean-v4.36.0", (root / "README.md").read_text())
            self.assertIn('alt="Lean v4.36.0"', (root / "README.md").read_text())
            self.assertNotIn('alt="Lean v4.35.0"', (root / "README.md").read_text())
            self.assertIn("README.md", changed)

    def test_apply_pin_edits_updates_pin_policy_constants(self):
        repo_root = Path(__file__).resolve().parent.parent.parent
        real_config = load_config(repo_root)
        shas = {d["name"]: SHAS[(d["repo"], "v4.36.0")] for d in real_config["deps"]}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_tree(root, "v4.35.0")
            with open(root / "README.md", "a", encoding="utf-8") as f:
                f.write("https://github.com/leanprover/lean4/releases/tag/v4.35.0\n")
            (root / "scripts").mkdir()
            policy_src = repo_root / real_config["pin_policy"]["path"]
            (root / real_config["pin_policy"]["path"]).write_text(
                policy_src.read_text())
            changed = apply_pin_edits(root, real_config, "v4.35.0", "v4.36.0", shas)
            self.assertIn("scripts/check_lake_surface.py", changed)
            readme = (root / "README.md").read_text()
            self.assertIn('alt="Lean v4.36.0"', readme)
            self.assertNotIn('alt="Lean v4.35.0"', readme)
            policy = (root / real_config["pin_policy"]["path"]).read_text()
            self.assertIn('"v4.36.0"', policy)
            self.assertIn(shas["mathlib"], policy)
            self.assertIn(shas["cslib"], policy)
            self.assertNotIn("v4.35.0", policy)


class GuardTests(unittest.TestCase):
    def _run_guard(self, *, tamper_toolchain=False, tamper_transitive=False,
                   tamper_lakefile_name=False, duplicate_require=False,
                   tamper_direct=False, conflict=False, duplicate_package=False,
                   missing_toolchain_tag=False, tamper_pin_policy=False,
                   stale_pin_policy=False):
        upstream = {}
        for dep in CONFIG["deps"]:
            manifest = upstream_manifest(["batteries", "Qq"])
            if conflict and dep["name"] == "cslib":
                manifest = upstream_manifest(["batteries", "Qq"])
                manifest["packages"][0] = dict(
                    manifest["packages"][0], rev="d" * 40)
            upstream[(dep["repo"], SHAS[(dep["repo"], "v4.36.0")])] = manifest
        client = FakeGitHub(tags={}, upstream=upstream)
        if missing_toolchain_tag:
            orig_tag_sha = client.tag_sha
            client.tag_sha = lambda slug, tag: (
                None if slug == "leanprover/lean4" else orig_tag_sha(slug, tag)
            )
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "base"
            pr = Path(tmp) / "pr"
            base.mkdir()
            pr.mkdir()
            write_tree(base, "v4.35.0")
            write_tree(pr, "v4.36.0", tamper_toolchain=tamper_toolchain,
                       tamper_transitive=tamper_transitive)
            # The guard loads the checked-in config, which carries a
            # pin_policy for check_lake_surface.py: give base/pr the real
            # file at the old pins, and the PR the file with the new
            # tag/SHAs applied (or a tampered / stale variant).
            repo_root = Path(__file__).resolve().parent.parent.parent
            real_config = load_config(repo_root)
            pin_policy = real_config["pin_policy"]
            real_policy = (repo_root / pin_policy["path"]).read_text()
            (base / "scripts").mkdir()
            (base / pin_policy["path"]).write_text(real_policy)
            shas = {d["name"]: SHAS[(d["repo"], "v4.36.0")] for d in CONFIG["deps"]}
            pr_policy = pinned_bump.apply_replacements_to_text(
                real_policy, pin_policy["replacements"], "v4.36.0", shas)
            if tamper_pin_policy:
                pr_policy = pr_policy.replace(shas["mathlib"], "0" * 40)
            if stale_pin_policy:
                pr_policy = real_policy
            (pr / "scripts").mkdir()
            (pr / pin_policy["path"]).write_text(pr_policy)
            if tamper_lakefile_name:
                lakefile = pr / "lakefile.toml"
                lakefile.write_text(
                    lakefile.read_text().replace('name = "fixture"', 'name = "other"'))
            if duplicate_require:
                lakefile = pr / "lakefile.toml"
                lakefile.write_text(
                    lakefile.read_text()
                    + '\n[[require]]\nname = "mathlib"\nrev = "v4.36.0"\n')
            if tamper_direct or duplicate_package:
                manifest_path = pr / "lake-manifest.json"
                manifest = json.loads(manifest_path.read_text())
                if tamper_direct:
                    for pkg in manifest["packages"]:
                        if pkg["name"] == "mathlib":
                            pkg["configFile"] = "evil.toml"
                if duplicate_package:
                    manifest["packages"].append(dict(manifest["packages"][0]))
                manifest_path.write_text(json.dumps(manifest, indent=1))
            changed = Path(tmp) / "changed.txt"
            changed.write_text("lean-toolchain\nlakefile.toml\nlake-manifest.json\n")
            import pinned_bump as module
            real_github = module.GitHub
            module.GitHub = lambda: client
            try:
                args = type("A", (), {
                    "base": str(base), "merge_base": str(base),
                    "pr": str(pr), "changed_files": str(changed),
                })()
                return module.cmd_guard(args)
            finally:
                module.GitHub = real_github

    def test_guard_passes_valid_bump(self):
        self.assertEqual(self._run_guard(), 0)

    def test_guard_fails_toolchain_mismatch(self):
        self.assertEqual(self._run_guard(tamper_toolchain=True), 1)

    def test_guard_fails_transitive_tamper(self):
        self.assertEqual(self._run_guard(tamper_transitive=True), 1)

    def test_guard_fails_lakefile_top_level_change(self):
        self.assertEqual(self._run_guard(tamper_lakefile_name=True), 1)

    def test_guard_fails_duplicate_require(self):
        self.assertEqual(self._run_guard(duplicate_require=True), 1)

    def test_guard_fails_direct_manifest_field_tamper(self):
        self.assertEqual(self._run_guard(tamper_direct=True), 1)

    def test_guard_fails_transitive_conflict(self):
        self.assertEqual(self._run_guard(conflict=True), 1)

    def test_guard_fails_duplicate_package(self):
        self.assertEqual(self._run_guard(duplicate_package=True), 1)

    def test_guard_fails_missing_lean_tag(self):
        self.assertEqual(self._run_guard(missing_toolchain_tag=True), 1)

    def test_guard_fails_pin_policy_tamper(self):
        self.assertEqual(self._run_guard(tamper_pin_policy=True), 1)

    def test_guard_fails_stale_pin_policy(self):
        self.assertEqual(self._run_guard(stale_pin_policy=True), 1)

    def test_replacement_sha_placeholder(self):
        out = pinned_bump.apply_replacements_to_text(
            'rev "' + "a" * 40 + '"',
            [{"pattern": '"[0-9a-f]{40}"', "replacement": '"{sha:mathlib}"'}],
            "v4.36.0", {"mathlib": "f" * 40},
        )
        self.assertIn("f" * 40, out)


class PreparedFilesTests(unittest.TestCase):
    def test_prepared_files(self):
        self.assertEqual(
            pinned_bump.prepared_files(CONFIG),
            ["README.md", "lake-manifest.json", "lakefile.toml", "lean-toolchain"],
        )
        config = dict(CONFIG, pin_policy={"path": "scripts/check_lake_surface.py"})
        self.assertIn("scripts/check_lake_surface.py", pinned_bump.prepared_files(config))

    def test_stage_and_verify_prepared(self):
        import os
        repo_root = Path(__file__).resolve().parent.parent.parent
        real_config = load_config(repo_root)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for rel in ["lean-toolchain", "lakefile.toml", "lake-manifest.json",
                        "README.md"]:
                (root / rel).write_text("placeholder\n")
            (root / "scripts").mkdir()
            (root / "scripts/check_lake_surface.py").write_text("placeholder\n")
            old_cwd = os.getcwd()
            os.chdir(root)
            try:
                args = type("A", (), {"dest": str(root / "staged")})()
                self.assertEqual(pinned_bump.cmd_stage_prepared(args), 0)
                vargs = type("A", (), {"dir": str(root / "staged")})()
                self.assertEqual(pinned_bump.cmd_verify_staged(vargs), 0)
                (root / "staged" / "evil.py").write_text("x\n")
                self.assertEqual(pinned_bump.cmd_verify_staged(vargs), 1)
                (root / "staged" / "evil.py").unlink()
                (root / "staged" / "README.md").unlink()
                self.assertEqual(pinned_bump.cmd_verify_staged(vargs), 1)
            finally:
                os.chdir(old_cwd)


class ForkPrTests(unittest.TestCase):
    def _pr(self, *, head_repo, head_ref, base_ref="main"):
        return {
            "head": {"ref": head_ref, "repo": {"full_name": head_repo}},
            "base": {"ref": base_ref},
        }

    def test_existing_bump_pr_requires_same_repo_and_main(self):
        branch = "bump-pinned/v4.36.0"
        self.assertTrue(pinned_bump._is_existing_bump_pr(
            self._pr(head_repo="example/repo", head_ref=branch),
            "example/repo", branch))
        self.assertFalse(pinned_bump._is_existing_bump_pr(
            self._pr(head_repo="fork/repo", head_ref=branch),
            "example/repo", branch))
        self.assertFalse(pinned_bump._is_existing_bump_pr(
            self._pr(head_repo="example/repo", head_ref=branch, base_ref="develop"),
            "example/repo", branch))
        self.assertFalse(pinned_bump._is_existing_bump_pr(
            self._pr(head_repo="example/repo", head_ref="bump-pinned/v4.35.0"),
            "example/repo", branch))

    def test_superseded_candidate_ignores_forks_and_current_branch(self):
        branch = "bump-pinned/v4.36.0"
        self.assertTrue(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref="bump-pinned/v4.35.0"),
            "example/repo", branch, "v4.36.0"))
        self.assertFalse(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="fork/repo", head_ref="bump-pinned/v4.35.0"),
            "example/repo", branch, "v4.36.0"))
        self.assertFalse(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref=branch),
            "example/repo", branch, "v4.36.0"))
        self.assertFalse(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref="some-feature"),
            "example/repo", branch, "v4.36.0"))

    def test_superseded_candidate_requires_strictly_older_target(self):
        branch = "bump-pinned/v4.36.0"
        # A newer open bump PR must never be closed when this run publishes
        # an older manual target.
        self.assertFalse(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref="bump-pinned/v4.37.0"),
            "example/repo", branch, "v4.36.0"))
        # An unparseable branch suffix is not a superseded target.
        self.assertFalse(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref="bump-pinned/not-a-tag"),
            "example/repo", branch, "v4.36.0"))
        # The same target on another branch is not strictly older.
        self.assertFalse(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref="bump-pinned/v4.36.0"),
            "example/repo", "bump-pinned/v4.36.0-other", "v4.36.0"))

    def test_bot_only_fails_closed_on_partial_commit_fetch(self):
        bot = [{"author": {"login": "bump-bot[bot]"}}]
        self.assertTrue(pinned_bump._pr_is_bot_only(bot, 1))
        self.assertTrue(pinned_bump._pr_is_bot_only(bot, None))
        # The PR reports more commits than were fetched: a human repair
        # commit may have been omitted, so this is not bot-only.
        self.assertFalse(pinned_bump._pr_is_bot_only(bot, 101))
        self.assertFalse(pinned_bump._pr_is_bot_only(
            bot + [{"author": {"login": "akiezun"}}], 2))
        self.assertFalse(pinned_bump._pr_is_bot_only([], None))

    def test_pr_commits_paginates(self):
        pages = {
            1: [{"author": {"login": "bump-bot[bot]"}}] * 100,
            2: [{"author": {"login": "bump-bot[bot]"}}],
            3: [],
        }

        class PagingGitHub(pinned_bump.GitHub):
            def __init__(self):
                super().__init__(repo="example/repo")
                self.paths = []

            def api(self, path):
                self.paths.append(path)
                import re as _re
                page = int(_re.search(r"[?&]page=(\d+)", path).group(1))
                return pages[page]

        client = PagingGitHub()
        self.assertEqual(len(client.pr_commits(123)), 101)
        self.assertEqual(
            client.paths,
            ["repos/example/repo/pulls/123/commits?per_page=100&page=1",
             "repos/example/repo/pulls/123/commits?per_page=100&page=2"])


class PrepareBaseTests(unittest.TestCase):
    def test_check_prepare_base(self):
        import os
        import subprocess
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.name", "t"], cwd=root, check=True)
            subprocess.run(["git", "config", "user.email", "t@t"], cwd=root, check=True)
            (root / "f").write_text("x\n")
            subprocess.run(["git", "add", "f"], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "c"], cwd=root, check=True)
            head = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=root, check=True,
                text=True, capture_output=True).stdout.strip()
            old_cwd = os.getcwd()
            old_env = os.environ.get("PREPARE_BASE_SHA")
            os.chdir(root)
            try:
                os.environ["PREPARE_BASE_SHA"] = "0" * 40
                with self.assertRaises(ValueError):
                    pinned_bump.check_prepare_base()
                os.environ["PREPARE_BASE_SHA"] = head
                pinned_bump.check_prepare_base()
                del os.environ["PREPARE_BASE_SHA"]
                pinned_bump.check_prepare_base()
            finally:
                os.chdir(old_cwd)
                if old_env is None:
                    os.environ.pop("PREPARE_BASE_SHA", None)
                else:
                    os.environ["PREPARE_BASE_SHA"] = old_env


class ConfigTests(unittest.TestCase):
    def test_checked_in_config_matches_this_repo(self):
        config = load_config(Path(__file__).resolve().parent.parent.parent)
        self.assertEqual(
            [d["name"] for d in config["deps"]],
            ["mathlib", "cslib"],
        )
        repo_root = Path(__file__).resolve().parent.parent.parent
        # The pinned set is stable; the tag itself moves with each bump,
        # so only assert it is a final release tag the repo agrees on.
        self.assertTrue(pinned_bump.is_final(current_tag(repo_root, config)))


class VersionTests(unittest.TestCase):
    def test_release_sorts_after_rc(self):
        self.assertGreater(pinned_bump.version_key("v4.36.0"),
                           pinned_bump.version_key("v4.36.0-rc2"))


if __name__ == "__main__":
    unittest.main()
