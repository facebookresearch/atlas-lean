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
    (root / "README.md").write_text("badge Lean-v4.35.0 end\n")
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
            self.assertIn("README.md", changed)


class GuardTests(unittest.TestCase):
    def _run_guard(self, *, tamper_toolchain=False, tamper_transitive=False):
        upstream = {}
        for dep in CONFIG["deps"]:
            upstream[(dep["repo"], SHAS[(dep["repo"], "v4.36.0")])] = upstream_manifest(
                ["batteries", "Qq"])
        client = FakeGitHub(tags={}, upstream=upstream)
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "base"
            pr = Path(tmp) / "pr"
            base.mkdir()
            pr.mkdir()
            write_tree(base, "v4.35.0")
            write_tree(pr, "v4.36.0", tamper_toolchain=tamper_toolchain,
                       tamper_transitive=tamper_transitive)
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
