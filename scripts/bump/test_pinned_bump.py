#!/usr/bin/env python3
"""Unit tests for pinned_bump.py. No network, no git, no Lake. Run:
python3 scripts/bump/test_pinned_bump.py
"""

import hashlib
import json
import shutil
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
    def __init__(self, *, tags, run_id=123, upstream=None, module_sources=None):
        super().__init__(repo="example/repo")
        self._tags = tags
        self._run_id = run_id
        self._upstream = upstream or {}
        # (slug, path) -> source bytes, for Mathlib module files fetched
        # by the API-existence check (ref is ignored: the fixture APIs
        # are the same names at both SHAs).
        self._module_sources = module_sources or {}

    def tags(self, slug):
        return [{"name": t, "commit": {"sha": SHAS[(slug, t)]}} for t in self._tags.get(slug, [])]

    def tag_sha(self, slug, tag):
        return SHAS.get((slug, tag))

    def successful_master_build_run(self, slug, sha):
        return self._run_id

    def contents(self, slug, path, ref):
        if (slug, path) in self._module_sources:
            return self._module_sources[(slug, path)]
        return json.dumps(self._upstream[(slug, ref)]).encode()

    def open_prs(self):
        return []

    def pr_commits(self, number):
        return []

    def close_pr(self, number, comment):
        raise AssertionError("close_pr should not be called in these tests")


MODULE_SOURCES = {
    ("leanprover-community/mathlib4", "Mathlib/Foo.lean"):
        b"theorem N1 : True := trivial\n",
}


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


# --- Migration-ledger fixtures (independent of pinned_bump) ---
# Canonical hashes recomputed here from scratch, so the tests check
# pinned_bump's re-pinning rather than re-stating it.

def _canonical(value):
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _test_sha(value):
    return hashlib.sha256(_canonical(value)).hexdigest()


def _test_row_sha(row):
    return _test_sha(
        {key: value for key, value in row.items() if key != "row_content_sha256"}
    )


def _test_lane_fp(lane, triage, apis):
    lane_triage = sorted(
        ({k: v for k, v in r.items() if k != "row_content_sha256"}
         for r in triage if r["lane"] == lane),
        key=lambda r: r["ordinal"],
    )
    declarations = [
        {"ordinal": r["ordinal"], "legacy_declarations": r["legacy_declarations"]}
        for r in lane_triage
    ]
    lane_apis = sorted(
        ({k: v for k, v in r.items() if k != "row_content_sha256"}
         for r in apis if r["lane"] == lane),
        key=lambda r: r["id"],
    )
    return {
        "targets_content_sha256": _test_sha(lane_triage),
        "declarations_content_sha256": _test_sha(declarations),
        "api_rows_content_sha256": _test_sha(lane_apis),
    }


MIGRATION_BASE = "b" * 40


def migration_fixture(*, mathlib_sha, lean_tag, base=MIGRATION_BASE):
    """A minimal but hash-consistent (ledger, checks) pair at the given pins."""
    ledger = {
        "book": "AlgebraNotes",
        "base": base,
        "sources": [{"path": "v1/x", "git_blob": "0" * 40,
                     "sha256": "1" * 64, "bytes": 1}],
        "pins": {"mathlib": mathlib_sha, "lean": lean_tag},
        "destination_apis": [
            {"id": "api-1", "module": "Mathlib.Foo", "name": "N1",
             "relation": "replacement_candidate", "scope": "unverified",
             "reason": "static_shape_only", "revision": mathlib_sha},
            {"id": "api-2", "module": "MathlibExt.Foo", "name": "N2",
             "relation": "replacement_candidate", "scope": "unverified",
             "reason": "static_shape_only", "revision": base},
        ],
    }
    triage_apis = [
        {"id": "lane:api-1", "lane": "lane", "name": "N1", "kind": "named",
         "module": "Mathlib.Foo", "revision": mathlib_sha,
         "row_content_sha256": ""},
        {"id": "lane:api-2", "lane": "lane", "name": "N2", "kind": "named",
         "module": "MathlibExt.Foo", "revision": base,
         "row_content_sha256": ""},
    ]
    for api in triage_apis:
        api["row_content_sha256"] = _test_row_sha(api)
    triage = [{
        "lane": "lane", "ordinal": 0, "sourceHash": "2" * 64,
        "row_content_sha256": "",
        "legacy_declarations": [], "api_refs": ["lane:api-1", "lane:api-2"],
        "disposition": "unresolved", "scope": "unverified", "issues": [],
    }]
    triage[0]["row_content_sha256"] = _test_row_sha(triage[0])
    sources = [{"lane": "lane", "target_count": 1,
                **_test_lane_fp("lane", triage, triage_apis)}]
    checks = {
        "schema": "algebra-notes-checks/2",
        "identity_sha256": _test_sha(
            {k: ledger[k] for k in ("book", "base", "sources", "pins")}),
        "source_fidelity": "unverified",
        "migration_gate": "parent_owned_pending",
        "v1_compiler_gate": "parent_owned_pending",
        "compiler_environments": [],
        "triage_sources": sources,
        "triage_apis": triage_apis,
        "triage": triage,
        "canonical_use_tests": [],
        "pending_targets": [],
    }
    return ledger, checks


def write_migration_ledgers(root: Path, *, mathlib_sha, lean_tag):
    ledger, checks = migration_fixture(mathlib_sha=mathlib_sha, lean_tag=lean_tag)
    dest = root / "blueprint" / "migrations"
    dest.mkdir(parents=True, exist_ok=True)
    (dest / "AlgebraNotes.json").write_text(
        json.dumps(ledger, sort_keys=True, separators=(",", ":")), encoding="utf-8")
    checks_text = json.dumps(checks, sort_keys=True, separators=(",", ":"))
    # The real checks file writes its top-level identity with a space after
    # the colon (pretty top level, compact array rows); keep that shape so
    # the re-pin is exercised against the real formatting.
    checks_text = checks_text.replace(
        f'"identity_sha256":"{checks["identity_sha256"]}"',
        f'"identity_sha256": "{checks["identity_sha256"]}"', 1)
    (dest / "AlgebraNotesChecks.json").write_text(checks_text, encoding="utf-8")
    return ledger, checks


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

    def test_allow_rc_requires_explicit_rc_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_tree(root, "v4.35.0")
            client = FakeGitHub(tags={slug: ["v4.35.0", "v4.36.0"] for slug in [
                "leanprover/lean4", "leanprover-community/mathlib4",
                "leanprover/cslib"]})
            # Auto-selection with --allow-rc must not pick a final release
            # (finish would then publish it on an -rc branch).
            target, _, _ = select_target(client, root, CONFIG, allow_rc=True)
            self.assertEqual(target, "")
            # A final target with --allow-rc is not an explicit -rc target.
            with self.assertRaises(ValueError):
                select_target(client, root, CONFIG, manual="v4.36.0", allow_rc=True)

    def test_bump_branch_uses_target_syntax_not_allow_rc(self):
        self.assertEqual(pinned_bump.bump_branch("v4.36.0"), "bump-pinned/v4.36.0")
        self.assertEqual(pinned_bump.bump_branch("v4.36.0-rc1"),
                         "bump-pinned-rc/v4.36.0-rc1")


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
            write_migration_ledgers(
                root,
                mathlib_sha=SHAS[("leanprover-community/mathlib4", "v4.35.0")],
                lean_tag="leanprover/lean4:v4.35.0")
            with open(root / "README.md", "a", encoding="utf-8") as f:
                f.write("https://github.com/leanprover/lean4/releases/tag/v4.35.0\n")
            (root / "scripts").mkdir()
            policy_src = repo_root / real_config["pin_policy"]["path"]
            (root / real_config["pin_policy"]["path"]).write_text(
                policy_src.read_text())
            changed = apply_pin_edits(root, real_config, "v4.35.0", "v4.36.0", shas)
            self.assertIn("scripts/check_lake_surface.py", changed)
            self.assertIn("blueprint/migrations/AlgebraNotes.json", changed)
            ledger = json.loads(
                (root / "blueprint/migrations/AlgebraNotes.json").read_text())
            self.assertEqual(ledger["pins"]["mathlib"], shas["mathlib"])
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
                   stale_pin_policy=False, migration="absent",
                   tamper_doc=False, stale_doc=False, missing_doc=False,
                   same_pin=False, add_dep=False, add_dep_no_config=False, config_tamper=None,
                   changed_only_config=False, config_add_doc=False,
                   config_add_dep_only=False, changed_guard_only=False,
                   manifest_rev_tamper=False, remove_dep=False, changed_guard_test=False,
                   duplicate_shadow=False, config_add_ledger=False,
                   malformed_require=False, nonstring_rev=False,
                   scope_repoint=False, add_dep_wrong_source=False, add_dep_scoped=False,
                   config_add_literal_tag_rule=False, config_literal_revert=False,
                   config_scramble_rule=False, config_noncanonical_group=False,
                   delete_assertion_and_rule=False,
                   config_malformed_doc=None, config_malformed_pin=False,
                   config_add_nonmatching_doc=False, config_bad_doc_regex=False,
                   config_unresolved_sha=False, config_bad_group_ref=False,
                   config_missing_doc_file=False, config_bad_pin_regex=False):
        upstream = {}
        for dep in CONFIG["deps"]:
            manifest = upstream_manifest(["batteries", "Qq"])
            if conflict and dep["name"] == "cslib":
                manifest = upstream_manifest(["batteries", "Qq"])
                manifest["packages"][0] = dict(
                    manifest["packages"][0], rev="d" * 40)
            upstream[(dep["repo"], SHAS[(dep["repo"], "v4.36.0")])] = manifest
        if add_dep or add_dep_no_config:
            upstream[("leanprover-community/physlib",
                      SHAS[("leanprover-community/physlib", "v4.35.0")])] = \
                upstream_manifest(["batteries"])
        # Same-pin verification resolves upstream manifests at the base
        # tag, so those entries must exist too (clean: the conflict
        # fixture stays confined to the v4.36.0 entries above).
        for dep in CONFIG["deps"]:
            upstream[(dep["repo"], SHAS[(dep["repo"], "v4.35.0")])] = \
                upstream_manifest(["batteries", "Qq"])
        client = FakeGitHub(
            tags={}, upstream=upstream, module_sources=MODULE_SOURCES)
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
            repo_root = Path(__file__).resolve().parent.parent.parent
            real_config = load_config(repo_root)
            base_config_text = json.dumps(real_config, indent=2, sort_keys=True)
            pr_config = json.loads(base_config_text)
            if add_dep and not add_dep_no_config:
                pr_config["deps"].append(
                    {"name": "Physlib", "repo": "leanprover-community/physlib"})
                pr_config["pin_policy"]["replacements"].append({
                    "pattern": "(physlib\\.get\\(\"rev\"\\) != \\(\\s*\")[0-9a-f]{40}(\")",
                    "replacement": "{g1}{sha:Physlib}{g2}",
                })

            if config_add_doc:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "badge", "replacement": "badge"})
            if config_add_dep_only:
                pr_config["deps"].append(
                    {"name": "Physlib", "repo": "leanprover-community/physlib"})
            if config_add_nonmatching_doc:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "Foo", "replacement": "Bar"})
            if config_literal_revert:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "Lean-v[0-9]+\\.[0-9]+\\.[0-9]+",
                     "replacement": "Lean-v4.35.0"})
            if config_scramble_rule:
                pr_config["doc_replacements"].append(
                    {"path": "README.md",
                     "pattern": "Lean-v([0-9]+)\\.([0-9]+)\\.([0-9]+)",
                     "replacement": "Lean-v{g3}.{g2}.{g1}"})
            if config_noncanonical_group:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "(badge)",
                     "replacement": "{g01}"})
            if delete_assertion_and_rule:
                pr_config["pin_policy"]["replacements"] = [
                    r for r in pr_config["pin_policy"]["replacements"]
                    if "mathlib" not in json.dumps(r)]
            if config_add_literal_tag_rule:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "v4\\.35\\.0",
                     "replacement": "{target}"})
            if config_malformed_doc == "int":
                pr_config["doc_replacements"].append(42)
            elif config_malformed_doc == "missing_path":
                pr_config["doc_replacements"].append(
                    {"pattern": "x", "replacement": "y"})
            elif config_malformed_doc == "traversal":
                pr_config["doc_replacements"].append(
                    {"path": "../outside.md", "pattern": "x", "replacement": "y"})
            elif config_malformed_doc == "query":
                pr_config["doc_replacements"].append(
                    {"path": "README.md?ref=evil", "pattern": "x", "replacement": "y"})
            elif config_malformed_doc == "unknown_key":
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "x", "replacement": "y",
                     "note": "hi"})
            if config_malformed_pin:
                pr_config["pin_policy"]["replacements"].append({"pattern": "x"})
            if config_bad_doc_regex:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "[", "replacement": "x"})
            if config_unresolved_sha:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "badge",
                     "replacement": "{sha:Nope}"})
            if config_bad_group_ref:
                pr_config["doc_replacements"].append(
                    {"path": "README.md", "pattern": "(badge)",
                     "replacement": "{g5}"})
            if config_missing_doc_file:
                pr_config["doc_replacements"].append(
                    {"path": "MISSING.md", "pattern": "x", "replacement": "y"})
            if config_bad_pin_regex:
                pr_config["pin_policy"]["replacements"].append(
                    {"pattern": "[", "replacement": "x"})
            if config_add_ledger:
                pr_config["migration_ledgers"] = (
                    pr_config.get("migration_ledgers", [])
                    + ["blueprint/migrations/Third.json"])
            if config_tamper == "remove_dep" or remove_dep:
                pr_config["deps"] = [
                    d for d in pr_config["deps"] if d["name"] != "cslib"]
                pr_config["pin_policy"]["replacements"] = [
                    r for r in pr_config["pin_policy"]["replacements"]
                    if "cslib" not in json.dumps(r)]
            elif config_tamper == "repoint_dep":
                for d in pr_config["deps"]:
                    if d["name"] == "mathlib":
                        d["repo"] = "example/mathlib-fork"
            elif config_tamper == "remove_replacement":
                pr_config["pin_policy"]["replacements"] = \
                    pr_config["pin_policy"]["replacements"][1:]
            (base / "scripts" / "bump").mkdir(parents=True)
            (base / "scripts" / "bump" / "pinned_deps.json").write_text(base_config_text)
            (pr / "scripts" / "bump").mkdir(parents=True)
            (pr / "scripts" / "bump" / "pinned_deps.json").write_text(
                json.dumps(pr_config, indent=2, sort_keys=True))
            write_tree(base, "v4.35.0")
            write_tree(pr, "v4.35.0" if same_pin else "v4.36.0",
                       tamper_toolchain=tamper_toolchain,
                       tamper_transitive=tamper_transitive)
            if scope_repoint:
                # Mirror the real lakefile shape (fixture requires carry
                # no scope), then repoint mathlib's scope in the PR tree.
                for tree in (base, pr):
                    lakefile = tree / "lakefile.toml"
                    text = lakefile.read_text()
                    text = text.replace(
                        'name = "mathlib"\nrev = "v4.35.0"',
                        'name = "mathlib"\nscope = "leanprover-community"\nrev = "v4.35.0"')
                    text = text.replace(
                        'name = "cslib"\nrev = "v4.35.0"',
                        'name = "cslib"\nscope = "leanprover"\nrev = "v4.35.0"')
                    lakefile.write_text(text)
                lakefile = pr / "lakefile.toml"
                lakefile.write_text(lakefile.read_text().replace(
                    'scope = "leanprover-community"', 'scope = "attacker"', 1))
            if add_dep or add_dep_no_config:
                lakefile = pr / "lakefile.toml"
                if add_dep_scoped:
                    source = 'scope = "leanprover-community"\n'
                elif add_dep_wrong_source:
                    source = 'git = "https://github.com/attacker/physlib"\n'
                else:
                    source = 'git = "https://github.com/leanprover-community/physlib"\n'
                lakefile.write_text(
                    lakefile.read_text()
                    + '\n[[require]]\nname = "Physlib"\n'
                    + source + 'rev = "v4.35.0"\n'
                    '\n[[lean_lib]]\nname = "PhyslibExt"\n'
                    'globs = ["PhyslibExt.+"]\n')
                manifest_path = pr / "lake-manifest.json"
                manifest = json.loads(manifest_path.read_text())
                manifest["packages"].append({
                    "name": "Physlib", "type": "git",
                    "url": "https://github.com/leanprover-community/physlib",
                    "rev": SHAS[("leanprover-community/physlib", "v4.35.0")],
                    "inputRev": "v4.35.0", "inherited": False,
                    "configFile": "lakefile.toml",
                    "manifestFile": "lake-manifest.json",
                })
                manifest_path.write_text(json.dumps(manifest, indent=1))
            elif same_pin:
                # Same-pin library addition without a new dependency, plus
                # unrelated doc / pin-policy restructuring the guard must
                # allow (bump-only exact checks are skipped at the same pin).
                lakefile = pr / "lakefile.toml"
                lakefile.write_text(
                    lakefile.read_text()
                    + '\n[[lean_lib]]\nname = "PhyslibExt"\n'
                    'globs = ["PhyslibExt.+"]\n')
            if malformed_require:
                (pr / "lakefile.toml").write_text(
                    'name = "fixture"\n\nrequire = ["bogus"]\n')
            if nonstring_rev:
                lakefile = pr / "lakefile.toml"
                lakefile.write_text(lakefile.read_text().replace(
                    'rev = "v4.35.0"', "rev = 123", 1))
            if duplicate_shadow:
                lakefile = pr / "lakefile.toml"
                lakefile.write_text(
                    '[[require]]\nname = "mathlib"\nrev = "v9.99.99"\n\n'
                    + lakefile.read_text())
            if remove_dep:
                lakefile = pr / "lakefile.toml"
                lakefile.write_text(lakefile.read_text().replace(
                    '\n[[require]]\nname = "cslib"\nrev = "v4.35.0"', ""))
                manifest_path = pr / "lake-manifest.json"
                manifest = json.loads(manifest_path.read_text())
                manifest["packages"] = [
                    pkg for pkg in manifest["packages"] if pkg["name"] != "cslib"]
                manifest_path.write_text(json.dumps(manifest, indent=1))
            if manifest_rev_tamper:
                manifest_path = pr / "lake-manifest.json"
                manifest = json.loads(manifest_path.read_text())
                for pkg in manifest["packages"]:
                    if pkg["name"] == "mathlib":
                        pkg["rev"] = "0" * 40
                manifest_path.write_text(json.dumps(manifest, indent=1))
            # write_tree's README carries only the first two doc
            # patterns; the real config has a third (releases/tag),
            # which the real README carries. Give both trees that
            # line at the old pin, as the validate-prepared fixtures do.
            for tree in (base, pr):
                with open(tree / "README.md", "a", encoding="utf-8") as f:
                    f.write("https://github.com/leanprover/lean4/releases/tag/v4.35.0\n")
            if migration != "absent":
                write_migration_ledgers(
                    base, mathlib_sha=SHAS[("leanprover-community/mathlib4", "v4.35.0")],
                    lean_tag="leanprover/lean4:v4.35.0")
                pr_sha = (
                    SHAS[("leanprover-community/mathlib4", "v4.35.0")]
                    if migration == "stale"
                    else SHAS[("leanprover-community/mathlib4", "v4.36.0")]
                )
                pr_tag = "v4.35.0" if migration == "stale" else "v4.36.0"
                write_migration_ledgers(
                    pr, mathlib_sha=pr_sha,
                    lean_tag=f"leanprover/lean4:{pr_tag}")
                if migration == "forged":
                    # Exact re-pin of the base pair, plus a forged
                    # non-pin field: pin-consistent, but not the
                    # derived pair, so the guard must fail.
                    ledger_path = pr / "blueprint/migrations/AlgebraNotes.json"
                    ledger = json.loads(ledger_path.read_text())
                    ledger["records"] = []
                    ledger_path.write_text(
                        json.dumps(ledger, sort_keys=True,
                                   separators=(",", ":")), encoding="utf-8")
            # The guard loads the checked-in config, which carries a
            # pin_policy for check_lake_surface.py: give base/pr the real
            # file at the old pins, and the PR the file with the new
            # tag/SHAs applied (or a tampered / stale variant).
            real_config = load_config(repo_root)
            pin_policy = real_config["pin_policy"]
            real_policy = (repo_root / pin_policy["path"]).read_text()
            (base / "scripts").mkdir(exist_ok=True)
            (base / pin_policy["path"]).write_text(real_policy)
            shas = {d["name"]: SHAS[(d["repo"], "v4.36.0")] for d in CONFIG["deps"]}
            if same_pin:
                # Same-pin: the pin-policy file may be restructured
                # (e.g. a new dep's constants); the guard skips the
                # bump-only exact check, so an added comment must pass.
                (pr / "scripts").mkdir(exist_ok=True)
                (pr / pin_policy["path"]).write_text(
                    real_policy + "\n# same-pin restructuring note\n")
                if delete_assertion_and_rule:
                    policy_path = pr / pin_policy["path"]
                    policy_path.write_text("\n".join(
                        line for line in policy_path.read_text().splitlines()
                        if 'mathlib.get("rev")' not in line) + "\n")
                if add_dep:
                    # The new Physlib pin replacement must match the PR
                    # policy file, so the PR adds its assertion line.
                    policy_path = pr / pin_policy["path"]
                    policy_path.write_text(
                        policy_path.read_text()
                        + 'physlib.get("rev") != ("' + "7" * 40 + '")\n')
            else:
                pr_policy = pinned_bump.apply_replacements_to_text(
                    real_policy, pin_policy["replacements"], "v4.36.0", shas)
                if tamper_pin_policy:
                    pr_policy = pr_policy.replace(shas["mathlib"], "0" * 40)
                if stale_pin_policy:
                    pr_policy = real_policy
                (pr / "scripts").mkdir(exist_ok=True)
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
            # The valid PR README is the base README with the real
            # config's doc replacements applied for the new tag; a
            # stale README (left at the old pin) or a tampered one
            # (expected text plus an unrelated edit) must fail. At the
            # same pin, doc edits are unrestricted: an added line passes.
            if same_pin:
                with open(pr / "README.md", "a", encoding="utf-8") as f:
                    f.write("\nPhyslibExt documentation.\n")
            elif missing_doc:
                (pr / "README.md").unlink()
            elif not stale_doc:
                readme = pinned_bump.apply_replacements_to_text(
                    (pr / "README.md").read_text(),
                    real_config["doc_replacements"], "v4.36.0", shas)
                if tamper_doc:
                    readme += "\nUnrelated doc edit.\n"
                (pr / "README.md").write_text(readme)
            changed = Path(tmp) / "changed.txt"
            if changed_guard_only:
                changed_lines = ["scripts/bump/pinned_bump.py"]
                if changed_guard_test:
                    changed_lines.append("scripts/bump/test_pinned_bump.py")
            elif changed_only_config:
                changed_lines = ["scripts/bump/pinned_deps.json"]
            else:
                changed_lines = ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
                if add_dep or config_tamper is not None or config_add_doc \
                        or config_add_dep_only or remove_dep or config_add_ledger \
                        or config_malformed_doc is not None or config_malformed_pin \
                        or config_add_nonmatching_doc or config_bad_doc_regex \
                        or config_unresolved_sha or config_bad_group_ref \
                        or config_missing_doc_file or config_bad_pin_regex \
                        or config_add_literal_tag_rule or config_literal_revert \
                        or config_scramble_rule or config_noncanonical_group \
                        or delete_assertion_and_rule:
                    changed_lines.append("scripts/bump/pinned_deps.json")
                if changed_guard_test:
                    changed_lines.append("scripts/bump/test_pinned_bump.py")
            changed.write_text("\n".join(changed_lines) + "\n")
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

    def test_guard_fails_stale_migration_ledgers(self):
        self.assertEqual(self._run_guard(migration="stale"), 1)

    def test_guard_passes_repinned_migration_ledgers(self):
        self.assertEqual(self._run_guard(migration="repinned"), 0)

    def test_guard_fails_forged_ledger_records(self):
        self.assertEqual(self._run_guard(migration="forged"), 1)

    def test_guard_fails_stale_doc(self):
        self.assertEqual(self._run_guard(stale_doc=True), 1)

    def test_guard_fails_tampered_doc(self):
        self.assertEqual(self._run_guard(tamper_doc=True), 1)

    def test_guard_fails_missing_doc(self):
        self.assertEqual(self._run_guard(missing_doc=True), 1)

    def test_guard_passes_same_pin_library_addition(self):
        # A new [[lean_lib]] at the current pin, plus unrelated doc and
        # pin-policy restructuring, is not a bump and must pass.
        self.assertEqual(self._run_guard(same_pin=True), 0)

    def test_guard_passes_same_pin_dependency_addition(self):
        # #727 shape: a new dependency (Physlib) at the current pin, with
        # the config extended in the same PR, must pass.
        self.assertEqual(self._run_guard(same_pin=True, add_dep=True), 0)

    def test_guard_fails_same_pin_addition_without_config(self):
        # Same lakefile addition, but pinned_deps.json not extended: the
        # config would drift from the lakefile, so the guard must fail
        # and tell the author to extend the config in the same PR.
        self.assertEqual(
            self._run_guard(same_pin=True, add_dep_no_config=True), 1)

    def test_guard_fails_same_pin_manifest_rev_tamper(self):
        self.assertEqual(self._run_guard(same_pin=True, manifest_rev_tamper=True), 1)

    def test_guard_fails_config_repoint(self):
        self.assertEqual(self._run_guard(config_tamper="repoint_dep"), 1)

    def test_guard_fails_config_replacement_removal(self):
        self.assertEqual(self._run_guard(config_tamper="remove_replacement"), 1)

    def test_guard_fails_config_change_in_bump(self):
        # Config extension must land in a same-pin PR first, not in a bump.
        self.assertEqual(self._run_guard(add_dep=True), 1)

    def test_guard_fails_config_only_repoint(self):
        # Codex P1: a PR touching only pinned_deps.json must not sail
        # through the old pin-files-only early return.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_tamper="repoint_dep"), 1)

    def test_guard_passes_config_only_doc_addition(self):
        # A config-only PR that only adds a doc replacement is a valid
        # extension and must pass.
        self.assertEqual(
            self._run_guard(changed_only_config=True, config_add_doc=True), 0)

    def test_guard_passes_guard_code_only(self):
        # Guard-code-only PRs get normal review; they must not fail
        # their own guard run.
        self.assertEqual(self._run_guard(changed_guard_only=True), 0)

    def test_config_paths_union_and_defensive(self):
        # Union of base + PR paths; malformed entries skipped, never raised.
        # Traversal (../../evil.py) and URL-delimiter (x?ref=evil) paths
        # are excluded: they must never reach the workflow's downloads.
        base = {"doc_replacements": [{"path": "README.md", "pattern": "x", "replacement": "y"}],
                "pin_policy": {"path": "scripts/check.py", "replacements": []},
                "migration_ledgers": ["a.json", 42]}
        pr = {"doc_replacements": [{"path": "NEW.md", "pattern": "x", "replacement": "y"}, 42,
                                     {"path": "../../evil.py", "pattern": "x", "replacement": "y"},
                                     {"path": "x?ref=evil", "pattern": "x", "replacement": "y"}],
              "pin_policy": {"path": "scripts/new_check.py", "replacements": []}}
        self.assertEqual(
            pinned_bump.config_paths_for("doc", base, pr), ["README.md", "NEW.md"])
        self.assertEqual(
            pinned_bump.config_paths_for("policy", base, pr),
            ["scripts/check.py", "scripts/new_check.py"])
        self.assertEqual(
            pinned_bump.config_paths_for("ledger", base, pr), ["a.json"])

    def test_guard_fails_config_only_malformed_doc_int(self):
        # Codex P1: a bare 42 in doc_replacements must fail schema
        # validation, not merge and brick the workflow's e["path"] read.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_malformed_doc="int"), 1)

    def test_guard_fails_config_only_malformed_doc_missing_path(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_malformed_doc="missing_path"), 1)

    def test_guard_fails_config_only_malformed_doc_query(self):
        # Codex P1: a ? in a configured path would alter the download URL.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_malformed_doc="query"), 1)

    def test_guard_fails_config_only_malformed_doc_traversal(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_malformed_doc="traversal"), 1)

    def test_guard_fails_config_only_malformed_doc_unknown_key(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_malformed_doc="unknown_key"), 1)

    def test_guard_fails_config_only_nonmatching_rule(self):
        # Codex P1: a valid but nonmatching rule (the old passing Foo
        # fixture) must fail: it would brick the next bump.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_add_nonmatching_doc=True), 1)

    def test_guard_fails_config_only_bad_doc_regex(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_bad_doc_regex=True), 1)

    def test_guard_fails_config_only_unresolved_sha(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_unresolved_sha=True), 1)

    def test_guard_fails_config_only_bad_group_ref(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_bad_group_ref=True), 1)

    def test_guard_fails_config_only_missing_doc_file(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_missing_doc_file=True), 1)

    def test_guard_fails_config_only_bad_pin_regex(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_bad_pin_regex=True), 1)

    def test_guard_fails_config_only_malformed_pin_replacement(self):
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_malformed_pin=True), 1)

    def test_guard_fails_same_pin_scope_repoint(self):
        # Codex P1: changing an existing require's scope to an attacker's
        # org must fail, even with names, revs, config, manifest unchanged.
        self.assertEqual(
            self._run_guard(same_pin=True, scope_repoint=True), 1)

    def test_guard_fails_config_only_literal_revert(self):
        # Codex P1: an added rule rewriting the generic output back to
        # the literal old tag must fail (hardcoded literal in replacement).
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_literal_revert=True), 1)

    def test_guard_fails_config_only_scramble_rule(self):
        # Codex P1: an added rule matching an earlier rule's output and
        # scrambling it (no literal, every regex still matches) must fail.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_scramble_rule=True), 1)

    def test_guard_fails_config_only_noncanonical_group(self):
        # Codex P2: {g01} passes numeric validation but stays literal.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_noncanonical_group=True), 1)

    def test_guard_fails_delete_assertion_and_rule(self):
        # Codex P1: deleting the Mathlib assertion from the PR policy
        # file and removing its rule must NOT make the rule repairable;
        # eligibility comes from the trusted base tree, not PR text.
        self.assertEqual(
            self._run_guard(same_pin=True, delete_assertion_and_rule=True), 1)

    def test_guard_fails_new_dep_scoped(self):
        # Codex P2: a new dependency with scope alone (even the correct
        # org) must fail; scope does not prove the exact repository.
        self.assertEqual(
            self._run_guard(same_pin=True, add_dep=True, add_dep_scoped=True), 1)

    def test_guard_fails_config_only_literal_tag_rule(self):
        # Codex P1: a rule with a literal current-tag pattern passes
        # current-tag simulation but breaks the next forward bump, when
        # the generic rules rewrite the text first.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_add_literal_tag_rule=True), 1)

    def test_config_extension_allows_removing_forward_broken_rule(self):
        # Repair path: a rule the forward simulation shows cannot apply
        # may be removed.
        import tempfile as _tempfile
        broken = {"path": "README.md", "pattern": "v4\\.35\\.0",
                  "replacement": "{target}"}
        base = json.loads(json.dumps(CONFIG))
        base["doc_replacements"] = base.get("doc_replacements", []) + [broken]
        pr = json.loads(json.dumps(base))
        pr["doc_replacements"] = [e for e in pr["doc_replacements"] if e != broken]
        with _tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "README.md").write_text(
                'badge Lean-v4.35.0 <img alt="Lean v4.35.0" /> end\n')
            client = FakeGitHub(tags={}, upstream={})
            repairable = pinned_bump.repairable_rule_patterns(
                base, tree, "v4.35.0", client)
            self.assertIn(broken["pattern"], repairable)
            problems = pinned_bump.check_config_extension(base, pr, repairable)
            self.assertNotIn("doc_replacements", " ".join(problems))

    def test_config_extension_rejects_removing_healthy_rule(self):
        healthy = {"path": "README.md", "pattern": "badge", "replacement": "badge"}
        base = json.loads(json.dumps(CONFIG))
        base["doc_replacements"] = base.get("doc_replacements", []) + [healthy]
        pr = json.loads(json.dumps(base))
        pr["doc_replacements"] = [e for e in pr["doc_replacements"] if e != healthy]
        problems = pinned_bump.check_config_extension(base, pr, frozenset())
        self.assertTrue(any("doc_replacements" in p for p in problems))

    def test_guard_fails_new_dep_wrong_source(self):
        # Codex P1: a new require sourcing from the wrong org must fail.
        self.assertEqual(
            self._run_guard(same_pin=True, add_dep=True,
                            add_dep_wrong_source=True), 1)

    def test_guard_fails_malformed_require_entry(self):
        # Audit: a non-table [[require]] entry must fail cleanly, not crash.
        self.assertEqual(
            self._run_guard(same_pin=True, malformed_require=True), 1)

    def test_guard_fails_nonstring_rev(self):
        # Audit: a non-string rev must fail cleanly, not crash in tag math.
        self.assertEqual(
            self._run_guard(same_pin=True, nonstring_rev=True), 1)

    def test_guard_fails_same_pin_duplicate_require(self):
        # Codex P1: a shadowed mathlib entry (v9.99.99 before the real
        # v4.35.0 entry) must fail; set/dict collapse must not hide it.
        self.assertEqual(
            self._run_guard(same_pin=True, duplicate_shadow=True), 1)

    def test_guard_fails_third_migration_ledger(self):
        # Codex P2: migration_ledgers must stay unchanged; a third entry
        # would disable all subsequent automated bumps. Same-pin mode
        # isolates the ledger check (bump mode would fail earlier on the
        # config change itself).
        self.assertEqual(
            self._run_guard(same_pin=True, config_add_ledger=True), 1)

    def test_guard_fails_dependency_removal(self):
        # Codex P1: removing a dep from config, lakefile, manifest, and
        # pin-policy replacements must fail the monotone-additions policy.
        self.assertEqual(self._run_guard(same_pin=True, remove_dep=True), 1)

    def test_guard_passes_same_pin_addition_with_test_update(self):
        # Codex P1: a dep addition that also updates the test fixtures
        # must pass; the test module is not guard code.
        self.assertEqual(
            self._run_guard(same_pin=True, add_dep=True,
                            changed_guard_test=True), 0)

    def test_guard_fails_config_only_dep_without_lakefile(self):
        # A config-only dependency addition without the lakefile half
        # would drift the config from the lakefile, so it must fail.
        self.assertEqual(
            self._run_guard(changed_only_config=True,
                            config_add_dep_only=True), 1)

    def test_replacement_sha_placeholder(self):
        out = pinned_bump.apply_replacements_to_text(
            'rev "' + "a" * 40 + '"',
            [{"pattern": '"[0-9a-f]{40}"', "replacement": '"{sha:mathlib}"'}],
            "v4.36.0", {"mathlib": "f" * 40},
        )
        self.assertIn("f" * 40, out)


class PushTests(unittest.TestCase):
    def test_run_redacts_secrets_in_error(self):
        import subprocess
        import unittest.mock
        secret = "SECRET-TOKEN-123"
        fake = subprocess.CompletedProcess(
            args=["git", "push", f"https://x-access-token:{secret}@github.com/x.git"],
            returncode=1, stdout="", stderr=f"fatal: could not read from {secret}\n")
        with unittest.mock.patch.object(
                pinned_bump.subprocess, "run", return_value=fake):
            with self.assertRaises(RuntimeError) as caught:
                pinned_bump.run(["git", "push", "https://example.invalid/x.git"],
                                redact=(secret,))
        self.assertNotIn(secret, str(caught.exception))
        self.assertIn("[redacted]", str(caught.exception))

    def test_push_branch_uses_credential_helper_not_url_token(self):
        import unittest.mock
        captured = {}

        def fake_run(cmd, **kwargs):
            captured["cmd"] = cmd
            captured.update(kwargs)
            return ""

        with unittest.mock.patch.object(pinned_bump, "run", side_effect=fake_run):
            pinned_bump.push_branch("example/repo", "bump-pinned/v4.36.0",
                                    "TOKEN-ABC-123")
        argv = captured["cmd"]
        self.assertNotIn("TOKEN-ABC-123", " ".join(argv))
        self.assertNotIn("x-access-token:TOKEN", " ".join(argv))
        self.assertIn("credential.helper", " ".join(argv))
        helper = argv[argv.index("-c") + 1]
        self.assertIn("$APP_TOKEN", helper)
        self.assertIn("https://github.com/example/repo.git", argv)
        self.assertEqual(captured["env"]["APP_TOKEN"], "TOKEN-ABC-123")
        self.assertEqual(captured["redact"], ("TOKEN-ABC-123",))


class PreparedFilesTests(unittest.TestCase):
    def test_prepared_files(self):
        self.assertEqual(
            pinned_bump.prepared_files(CONFIG),
            ["README.md", "lake-manifest.json", "lakefile.toml", "lean-toolchain"],
        )
        config = dict(CONFIG, pin_policy={"path": "scripts/check_lake_surface.py"})
        self.assertIn("scripts/check_lake_surface.py", pinned_bump.prepared_files(config))
        config = dict(CONFIG, migration_ledgers=[
            "blueprint/migrations/AlgebraNotes.json",
            "blueprint/migrations/AlgebraNotesChecks.json",
        ])
        self.assertIn(
            "blueprint/migrations/AlgebraNotes.json",
            pinned_bump.prepared_files(config))
        self.assertIn(
            "blueprint/migrations/AlgebraNotesChecks.json",
            pinned_bump.prepared_files(config))

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
            migrations = root / "blueprint" / "migrations"
            migrations.mkdir(parents=True)
            (migrations / "AlgebraNotes.json").write_text("placeholder\n")
            (migrations / "AlgebraNotesChecks.json").write_text("placeholder\n")
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


class ValidatePreparedTests(unittest.TestCase):
    OLD = SHAS[("leanprover-community/mathlib4", "v4.35.0")]
    NEW = SHAS[("leanprover-community/mathlib4", "v4.36.0")]

    def _setup(self, tmp):
        repo_root = Path(__file__).resolve().parent.parent.parent
        real_config = load_config(repo_root)
        base = Path(tmp) / "base"
        prepared = Path(tmp) / "prepared"
        base.mkdir()
        write_tree(base, "v4.35.0")
        write_migration_ledgers(
            base, mathlib_sha=self.OLD, lean_tag="leanprover/lean4:v4.35.0")
        with open(base / "README.md", "a", encoding="utf-8") as f:
            f.write("https://github.com/leanprover/lean4/releases/tag/v4.35.0\n")
        (base / "scripts").mkdir()
        (base / real_config["pin_policy"]["path"]).write_text(
            (repo_root / real_config["pin_policy"]["path"]).read_text())
        shutil.copytree(base, prepared)
        shas = {d["name"]: SHAS[(d["repo"], "v4.36.0")]
                for d in real_config["deps"]}
        pinned_bump.apply_pin_edits(
            prepared, real_config, "v4.35.0", "v4.36.0", shas)
        # Simulate `lake update` in prepare: it rewrites the direct
        # manifest entries to the new rev/inputRev; apply_pin_edits
        # does not touch the manifest.
        manifest_path = prepared / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text())
        for pkg in manifest["packages"]:
            if not pkg.get("inherited"):
                pkg["rev"] = shas[pkg["name"]]
                pkg["inputRev"] = "v4.36.0"
        manifest_path.write_text(json.dumps(manifest, indent=1))
        base_files = {
            rel: (base / rel).read_text(encoding="utf-8")
            for rel in ["lake-manifest.json", "lakefile.toml", "README.md",
                        "lean-toolchain",
                        "blueprint/migrations/AlgebraNotes.json",
                        "blueprint/migrations/AlgebraNotesChecks.json",
                        real_config["pin_policy"]["path"]]
        }
        upstream = {}
        for dep in CONFIG["deps"]:
            upstream[(dep["repo"], SHAS[(dep["repo"], "v4.36.0")])] = (
                upstream_manifest(["batteries", "Qq"]))
        client = FakeGitHub(
            tags={slug: ["v4.35.0", "v4.36.0"] for slug in [
                "leanprover/lean4", "leanprover-community/mathlib4",
                "leanprover/cslib"]},
            upstream=upstream, module_sources=MODULE_SOURCES)
        return prepared, real_config, base_files, client

    def test_valid_prepared_tree_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            prepared, config, base_files, client = self._setup(tmp)
            self.assertEqual(
                pinned_bump.validate_prepared_contents(
                    client, prepared, config, "v4.36.0", allow_rc=False,
                    base_files=base_files),
                [])

    def test_pin_policy_tamper_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            prepared, config, base_files, client = self._setup(tmp)
            path = prepared / config["pin_policy"]["path"]
            shas = {d["name"]: SHAS[(d["repo"], "v4.36.0")]
                    for d in config["deps"]}
            path.write_text(path.read_text().replace(shas["mathlib"], "0" * 40))
            self.assertNotEqual(
                pinned_bump.validate_prepared_contents(
                    client, prepared, config, "v4.36.0", allow_rc=False,
                    base_files=base_files),
                [])

    def test_manifest_tamper_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            prepared, config, base_files, client = self._setup(tmp)
            path = prepared / "lake-manifest.json"
            manifest = json.loads(path.read_text())
            for pkg in manifest["packages"]:
                if pkg.get("inherited"):
                    pkg["rev"] = "d" * 40
            path.write_text(json.dumps(manifest, indent=1))
            self.assertNotEqual(
                pinned_bump.validate_prepared_contents(
                    client, prepared, config, "v4.36.0", allow_rc=False,
                    base_files=base_files),
                [])

    def test_doc_tamper_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            prepared, config, base_files, client = self._setup(tmp)
            path = prepared / "README.md"
            path.write_text(path.read_text().replace("v4.36.0", "v4.35.0"))
            self.assertNotEqual(
                pinned_bump.validate_prepared_contents(
                    client, prepared, config, "v4.36.0", allow_rc=False,
                    base_files=base_files),
                [])

    def test_stale_ledger_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            prepared, config, base_files, client = self._setup(tmp)
            write_migration_ledgers(
                prepared, mathlib_sha=self.OLD,
                lean_tag="leanprover/lean4:v4.35.0")
            self.assertNotEqual(
                pinned_bump.validate_prepared_contents(
                    client, prepared, config, "v4.36.0", allow_rc=False,
                    base_files=base_files),
                [])

    def test_forged_ledger_records_fail(self):
        # Pin-consistent (same pins/hashes) but with replaced records:
        # the exact-derived-content check must fail it.
        with tempfile.TemporaryDirectory() as tmp:
            prepared, config, base_files, client = self._setup(tmp)
            path = prepared / "blueprint/migrations/AlgebraNotes.json"
            ledger = json.loads(path.read_text())
            ledger["records"] = []
            path.write_text(json.dumps(
                ledger, sort_keys=True, separators=(",", ":")),
                encoding="utf-8")
            self.assertNotEqual(
                pinned_bump.validate_prepared_contents(
                    client, prepared, config, "v4.36.0", allow_rc=False,
                    base_files=base_files),
                [])

    def test_missing_api_at_new_pin_fails(self):
        # The re-pinned pointers advance, but Mathlib/Foo.lean at the
        # new SHA no longer declares N1: the existence check must fail.
        with tempfile.TemporaryDirectory() as tmp:
            prepared, config, base_files, client = self._setup(tmp)
            client.contents = lambda slug, path, ref: (
                b"theorem Other : True := trivial\n")
            self.assertNotEqual(
                pinned_bump.validate_prepared_contents(
                    client, prepared, config, "v4.36.0", allow_rc=False,
                    base_files=base_files),
                [])


class ValidatePreparedGitTests(unittest.TestCase):
    """cmd_validate_prepared end-to-end via git HEAD as the base tree."""

    def _repo(self, tmp, *, tamper=False):
        import os
        import subprocess
        repo_root = Path(__file__).resolve().parent.parent.parent
        real_config = load_config(repo_root)
        root = Path(tmp)
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "config", "user.name", "t"], cwd=root, check=True)
        subprocess.run(["git", "config", "user.email", "t@t"], cwd=root, check=True)
        write_tree(root, "v4.35.0")
        write_migration_ledgers(
            root, mathlib_sha=SHAS[("leanprover-community/mathlib4", "v4.35.0")],
            lean_tag="leanprover/lean4:v4.35.0")
        with open(root / "README.md", "a", encoding="utf-8") as f:
            f.write("https://github.com/leanprover/lean4/releases/tag/v4.35.0\n")
        (root / "scripts").mkdir()
        (root / real_config["pin_policy"]["path"]).write_text(
            (repo_root / real_config["pin_policy"]["path"]).read_text())
        subprocess.run(["git", "add", "-A"], cwd=root, check=True)
        subprocess.run(["git", "commit", "-qm", "base"], cwd=root, check=True)
        shas = {d["name"]: SHAS[(d["repo"], "v4.36.0")]
                for d in real_config["deps"]}
        pinned_bump.apply_pin_edits(root, real_config, "v4.35.0", "v4.36.0", shas)
        manifest_path = root / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text())
        for pkg in manifest["packages"]:
            if not pkg.get("inherited"):
                pkg["rev"] = shas[pkg["name"]]
                pkg["inputRev"] = "v4.36.0"
        manifest_path.write_text(json.dumps(manifest, indent=1))
        if tamper:
            path = root / real_config["pin_policy"]["path"]
            path.write_text(
                path.read_text().replace(shas["mathlib"], "0" * 40))
        upstream = {}
        for dep in CONFIG["deps"]:
            upstream[(dep["repo"], SHAS[(dep["repo"], "v4.36.0")])] = (
                upstream_manifest(["batteries", "Qq"]))
        client = FakeGitHub(
            tags={slug: ["v4.35.0", "v4.36.0"] for slug in [
                "leanprover/lean4", "leanprover-community/mathlib4",
                "leanprover/cslib"]},
            upstream=upstream, module_sources=MODULE_SOURCES)
        return root, client

    def test_validate_prepared_cli_passes_and_fails_tamper(self):
        import os
        for tamper, expected in [(False, 0), (True, 1)]:
            with tempfile.TemporaryDirectory() as tmp:
                root, client = self._repo(tmp, tamper=tamper)
                import pinned_bump as module
                real_github = module.GitHub
                module.GitHub = lambda: client
                old_cwd = os.getcwd()
                os.chdir(root)
                try:
                    args = type("A", (), {
                        "target": "v4.36.0", "allow_rc": False,
                    })()
                    self.assertEqual(module.cmd_validate_prepared(args), expected)
                finally:
                    os.chdir(old_cwd)
                    module.GitHub = real_github


class MergeGroupTests(unittest.TestCase):
    def test_parses_merge_group_head_ref(self):
        self.assertEqual(
            pinned_bump.parse_merge_group_head_ref(
                "gh-readonly-queue/main/pr-928-abcdef"),
            928)
        self.assertEqual(
            pinned_bump.parse_merge_group_head_ref("pr-123"), 123)

    def test_unparseable_head_ref_fails_closed(self):
        self.assertIsNone(pinned_bump.parse_merge_group_head_ref("main"))
        self.assertIsNone(pinned_bump.parse_merge_group_head_ref(
            "gh-readonly-queue/main/pr-abc"))
        self.assertIsNone(pinned_bump.parse_merge_group_head_ref(""))


class MigrationLedgerTests(unittest.TestCase):
    OLD = SHAS[("leanprover-community/mathlib4", "v4.35.0")]
    NEW = SHAS[("leanprover-community/mathlib4", "v4.36.0")]

    def _tree(self, tmp):
        root = Path(tmp)
        write_tree(root, "v4.35.0")
        write_migration_ledgers(
            root, mathlib_sha=self.OLD, lean_tag="leanprover/lean4:v4.35.0")
        return root

    def test_repin_moves_mathlib_pins_and_recomputes_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._tree(tmp)
            ledger_path = root / "blueprint/migrations/AlgebraNotes.json"
            checks_path = root / "blueprint/migrations/AlgebraNotesChecks.json"
            old_ledger_text = ledger_path.read_text()
            old_checks_text = checks_path.read_text()
            changed = pinned_bump.repin_migration_ledgers(
                root, "v4.36.0", {"mathlib": self.NEW})
            self.assertEqual(changed, [
                "blueprint/migrations/AlgebraNotes.json",
                "blueprint/migrations/AlgebraNotesChecks.json",
            ])
            ledger = json.loads(ledger_path.read_text())
            checks = json.loads(checks_path.read_text())
            self.assertEqual(ledger["pins"],
                             {"mathlib": self.NEW, "lean": "leanprover/lean4:v4.36.0"})
            self.assertEqual(
                [a["revision"] for a in ledger["destination_apis"]],
                [self.NEW, MIGRATION_BASE])
            self.assertEqual(
                [a["revision"] for a in checks["triage_apis"]],
                [self.NEW, MIGRATION_BASE])
            # Hashes recomputed independently in this test, not by pinned_bump.
            expected_ledger, expected_checks = migration_fixture(
                mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
            self.assertEqual(ledger, expected_ledger)
            self.assertEqual(checks, expected_checks)
            self.assertEqual(
                pinned_bump.check_migration_ledger_pins(
                    ledger, checks, mathlib_sha=self.NEW,
                    lean_tag="leanprover/lean4:v4.36.0"), [])
            # Formatting preserved: the new texts are the old texts with
            # exactly the intended token swaps applied.
            expected_ledger_text = old_ledger_text.replace(
                f'"mathlib":"{self.OLD}"', f'"mathlib":"{self.NEW}"').replace(
                '"lean":"leanprover/lean4:v4.35.0"',
                '"lean":"leanprover/lean4:v4.36.0"').replace(
                f'"revision":"{self.OLD}"', f'"revision":"{self.NEW}"')
            self.assertEqual(ledger_path.read_text(), expected_ledger_text)

    def test_exact_check_accepts_derived_pair(self):
        base_ledger, base_checks = migration_fixture(
            mathlib_sha=self.OLD, lean_tag="leanprover/lean4:v4.35.0")
        expected_ledger, expected_checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        self.assertEqual(
            pinned_bump.check_ledgers_match_expected(
                expected_ledger, expected_checks,
                base_ledger=base_ledger, base_checks=base_checks,
                old_mathlib=self.OLD, old_lean="leanprover/lean4:v4.35.0",
                new_mathlib=self.NEW, new_lean="leanprover/lean4:v4.36.0"),
            [])

    def test_exact_check_rejects_changed_migration_status(self):
        base_ledger, base_checks = migration_fixture(
            mathlib_sha=self.OLD, lean_tag="leanprover/lean4:v4.35.0")
        expected_ledger, expected_checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        expected_ledger = dict(expected_ledger, migration="complete")
        self.assertNotEqual(
            pinned_bump.check_ledgers_match_expected(
                expected_ledger, expected_checks,
                base_ledger=base_ledger, base_checks=base_checks,
                old_mathlib=self.OLD, old_lean="leanprover/lean4:v4.35.0",
                new_mathlib=self.NEW, new_lean="leanprover/lean4:v4.36.0"),
            [])

    def test_repin_refuses_stale_pre_bump_pair(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._tree(tmp)
            path = root / "blueprint/migrations/AlgebraNotes.json"
            ledger = json.loads(path.read_text())
            ledger["pins"]["mathlib"] = "0" * 40
            path.write_text(json.dumps(
                ledger, sort_keys=True, separators=(",", ":")), encoding="utf-8")
            with self.assertRaises(ValueError):
                pinned_bump.repin_migration_ledgers(
                    root, "v4.36.0", {"mathlib": self.NEW})

    def test_repin_refuses_unexpected_api_revision(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._tree(tmp)
            path = root / "blueprint/migrations/AlgebraNotes.json"
            ledger = json.loads(path.read_text())
            ledger["destination_apis"][0]["revision"] = "0" * 40
            path.write_text(json.dumps(
                ledger, sort_keys=True, separators=(",", ":")), encoding="utf-8")
            with self.assertRaises(ValueError):
                pinned_bump.repin_migration_ledgers(
                    root, "v4.36.0", {"mathlib": self.NEW})

    def test_repin_is_noop_when_already_at_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._tree(tmp)
            ledger_path = root / "blueprint/migrations/AlgebraNotes.json"
            before = ledger_path.read_text()
            self.assertEqual(pinned_bump.repin_migration_ledgers(
                root, "v4.35.0", {"mathlib": self.OLD}), [])
            self.assertEqual(ledger_path.read_text(), before)

    def test_apply_pin_edits_repins_ledgers(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._tree(tmp)
            config = dict(CONFIG, migration_ledgers=[
                "blueprint/migrations/AlgebraNotes.json",
                "blueprint/migrations/AlgebraNotesChecks.json",
            ])
            changed = pinned_bump.apply_pin_edits(
                root, config, "v4.35.0", "v4.36.0", {"mathlib": self.NEW})
            self.assertIn("blueprint/migrations/AlgebraNotes.json", changed)
            ledger = json.loads(
                (root / "blueprint/migrations/AlgebraNotes.json").read_text())
            self.assertEqual(ledger["pins"]["mathlib"], self.NEW)
            self.assertEqual(pinned_bump.current_tag(root, config), "v4.36.0")


class ApiExistenceTests(unittest.TestCase):
    OLD = SHAS[("leanprover-community/mathlib4", "v4.35.0")]
    NEW = SHAS[("leanprover-community/mathlib4", "v4.36.0")]

    def _client(self, sources):
        class C:
            def contents(self, slug, path, ref):
                if (slug, path) in sources:
                    return sources[(slug, path)]
                raise RuntimeError(f"not found: {slug} {path}@{ref}")
        return C()

    def test_passes_when_apis_declared(self):
        ledger, checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        client = self._client({
            ("leanprover-community/mathlib4", "Mathlib/Foo.lean"):
                b"theorem N1 : True := trivial\n",
        })
        self.assertEqual(pinned_bump.verify_apis_exist_at_pin(
            client, ledger, checks, mathlib_sha=self.NEW,
            mathlib_repo="leanprover-community/mathlib4"), [])

    def test_fails_when_api_renamed_away(self):
        ledger, checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        client = self._client({
            ("leanprover-community/mathlib4", "Mathlib/Foo.lean"):
                b"theorem Other : True := trivial\n",
        })
        problems = pinned_bump.verify_apis_exist_at_pin(
            client, ledger, checks, mathlib_sha=self.NEW,
            mathlib_repo="leanprover-community/mathlib4")
        self.assertTrue(any("N1" in p for p in problems), problems)

    def test_fails_when_api_only_in_comment(self):
        ledger, checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        client = self._client({
            ("leanprover-community/mathlib4", "Mathlib/Foo.lean"):
                b"-- theorem N1 : True := trivial\n",
        })
        problems = pinned_bump.verify_apis_exist_at_pin(
            client, ledger, checks, mathlib_sha=self.NEW,
            mathlib_repo="leanprover-community/mathlib4")
        self.assertTrue(any("N1" in p for p in problems), problems)

    def test_fails_when_api_in_wrong_namespace(self):
        ledger, checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        # The ledger wants N1 in Mathlib.Foo; a declaration of Other.N1
        # (qualified, or N1 under `namespace Other`) is not it.
        for source in (
            b"theorem Other.N1 : True := trivial\n",
            b"namespace Other\ntheorem N1 : True := trivial\nend Other\n",
        ):
            client = self._client({
                ("leanprover-community/mathlib4", "Mathlib/Foo.lean"): source,
            })
            problems = pinned_bump.verify_apis_exist_at_pin(
                client, ledger, checks, mathlib_sha=self.NEW,
                mathlib_repo="leanprover-community/mathlib4")
            self.assertTrue(any("N1" in p for p in problems), (source, problems))

    def test_passes_when_api_declared_under_matching_namespace(self):
        # Fixture API is bare "N1"; a module declaring it as N1 under no
        # namespace passes, and a qualified ledger name passes when the
        # namespace matches. Use a qualified ledger entry for the latter.
        ledger, checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        ledger["destination_apis"][0]["name"] = "Wanted.N1"
        checks["triage_apis"][0]["name"] = "Wanted.N1"
        client = self._client({
            ("leanprover-community/mathlib4", "Mathlib/Foo.lean"):
                b"namespace Wanted\ntheorem N1 : True := trivial\nend Wanted\n",
        })
        self.assertEqual(pinned_bump.verify_apis_exist_at_pin(
            client, ledger, checks, mathlib_sha=self.NEW,
            mathlib_repo="leanprover-community/mathlib4"), [])

    def test_fails_closed_when_module_fetch_fails(self):
        ledger, checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        client = self._client({})
        problems = pinned_bump.verify_apis_exist_at_pin(
            client, ledger, checks, mathlib_sha=self.NEW,
            mathlib_repo="leanprover-community/mathlib4")
        self.assertTrue(any("cannot fetch" in p for p in problems), problems)

    def test_unnamed_instance_needs_only_module_file(self):
        ledger, checks = migration_fixture(
            mathlib_sha=self.NEW, lean_tag="leanprover/lean4:v4.36.0")
        checks["triage_apis"].append({
            "id": "lane:anon", "lane": "lane", "name": None,
            "kind": "unnamed_instance", "module": "Mathlib.Bar",
            "revision": self.NEW, "row_content_sha256": "0" * 64,
        })
        client = self._client({
            ("leanprover-community/mathlib4", "Mathlib/Foo.lean"):
                b"theorem N1 : True := trivial\n",
            ("leanprover-community/mathlib4", "Mathlib/Bar.lean"):
                b"-- no named declarations here\n",
        })
        self.assertEqual(pinned_bump.verify_apis_exist_at_pin(
            client, ledger, checks, mathlib_sha=self.NEW,
            mathlib_repo="leanprover-community/mathlib4"), [])


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

    def test_superseded_candidate_ignores_non_main_base(self):
        branch = "bump-pinned/v4.36.0"
        # An older bump PR intentionally targeting a release branch must
        # never be closed when this run publishes to main.
        self.assertFalse(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref="bump-pinned/v4.35.0",
                     base_ref="release"),
            "example/repo", branch, "v4.36.0"))
        self.assertTrue(pinned_bump._is_superseded_candidate(
            self._pr(head_repo="example/repo", head_ref="bump-pinned/v4.35.0",
                     base_ref="main"),
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
        self.assertEqual(
            config.get("migration_ledgers"),
            ["blueprint/migrations/AlgebraNotes.json",
             "blueprint/migrations/AlgebraNotesChecks.json"],
        )


class VersionTests(unittest.TestCase):
    def test_release_sorts_after_rc(self):
        self.assertGreater(pinned_bump.version_key("v4.36.0"),
                           pinned_bump.version_key("v4.36.0-rc2"))


if __name__ == "__main__":
    unittest.main()
