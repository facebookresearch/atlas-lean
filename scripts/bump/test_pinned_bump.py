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
                   stale_pin_policy=False, migration="absent"):
        upstream = {}
        for dep in CONFIG["deps"]:
            manifest = upstream_manifest(["batteries", "Qq"])
            if conflict and dep["name"] == "cslib":
                manifest = upstream_manifest(["batteries", "Qq"])
                manifest["packages"][0] = dict(
                    manifest["packages"][0], rev="d" * 40)
            upstream[(dep["repo"], SHAS[(dep["repo"], "v4.36.0")])] = manifest
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
            write_tree(base, "v4.35.0")
            write_tree(pr, "v4.36.0", tamper_toolchain=tamper_toolchain,
                       tamper_transitive=tamper_transitive)
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

    def test_guard_fails_stale_migration_ledgers(self):
        self.assertEqual(self._run_guard(migration="stale"), 1)

    def test_guard_passes_repinned_migration_ledgers(self):
        self.assertEqual(self._run_guard(migration="repinned"), 0)

    def test_guard_fails_forged_ledger_records(self):
        self.assertEqual(self._run_guard(migration="forged"), 1)

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
