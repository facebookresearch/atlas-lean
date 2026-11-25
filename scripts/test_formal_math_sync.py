#!/usr/bin/env python3
"""Offline tests for scripts/check_formal_math_sync.py and scripts/sync_formal_math.py.

    python3 -m unittest discover -s scripts -p test_formal_math_sync.py -v

Each checker test first asserts that the valid fixture passes (the positive case), then breaks one
thing and asserts the matching problem (the negative case). The sync tests build a throwaway
Formal-Math git repository; they need git but no network.
"""
from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_formal_math_sync as c  # noqa: E402
import sync_formal_math as s  # noqa: E402

BODY = "module\n\n" + "".join(f"def x{i} : Nat := {i}\n" for i in range(1, 31))
UPSTREAM = "/-\nAuthors: Adam Kiezun\n-/\n" + BODY  # formal-math's own header: replaceable
FRESH = c.META + "\n" + "".join(f"theorem fresh{i} : {i} = {i} := rfl\n" for i in range(12))  # new ATLAS-only work
NOTICE = "/-\nPortions of this file are adapted from: example (Apache 2.0).\n-/"
THIRD_PARTY = "/-\nCopyright 2026 The Formal Conjectures Authors.\n\nLicensed under the Apache License, Version 2.0.\n-/\n"
COMMIT = "a" * 40


def write(root: Path, rel: str, text: str) -> None:
    (root / rel).parent.mkdir(parents=True, exist_ok=True)
    (root / rel).write_text(text, encoding="utf-8")


def quiet(fn, *args):
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        code = fn(*args)
    return code, out.getvalue() + err.getvalue()


def make_fixture(root: Path) -> dict:
    """Write one file per disposition (plus an unlisted local file) and return the manifest."""
    for library in c.ROOTS:
        (root / library).mkdir(parents=True, exist_ok=True)
    files = {
        "MathlibExt/Identical.lean": (c.META + "\n" + BODY, {"disposition": "identical"}),
        "MathlibExt/Attributed.lean": (c.META + "\n" + NOTICE + "\n\n" + BODY,
                                       {"disposition": "attributed", "notice": NOTICE}),
        "MathlibExt/Kept.lean": (THIRD_PARTY + "\n" + BODY, {"disposition": "identical", "header": "upstream"}),
        "MathlibExtTest/Behind.lean": (c.META + BODY, {"disposition": "behind", "upstream_commit": COMMIT}),
        "CSLibExt/Diverged.lean": (c.META + "\ndef y : Nat := 2\n",
                                   {"disposition": "diverged", "rationale": "ATLAS-only fix", "backport": "pending"}),
    }
    rows = []
    for path, (text, fields) in files.items():
        write(root, path, text)
        row = {"path": path, "published_sha256": c.sha256(text), **fields}
        if fields["disposition"] in c.SYNCED:  # a kept third-party header is part of the body
            row["upstream_sha256"] = c.sha256(text if fields.get("header") == "upstream" else BODY)
        rows.append(row)
    rows.append({"path": "WantedExt/Retired.lean", "disposition": "retired"})
    write(root, "CSLibExtTest/Local.lean", c.META + "\ndef z : Nat := 3\n")  # no row: ignored
    manifest = {
        "schema_version": 1,
        "upstream": {"repository": "fairinternal/formal-math", "commit": COMMIT},
        "lean_toolchain": "leanprover/lean4:v4.35.0",
        "roots": list(c.ROOTS),
        "rows": sorted(rows, key=lambda row: row["path"]),
    }
    write(root, c.MANIFEST, c.dump_manifest(manifest))
    return manifest


class CheckerTest(unittest.TestCase):
    def setUp(self) -> None:
        self.env = mock.patch.dict(os.environ)
        self.env.start()
        os.environ.pop("GITHUB_ACTIONS", None)
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.manifest = make_fixture(self.root)

    def tearDown(self) -> None:
        self.tmp.cleanup()
        self.env.stop()

    def save(self, sort: bool = True) -> None:
        if sort:
            self.manifest["rows"].sort(key=lambda row: str(row.get("path")))
        write(self.root, c.MANIFEST, c.dump_manifest(self.manifest))

    def problems(self) -> list[str]:
        return c.check(self.root, self.root / c.MANIFEST)[0]

    def row(self, path: str) -> dict:
        return next(row for row in self.manifest["rows"] if row["path"] == path)

    def main(self, *args: str) -> tuple[int, str]:
        return quiet(c.main, ["--root", str(self.root), *args])

    def assert_clean_then(self, mutate, expected: str) -> None:
        self.assertEqual(self.problems(), [], "valid fixture must pass")
        mutate()
        found = self.problems()
        self.assertTrue(any(expected in p for p in found), f"expected {expected!r} in {found}")
        self.assertEqual(self.main()[0], 1, "preflight must block")

    def set_row(self, target: str, **fields) -> None:
        self.row(target).update(fields)
        self.save()

    # Positive cases: what the scoped check deliberately ignores.
    def test_valid_manifest_passes(self) -> None:
        code, out = self.main()
        self.assertEqual(code, 0)
        self.assertIn("ok [formal-math-sync]: 6 rows; synced files match the manifest.", out)
        self.assertIn("skipping the base-manifest comparison: not a git checkout", out)  # outside CI only

    def test_exact_copy_of_a_tracked_file_needs_a_row(self) -> None:
        def mutate() -> None:  # the source stays unchanged
            write(self.root, "WantedExt/Copy.lean", (self.root / "MathlibExt/Identical.lean").read_text())
        self.assert_clean_then(mutate, "WantedExt/Copy.lean: exact copy of tracked MathlibExt/Identical.lean")
        self.assertIn("--record-divergence WantedExt/Copy.lean", self.main()[1])
        self.assertEqual(self.main("--record-divergence", "WantedExt/Copy.lean", "--rationale", "a deliberate copy",
                                   "--backport", "not-needed")[0], 0)
        self.assertEqual(self.problems(), [])

    def test_files_without_a_row_are_ignored(self) -> None:
        write(self.root, "WantedExt/New.lean", FRESH)
        write(self.root, "CSLibExtTest/Local.lean", c.META + "\ndef z : Nat := 4\n")
        self.assertEqual(self.problems(), [])

    def test_diverged_file_edit_needs_a_refreshed_row(self) -> None:
        self.assert_clean_then(lambda: write(self.root, "CSLibExt/Diverged.lean", c.META + "\ndef y : Nat := 3\n"),
                               "diverged file changed since its rationale was recorded")
        code, out = self.main()
        self.assertIn("--record-divergence CSLibExt/Diverged.lean --rationale", out)
        self.assertEqual(self.main("--record-divergence", "CSLibExt/Diverged.lean", "--rationale", "second fix",
                                   "--backport", "pending")[0], 0)
        self.assertEqual(self.problems(), [])
        self.assertEqual(self.row_on_disk("CSLibExt/Diverged.lean")["rationale"], "second fix")

    def test_diverged_file_missing(self) -> None:
        self.assert_clean_then(lambda: os.remove(self.root / "CSLibExt/Diverged.lean"), "diverged file is missing")
        self.assertIn("--retire CSLibExt/Diverged.lean", self.main()[1])

    # Malformed manifest.
    def test_unreadable_manifest(self) -> None:
        self.assert_clean_then(lambda: write(self.root, c.MANIFEST, "{"), "cannot read manifest")

    def test_wrong_schema_version(self) -> None:
        self.assert_clean_then(lambda: (self.manifest.update(schema_version=3), self.save()),
                               "unsupported schema_version: 3")

    def test_upstream_repository_is_formal_math(self) -> None:
        for repository in ("", "someone/else"):
            with self.subTest(repository=repository):
                self.manifest["upstream"]["repository"] = repository
                self.save()
                self.assertTrue(any("must be repository 'fairinternal/formal-math'" in p for p in self.problems()))

    def test_upstream_pin_needs_full_commit(self) -> None:
        self.assert_clean_then(lambda: (self.manifest.update(upstream={"repository": "x", "commit": "abc"}), self.save()),
                               "full 40-hex commit")

    def test_unsorted_rows(self) -> None:
        def mutate() -> None:
            self.manifest["rows"].reverse()
            self.save(sort=False)
        self.assert_clean_then(mutate, "rows are not sorted by path")

    def test_duplicate_row(self) -> None:
        def mutate() -> None:
            self.manifest["rows"].append(dict(self.row("CSLibExt/Diverged.lean")))
            self.save()
        self.assert_clean_then(mutate, "duplicate row")

    def test_absolute_path(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", path=str(self.root / "CSLibExt/Diverged.lean")),
                               "absolute path")

    def test_escaping_path(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", path="CSLibExt/../../outside/X.lean"),
                               "escaping path")

    def test_path_outside_roots(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", path="PhyslibExt/X.lean"),
                               "outside the root libraries")

    def test_symlinked_path(self) -> None:
        def mutate() -> None:
            target = self.root / "MathlibExt/Identical.lean"
            os.replace(target, self.root / "elsewhere.lean")
            target.symlink_to(self.root / "elsewhere.lean")
        self.assert_clean_then(mutate, "symlinked path")

    def test_symlinked_manifest(self) -> None:
        def mutate() -> None:
            write(self.root, "provenance/other.json", json.dumps({**self.manifest, "rows": []}))
            os.remove(self.root / c.MANIFEST)
            (self.root / c.MANIFEST).symlink_to("other.json")
        self.assert_clean_then(mutate, "provenance/formal-math-sync.json: the manifest path must not go through a symlink")

    def test_unknown_disposition(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", disposition="local"), "unknown disposition")

    def test_malformed_hash_field(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", upstream_sha256="not-a-hash"),
                               "upstream_sha256 is not a SHA-256")

    # Synced rows.
    def test_synced_file_missing(self) -> None:
        self.assert_clean_then(lambda: os.remove(self.root / "MathlibExt/Identical.lean"), "identical file is missing")
        code, out = self.main()
        self.assertIn("--retire MathlibExt/Identical.lean", out)

    def test_synced_file_changed(self) -> None:
        self.assert_clean_then(lambda: write(self.root, "MathlibExtTest/Behind.lean", c.META + BODY + "\n-- edit\n"),
                               "synced file changed")
        code, out = self.main()
        self.assertIn("--record-divergence MathlibExtTest/Behind.lean --rationale", out)

    def test_header_only_violation_in_body(self) -> None:
        self.assert_clean_then(lambda: self.set_row("MathlibExt/Identical.lean", upstream_sha256=c.sha256("other")),
                               "header-only violation: body after the header")

    def test_header_only_violation_missing_meta_header(self) -> None:
        def mutate() -> None:
            write(self.root, "MathlibExtTest/Behind.lean", UPSTREAM)
            self.set_row("MathlibExtTest/Behind.lean", published_sha256=c.sha256(UPSTREAM))
        self.assert_clean_then(mutate, "does not start with the Meta header")

    def test_attributed_notice_changed(self) -> None:
        self.assert_clean_then(lambda: self.set_row("MathlibExt/Attributed.lean", notice=NOTICE.replace("example", "x")),
                               "recorded notice does not follow the Meta header")

    def notice_as(self, notice: str) -> None:
        text = c.META + "\n" + notice + "\n\n" + BODY
        write(self.root, "MathlibExt/Attributed.lean", text)
        self.set_row("MathlibExt/Attributed.lean", published_sha256=c.sha256(text), notice=notice)

    def test_code_recorded_as_notice(self) -> None:
        self.assert_clean_then(lambda: self.notice_as("def atlasOnly : Nat := 999"), "not exactly one attribution block")

    def test_code_between_notice_blocks(self) -> None:
        self.assert_clean_then(lambda: self.notice_as(NOTICE + "\ndef atlasOnly : Nat := 999\n" + NOTICE),
                               "not exactly one attribution block")

    def test_descriptive_comment_is_not_a_notice(self) -> None:
        self.assert_clean_then(lambda: self.notice_as("/-\nSinger's difference-set theorem.\n-/"),
                               "not exactly one attribution block")

    def test_kept_header_must_be_a_license(self) -> None:
        def mutate() -> None:
            text = "/-\nAuthors: Someone\n-/\n\n" + BODY
            write(self.root, "MathlibExt/Kept.lean", text)
            self.set_row("MathlibExt/Kept.lean", published_sha256=c.sha256(text))
        self.assert_clean_then(mutate, "third-party copyright and license header")

    # Retired and diverged rows.
    def test_retired_file_exists(self) -> None:
        self.assert_clean_then(lambda: write(self.root, "WantedExt/Retired.lean", c.META + BODY),
                               "retired row, but the file exists")

    def test_divergence_without_rationale(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", rationale=" "),
                               "rationale must be a non-empty string")

    def test_divergence_with_undeclared_backport_status(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", backport="pending: maybe later"),
                               "backport must be 'pending', 'not-needed', or an https:// URL")

    def test_divergence_without_backport(self) -> None:
        def mutate() -> None:
            del self.row("CSLibExt/Diverged.lean")["backport"]
            self.save()
        self.assert_clean_then(mutate, "diverged row has no backport")

    # The offline helper.
    def test_record_divergence_repairs_a_changed_file(self) -> None:
        for path in ("MathlibExt/Identical.lean", "MathlibExt/Attributed.lean"):
            write(self.root, path, c.META + BODY + "\n-- ATLAS fix\n")
        self.assertEqual(len(self.problems()), 2)
        code, _ = self.main("--record-divergence", "MathlibExt/Identical.lean", "MathlibExt/Attributed.lean",
                            "--rationale", "statement fix", "--backport", "https://github.com/x/y/pull/1")
        self.assertEqual(code, 0)
        self.assertEqual(self.problems(), [])
        row = self.row_on_disk("MathlibExt/Attributed.lean")
        self.assertEqual((row["disposition"], row["rationale"]), ("diverged", "statement fix"))
        self.assertNotIn("notice", row)

    def test_record_divergence_rejects_bad_input(self) -> None:
        before = (self.root / c.MANIFEST).read_bytes()
        for args in (["--rationale", " ", "--backport", "pending"],
                     ["--rationale", "why", "--backport", "later"]):
            with self.assertRaises(SystemExit):
                self.main("--record-divergence", "MathlibExt/Identical.lean", *args)
        os.remove(self.root / "MathlibExt/Identical.lean")
        code, out = self.main("--record-divergence", "MathlibExt/Identical.lean", "--rationale", "why", "--backport", "pending")
        self.assertEqual(code, 1)
        self.assertIn("use --retire", out)
        self.assertEqual((self.root / c.MANIFEST).read_bytes(), before)

    def test_record_divergence_can_start_tracking_a_moved_file(self) -> None:
        self.assertEqual(self.main("--record-divergence", "CSLibExtTest/Local.lean", "--rationale", "moved here",
                                   "--backport", "pending")[0], 0)
        self.assertEqual(self.row_on_disk("CSLibExtTest/Local.lean")["disposition"], "diverged")
        self.assertEqual(self.problems(), [])
        self.assertEqual(self.main("--retire", "CSLibExtTest/Missing.lean")[0], 1)  # --retire never creates rows

    def test_retire_repairs_a_deleted_file(self) -> None:
        os.remove(self.root / "MathlibExt/Kept.lean")
        self.assertNotEqual(self.problems(), [])
        self.assertEqual(self.main("--retire", "MathlibExt/Kept.lean")[0], 0)
        self.assertEqual(self.problems(), [])
        row = self.row_on_disk("MathlibExt/Kept.lean")
        self.assertEqual(row["disposition"], "retired")
        self.assertEqual(row["published_sha256"], self.row("MathlibExt/Kept.lean")["published_sha256"])  # kept

    def test_retire_rejects_an_existing_file(self) -> None:
        code, out = self.main("--retire", "MathlibExt/Kept.lean")
        self.assertEqual(code, 1)
        self.assertIn("file still exists", out)
        self.assertEqual(self.row_on_disk("MathlibExt/Kept.lean")["disposition"], "identical")

    def row_on_disk(self, path: str) -> dict:
        return next(r for r in json.loads((self.root / c.MANIFEST).read_text())["rows"] if r["path"] == path)


def run_git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@t", *args],
                          check=True, capture_output=True, text=True).stdout.strip()


class BaseGuardTest(unittest.TestCase):
    """Rows never disappear; synced rows' upstream hashes only change in a sync (a moved pin)."""

    def setUp(self) -> None:
        self.env = mock.patch.dict(os.environ)
        self.env.start()
        os.environ["GITHUB_ACTIONS"] = "true"  # CI mode, pull-request style: the base is HEAD's first parent
        os.environ.pop("GITHUB_EVENT_NAME", None)
        os.environ.pop("GITHUB_EVENT_PATH", None)
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "atlas"
        self.root.mkdir()
        run_git(self.root, "init", "-q", "-b", "main")
        write(self.root, "README.md", "atlas\n")
        self.commit("init")  # no manifest yet
        self.manifest = make_fixture(self.root)
        self.commit("base")

    def tearDown(self) -> None:
        self.tmp.cleanup()
        self.env.stop()

    def commit(self, message: str) -> None:
        run_git(self.root, "add", "-A")
        run_git(self.root, "commit", "-qm", message)

    def save(self) -> None:
        self.manifest["rows"].sort(key=lambda row: row["path"])
        write(self.root, c.MANIFEST, c.dump_manifest(self.manifest))

    def run_check(self, root: Path | None = None, *args: str) -> tuple[int, str]:
        return quiet(c.main, ["--root", str(root or self.root), *args])

    def drop_row(self, path: str) -> None:
        self.manifest["rows"] = [row for row in self.manifest["rows"] if row["path"] != path]
        self.save()

    def repin(self) -> None:
        self.manifest["upstream"]["commit"] = "b" * 40
        self.save()

    def test_unchanged_rows_pass(self) -> None:
        write(self.root, "WantedExt/New.lean", FRESH)
        self.commit("add a local file")
        self.assertEqual(self.run_check(), (0, "ok [formal-math-sync]: 6 rows; synced files match the manifest.\n"))

    def test_row_removed_fails_without_repin(self) -> None:
        self.assertEqual(self.run_check()[0], 0)
        self.drop_row("MathlibExt/Identical.lean")
        self.commit("drop a row")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Identical.lean: row removed or renamed", out)

    def test_repin_cannot_erase_rows(self) -> None:
        self.manifest["rows"] = []
        self.repin()
        self.commit("re-pin to an arbitrary commit and drop every row")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertEqual(out.count("row removed or renamed"), 6, out)

    def test_deleted_file_keeps_its_row_as_retired(self) -> None:
        os.remove(self.root / "MathlibExt/Identical.lean")
        self.assertEqual(self.run_check(None, "--retire", "MathlibExt/Identical.lean")[0], 0)
        self.commit("retire a synced file")
        self.assertEqual(self.run_check()[0], 0)

    def test_recorded_divergence_passes(self) -> None:
        write(self.root, "MathlibExt/Identical.lean", c.META + BODY + "\n-- fix\n")
        self.assertEqual(self.run_check(None, "--record-divergence", "MathlibExt/Identical.lean",
                                        "--rationale", "fix", "--backport", "pending")[0], 0)
        self.commit("record a divergence")
        self.assertEqual(self.run_check()[0], 0)

    def relabel_edit(self) -> None:
        """Edit a synced file and rewrite both hashes so it still looks upstream-identical."""
        text = c.META + "\n" + BODY + "def atlasOnly : Nat := 999\n"
        write(self.root, "MathlibExt/Identical.lean", text)
        row = next(r for r in self.manifest["rows"] if r["path"] == "MathlibExt/Identical.lean")
        row["published_sha256"], row["upstream_sha256"] = c.sha256(text), c.sha256(BODY + "def atlasOnly : Nat := 999\n")
        self.save()

    def test_upstream_hash_rewrite_fails_without_repin(self) -> None:
        self.relabel_edit()
        self.commit("relabel an edit as upstream")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Identical.lean: synced row changed (published_sha256, upstream_sha256) while the "
                      "upstream pin is unchanged", out)

    def edit_row(self, path: str, **fields) -> dict:
        row = next(r for r in self.manifest["rows"] if r["path"] == path)
        for key, value in fields.items():
            if value is None:
                row.pop(key, None)
            else:
                row[key] = value
        self.save()
        return row

    def assert_blocked(self, message: str, expected: str) -> None:
        self.assertEqual(c.check(self.root, self.root / c.MANIFEST)[0], [], "the tree alone must look valid")
        self.commit(message)
        code, out = self.run_check()
        self.assertEqual(code, 1, out)
        self.assertIn(expected, out)

    def test_attribution_cannot_be_dropped_by_relabeling(self) -> None:
        text = c.META + "\n" + BODY  # notice deleted from the file
        write(self.root, "MathlibExt/Attributed.lean", text)
        self.edit_row("MathlibExt/Attributed.lean", disposition="identical", notice=None, published_sha256=c.sha256(text))
        self.assert_blocked("drop an attribution notice", "MathlibExt/Attributed.lean: synced row changed "
                            "(disposition, notice, published_sha256)")

    def test_behind_cannot_be_relabeled_identical(self) -> None:
        self.edit_row("MathlibExtTest/Behind.lean", disposition="identical",
                      upstream_commit=None)
        self.assert_blocked("claim a behind file is current", "MathlibExtTest/Behind.lean: synced row changed "
                            "(disposition, upstream_commit)")

    def test_diverged_upstream_hash_is_frozen(self) -> None:
        self.edit_row("CSLibExt/Diverged.lean", upstream_sha256="e" * 64)
        self.assert_blocked("rewrite a diverged row's upstream hash",
                            "CSLibExt/Diverged.lean: diverged row changed upstream_sha256")

    def test_behind_divergence_keeps_its_upstream_revision(self) -> None:
        write(self.root, "MathlibExtTest/Behind.lean", c.META + BODY + "\n-- fix\n")
        self.assertEqual(self.run_check(None, "--record-divergence", "MathlibExtTest/Behind.lean",
                                        "--rationale", "fix", "--backport", "pending")[0], 0)
        row = json.loads((self.root / c.MANIFEST).read_text())["rows"]
        row = next(r for r in row if r["path"] == "MathlibExtTest/Behind.lean")
        self.assertEqual((row["upstream_commit"], row["upstream_sha256"]), (COMMIT, c.sha256(BODY)))
        self.commit("record a divergence on a behind file")
        self.assertEqual(self.run_check()[0], 0)

    def test_divergence_cannot_drop_the_upstream_revision(self) -> None:
        text = c.META + BODY + "\n-- fix\n"
        write(self.root, "MathlibExtTest/Behind.lean", text)
        self.edit_row("MathlibExtTest/Behind.lean", disposition="diverged", upstream_commit=None,
                      published_sha256=c.sha256(text), rationale="fix", backport="pending")
        self.assert_blocked("drop the upstream revision", "MathlibExtTest/Behind.lean: upstream_commit changed "
                            "when the row became diverged")

    def test_diverging_cannot_add_an_upstream_revision(self) -> None:
        text = c.META + "\n" + BODY + "\n-- fix\n"
        write(self.root, "MathlibExt/Identical.lean", text)
        self.edit_row("MathlibExt/Identical.lean", disposition="diverged", upstream_commit="d" * 40,
                      published_sha256=c.sha256(text), rationale="fix", backport="pending")
        self.assert_blocked("invent an upstream revision", "MathlibExt/Identical.lean: upstream_commit changed "
                            "when the row became diverged")

    def move_identical(self, edit: bool) -> None:
        run_git(self.root, "mv", "MathlibExt/Identical.lean", "WantedExt/Renamed.lean")
        if edit:
            with open(self.root / "WantedExt/Renamed.lean", "a") as out:
                out.write("-- moved\n")
        self.assertEqual(self.run_check(None, "--retire", "MathlibExt/Identical.lean")[0], 0)
        self.manifest = json.loads((self.root / c.MANIFEST).read_text())

    def assert_fails(self, message: str, expected: str) -> None:
        self.commit(message)
        code, out = self.run_check()
        self.assertEqual(code, 1, out)
        self.assertIn(expected, out)

    def test_pure_rename_of_a_tracked_file_needs_a_row(self) -> None:
        self.move_identical(edit=False)
        self.assert_fails("retire and rename", "WantedExt/Renamed.lean: renamed from tracked MathlibExt/Identical.lean")
        self.assertEqual(self.run_check(None, "--record-divergence", "WantedExt/Renamed.lean", "--rationale",
                                        "moved to WantedExt", "--backport", "not-needed")[0], 0)
        self.commit("track the new path")
        self.assertEqual(self.run_check()[0], 0)

    def test_rename_with_edits_of_a_tracked_file_needs_a_row(self) -> None:
        self.move_identical(edit=True)
        self.assert_fails("retire, rename and edit", "WantedExt/Renamed.lean: renamed from tracked")

    def test_near_copy_of_a_tracked_file_needs_a_row(self) -> None:
        text = (self.root / "MathlibExt/Identical.lean").read_text().replace("def x7 ", "def y7 ")
        write(self.root, "WantedExt/NearCopy.lean", text)  # the source stays unchanged
        self.assertEqual(c.check(self.root, self.root / c.MANIFEST)[0], [], "not an exact copy")
        self.commit("near copy of a synced file")
        code, out = self.run_check()
        self.assertEqual(code, 1, out)
        self.assertIn("WantedExt/NearCopy.lean: copied from tracked MathlibExt/Identical.lean", out)

    def retire_identical(self) -> str:
        text = (self.root / "MathlibExt/Identical.lean").read_text()
        os.remove(self.root / "MathlibExt/Identical.lean")
        self.assertEqual(self.run_check(None, "--retire", "MathlibExt/Identical.lean")[0], 0)
        self.commit("retire a synced file")
        self.assertEqual(self.run_check()[0], 0)
        return text

    def test_exact_copy_of_a_file_retired_earlier_needs_a_row(self) -> None:
        text = self.retire_identical()
        write(self.root, "WantedExt/Back.lean", text)
        self.assert_fails("copy it back later", "WantedExt/Back.lean: exact copy of tracked MathlibExt/Identical.lean")

    def test_near_copy_of_a_file_retired_earlier_needs_a_row(self) -> None:
        text = self.retire_identical()
        write(self.root, "WantedExt/Back.lean", text.replace("def x7 ", "def y7 ") + "-- reworded\n")
        self.assert_fails("near copy later", "WantedExt/Back.lean: near copy of retired MathlibExt/Identical.lean")

    def test_retiring_cannot_drop_provenance(self) -> None:
        os.remove(self.root / "MathlibExt/Identical.lean")
        self.edit_row("MathlibExt/Identical.lean", disposition="retired", published_sha256=None, upstream_sha256=None)
        self.assert_fails("retire and drop the fingerprint", "retiring the row changed published_sha256, upstream_sha256")

    def test_retired_fingerprint_must_match_the_base_file(self) -> None:
        os.remove(self.root / "MathlibExt/Identical.lean")
        self.assertEqual(self.run_check(None, "--retire", "MathlibExt/Identical.lean")[0], 0)
        self.manifest = json.loads((self.root / c.MANIFEST).read_text())
        self.edit_row("MathlibExt/Identical.lean", line_fingerprint=["0" * 12])
        self.assert_fails("forge the fingerprint", "line_fingerprint does not match the file at base")

    def test_retire_after_committing_the_deletion_keeps_the_fingerprint(self) -> None:
        os.remove(self.root / "MathlibExt/Identical.lean")
        self.commit("delete first")
        self.assertEqual(self.run_check(None, "--retire", "MathlibExt/Identical.lean")[0], 0)
        self.commit("then retire")
        self.assertEqual(self.run_check(None, "--base", "HEAD~2")[0], 0)

    def test_retire_with_deletion_passes(self) -> None:
        os.remove(self.root / "MathlibExt/Identical.lean")
        self.assertEqual(self.run_check(None, "--retire", "MathlibExt/Identical.lean")[0], 0)
        self.commit("delete a synced file")
        self.assertEqual(self.run_check()[0], 0)

    def test_pending_local_merge_checks_retirement_against_incoming_main(self) -> None:
        del os.environ["GITHUB_ACTIONS"]
        run_git(self.root, "branch", "topic")
        path = "CSLibExt/Diverged.lean"
        before = (self.root / path).read_text()
        after = before + "-- update published on main\n"
        write(self.root, path, after)
        self.edit_row(path, published_sha256=c.sha256(after), rationale="updated on main")
        self.commit("update the published file")
        run_git(self.root, "update-ref", "refs/remotes/origin/main", "HEAD")
        run_git(self.root, "switch", "topic")
        run_git(self.root, "merge", "--no-commit", "--no-ff", "origin/main")

        (self.root / path).unlink()
        self.edit_row(path, disposition="retired", rationale=None, backport=None,
                      line_fingerprint=c.line_fingerprint(after))
        run_git(self.root, "add", "-u")
        code, out = self.run_check()
        self.assertEqual(code, 0, out)

        self.edit_row(path, published_sha256=c.sha256(before),
                      line_fingerprint=c.line_fingerprint(before))
        moved = "CSLibExt/Moved.lean"
        write(self.root, moved, after)
        run_git(self.root, "add", c.MANIFEST, moved)
        code, out = self.run_check()
        self.assertEqual(code, 1, out)
        self.assertIn("retiring the row changed published_sha256", out)
        self.assertIn("line_fingerprint does not match the file at base", out)
        self.assertIn(f"{moved}: renamed from tracked {path}", out)

    def test_backport_link_update_passes(self) -> None:
        self.edit_row("CSLibExt/Diverged.lean", backport="https://github.com/fairinternal/formal-math/pull/1")
        self.commit("link the backport PR")
        self.assertEqual(self.run_check()[0], 0)

    def labeled_pr(self, *labels: str) -> None:
        self.event("pull_request", {"pull_request": {"labels": [{"name": name} for name in labels]}})

    def test_upstream_hash_change_passes_with_labeled_repin(self) -> None:
        self.relabel_edit()
        self.repin()
        self.commit("sync: upstream changed this file")
        self.labeled_pr("formal-math-sync")
        code, out = self.run_check()
        self.assertEqual(code, 0, out)
        self.assertIn("authorized by the 'formal-math-sync' label", out)

    def test_unlabeled_pr_cannot_repin(self) -> None:
        self.relabel_edit()
        self.repin()
        self.commit("forge an upstream relabel with an arbitrary pin")
        self.labeled_pr("statement-fix")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("without the 'formal-math-sync' label", out)
        self.assertIn("push a commit or close and reopen", out)

    def test_push_may_repin(self) -> None:
        before = run_git(self.root, "rev-parse", "HEAD")
        self.relabel_edit()
        self.repin()
        self.commit("sync pushed to main")
        self.event("push", {"before": before})
        code, out = self.run_check()
        self.assertEqual(code, 0, out)
        self.assertIn("by a push event (maintainer-only)", out)

    def test_repin_fails_closed_without_event_payload(self) -> None:
        self.relabel_edit()
        self.repin()
        self.commit("sync")
        os.environ["GITHUB_EVENT_NAME"], os.environ["GITHUB_EVENT_PATH"] = "pull_request", str(Path(self.tmp.name) / "none.json")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("cannot authorize it (event payload unreadable)", out)

    def test_local_repin_warns(self) -> None:
        self.relabel_edit()
        self.repin()
        self.commit("sync")
        del os.environ["GITHUB_ACTIONS"]
        code, out = self.run_check(None, "--base", "HEAD~1")
        self.assertEqual(code, 0, out)
        self.assertIn("allowed outside CI", out)

    def test_diverged_rehash_needs_a_new_rationale(self) -> None:
        text = c.META + "\ndef y : Nat := 3\n"
        write(self.root, "CSLibExt/Diverged.lean", text)
        row = next(r for r in self.manifest["rows"] if r["path"] == "CSLibExt/Diverged.lean")
        row["published_sha256"] = c.sha256(text)  # rehashed by hand, old rationale kept
        self.save()
        self.commit("edit a diverged file")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("CSLibExt/Diverged.lean: diverged file changed but its rationale did not", out)
        self.assertEqual(self.run_check(None, "--record-divergence", "CSLibExt/Diverged.lean",
                                        "--rationale", "second fix", "--backport", "pending")[0], 0)
        self.commit("explain it")
        self.assertEqual(self.run_check()[0], 0)

    def add_synced_row(self) -> None:
        write(self.root, "WantedExt/New.lean", c.META + BODY)
        self.manifest["rows"].append({"path": "WantedExt/New.lean", "disposition": "identical",
                                      "published_sha256": c.sha256(c.META + BODY), "upstream_sha256": c.sha256(BODY)})
        self.save()

    def test_new_synced_row_fails_without_repin(self) -> None:
        self.add_synced_row()
        self.commit("claim a new file is upstream")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("WantedExt/New.lean: new synced row while the upstream pin is unchanged", out)

    def test_new_synced_row_passes_with_labeled_repin(self) -> None:
        self.add_synced_row()
        self.repin()
        self.commit("sync: import a new upstream file")
        self.labeled_pr("formal-math-sync")
        self.assertEqual(self.run_check()[0], 0)

    def rename(self) -> None:
        os.replace(self.root / "MathlibExt/Identical.lean", self.root / "MathlibExt/Moved.lean")
        next(row for row in self.manifest["rows"] if row["path"] == "MathlibExt/Identical.lean")["path"] = \
            "MathlibExt/Moved.lean"
        self.save()

    def test_row_path_change_fails_without_repin(self) -> None:
        self.rename()
        self.commit("move a synced file")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Identical.lean: row removed or renamed", out)

    def test_row_path_change_fails_even_with_repin(self) -> None:
        self.rename()
        self.repin()
        self.commit("move a synced file in a sync")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Identical.lean: row removed or renamed", out)

    def shallow_clone(self) -> Path:
        run_git(self.root, "config", "uploadpack.allowReachableSHA1InWant", "true")
        run_git(self.root, "config", "uploadpack.allowAnySHA1InWant", "true")
        work = Path(self.tmp.name) / "ci"
        subprocess.run(["git", "clone", "-q", "--depth=1", f"file://{self.root}", str(work)],
                       check=True, capture_output=True)
        return work

    def test_shallow_ci_checkout_fetches_the_base(self) -> None:
        self.drop_row("MathlibExt/Identical.lean")
        self.commit("drop a row")
        work = self.shallow_clone()
        parent = run_git(work, "cat-file", "-p", "HEAD").split("parent ")[1].split()[0]
        self.assertNotEqual(subprocess.run(["git", "-C", str(work), "cat-file", "-e", parent]).returncode, 0)
        code, out = self.run_check(work)
        self.assertEqual(code, 1, out)
        self.assertIn("row removed or renamed", out)  # only visible if the base was fetched
        run_git(work, "cat-file", "-e", parent)

    def test_shallow_ci_checkout_passes_when_rows_are_kept(self) -> None:
        write(self.root, "WantedExt/New.lean", FRESH)
        self.commit("add a local file")
        self.assertEqual(self.run_check(self.shallow_clone())[0], 0)

    def test_fails_closed_in_ci_when_the_base_is_unreadable(self) -> None:
        work = self.shallow_clone()
        run_git(work, "remote", "set-url", "origin", f"file://{self.tmp.name}/missing")
        code, out = self.run_check(work)
        self.assertEqual(code, 1)
        self.assertIn("cannot read the base commit", out)
        del os.environ["GITHUB_ACTIONS"]  # outside CI: fall back to the origin/main merge-base
        self.assertEqual(self.run_check(work)[0], 0)

    def multi_commit_push(self) -> str:
        """Drop a row in one commit, then make an unrelated commit; return the pre-push commit."""
        before = run_git(self.root, "rev-parse", "HEAD")
        self.drop_row("MathlibExt/Identical.lean")
        self.commit("drop a row")
        write(self.root, "WantedExt/New.lean", FRESH)
        self.commit("unrelated")
        return before

    def event(self, name: str, payload: object) -> None:
        path = Path(self.tmp.name) / "event.json"
        path.write_text(json.dumps(payload) if not isinstance(payload, str) else payload)
        os.environ["GITHUB_EVENT_NAME"], os.environ["GITHUB_EVENT_PATH"] = name, str(path)

    def test_push_compares_with_the_commit_before_the_push(self) -> None:
        before = self.multi_commit_push()
        self.assertEqual(self.run_check()[0], 0)  # the tip's first parent also lacks the row
        self.event("push", {"before": before})
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Identical.lean: row removed or renamed", out)

    def test_push_of_a_new_branch_falls_back_to_the_first_parent(self) -> None:
        self.multi_commit_push()
        self.event("push", {"before": "0" * 40})
        self.assertEqual(self.run_check()[0], 0)

    def test_push_with_unreadable_event_fails_closed(self) -> None:
        self.multi_commit_push()
        self.event("push", "not json")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("cannot read the base commit (the push event's before commit", out)

    def test_merge_group_compares_with_its_base(self) -> None:
        before = self.multi_commit_push()
        self.event("merge_group", {"merge_group": {"base_sha": before}})
        self.assertIn("row removed or renamed", self.run_check()[1])

    def test_shallow_push_fetches_the_before_commit(self) -> None:
        before = self.multi_commit_push()
        work = self.shallow_clone()
        self.event("push", {"before": before})
        code, out = self.run_check(work)
        self.assertEqual(code, 1, out)
        self.assertIn("row removed or renamed", out)
        run_git(work, "cat-file", "-e", before)

    def test_symlinked_manifest_cannot_hide_the_base(self) -> None:
        write(self.root, "provenance/empty.json", json.dumps({**self.manifest, "rows": []}))
        os.remove(self.root / c.MANIFEST)
        (self.root / c.MANIFEST).symlink_to("empty.json")
        self.commit("point the manifest at an empty file")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn("must not go through a symlink", out)
        self.assertNotIn("ok [formal-math-sync]", out)

    def test_moving_the_manifest_cannot_hide_the_base(self) -> None:
        run_git(self.root, "mv", c.MANIFEST, "provenance/moved.json")
        write(self.root, "provenance/moved.json", json.dumps({**self.manifest, "rows": []}))
        self.commit("move the manifest and empty it")
        code, out = self.run_check(None, "--manifest", str(self.root / "provenance/moved.json"))
        self.assertEqual(code, 1)
        self.assertEqual(out.count("row removed or renamed"), 6, out)

    def test_post_cutover_base_without_a_manifest_fails_closed(self) -> None:
        os.remove(self.root / c.MANIFEST)
        write(self.root, c.CHECKER, "# the checker exists in this base\n")
        self.commit("a base with the checker but no manifest")
        self.manifest["rows"] = []
        self.save()
        self.commit("bring back an empty manifest")
        code, out = self.run_check()
        self.assertEqual(code, 1)
        self.assertIn(f"has {c.CHECKER} but no manifest", out)

    def test_explicit_base_must_resolve(self) -> None:
        del os.environ["GITHUB_ACTIONS"]
        code, out = self.run_check(None, "--base", "no-such-ref")
        self.assertEqual(code, 1)
        self.assertIn("cannot resolve --base no-such-ref", out)


class ShardedLedgerTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        env = mock.patch.dict(os.environ)
        env.start()
        self.addCleanup(env.stop)
        os.environ.pop("GITHUB_ACTIONS", None)
        self.root = Path(self.temp.name)
        self.manifest = self.root / c.MANIFEST
        self.legacy = make_fixture(self.root)
        retired = next(row for row in self.legacy["rows"] if row["disposition"] == "retired")
        retired["line_fingerprint"] = c.line_fingerprint(BODY)
        retired["published_sha256"] = c.sha256(c.META + BODY)
        self.manifest.write_text(c.dump_manifest(self.legacy), encoding="utf-8")
        run_git(self.root, "init", "-q")
        self.base = self.commit("legacy ledger")

    def commit(self, message: str) -> str:
        run_git(self.root, "add", "-A")
        run_git(self.root, "commit", "-qm", message)
        return run_git(self.root, "rev-parse", "HEAD")

    def convert(self) -> str:
        self.assertEqual(quiet(c.main, ["--root", str(self.root), "--split-by-domain"])[0], 0)
        return self.commit("split the ledger")

    def record(self, path: str) -> None:
        code, output = quiet(c.main, ["--root", str(self.root), "--record-divergence", path,
                                      "--rationale", "Reviewed Atlas change", "--backport", "pending"])
        self.assertEqual(code, 0, output)

    def fail_replacement(self, manifest: dict, number: int) -> None:
        original_replace = os.replace
        calls = 0

        def replace(source: Path, target: Path) -> None:
            nonlocal calls
            calls += 1
            if calls == number:
                raise OSError("simulated replacement failure")
            original_replace(source, target)

        with mock.patch.object(c.os, "replace", side_effect=replace):
            with self.assertRaisesRegex(OSError, "simulated replacement failure"):
                c.write_manifest(self.manifest, manifest)

    def test_conversion_write_failure_restores_all_originals(self) -> None:
        sharded = {**self.legacy, "schema_version": c.SHARDED_SCHEMA_VERSION}
        document_count = len(c.manifest_documents(self.manifest, sharded))
        before = self.manifest.read_bytes()
        for number in (2, document_count):
            with self.subTest(failing_write=number):
                self.fail_replacement(sharded, number)
                self.assertEqual(self.manifest.read_bytes(), before)
                self.assertEqual(c.worktree_shards(self.manifest), {})
                self.assertEqual(run_git(self.root, "status", "--porcelain"), "")
        c.write_manifest(self.manifest, sharded)
        self.assertEqual(c.load(self.manifest), (sharded, []))

    def test_sharded_write_failure_restores_existing_and_removes_new_files(self) -> None:
        self.convert()
        original, _ = c.load(self.manifest)
        before = {path: path.read_bytes()
                  for path in c.manifest_documents(self.manifest, original)}
        updated = json.loads(json.dumps(original))
        updated["lean_toolchain"] = "leanprover/lean4:v4.36.0"
        next(row for row in updated["rows"] if row["disposition"] == "diverged")["rationale"] += \
            ". A reviewed documentation update."
        new_path = "MathlibExt/Algebra/New.lean"
        updated["rows"].append({"path": new_path, "disposition": "diverged",
                                "published_sha256": c.sha256(FRESH), "rationale": "New port",
                                "backport": "pending"})
        updated["rows"].sort(key=lambda row: row["path"])
        new_file = c.shard_path(self.manifest, new_path)
        for number in (2, 3):
            with self.subTest(failing_write=number):
                self.fail_replacement(updated, number)
                self.assertEqual({path: path.read_bytes() for path in before}, before)
                self.assertFalse(new_file.exists())
        c.write_manifest(self.manifest, updated)
        self.assertEqual(c.load(self.manifest), (updated, []))

    def test_staging_failure_never_changes_the_ledger(self) -> None:
        self.convert()
        ledger, _ = c.load(self.manifest)
        before = {path: path.read_bytes() for path in c.manifest_documents(self.manifest, ledger)}
        updated = {**ledger, "lean_toolchain": "leanprover/lean4:v4.36.0"}
        original_write = Path.write_bytes

        def write_bytes(path: Path, data: bytes) -> int:
            if path.name.endswith(".old"):
                raise OSError("simulated staging failure")
            return original_write(path, data)

        with mock.patch.object(Path, "write_bytes", write_bytes):
            with self.assertRaisesRegex(OSError, "simulated staging failure"):
                c.write_manifest(self.manifest, updated)
        self.assertEqual({path: path.read_bytes() for path in before}, before)

    def test_conversion_preserves_logical_rows_and_git_history(self) -> None:
        head = self.convert()
        expected = {**self.legacy, "schema_version": c.SHARDED_SCHEMA_VERSION}
        self.assertEqual(c.load(self.manifest), (expected, []))
        self.assertEqual(c.load_revision(self.root, self.base), (self.legacy, []))
        self.assertEqual(c.load_revision(self.root, head), (expected, []))
        self.assertNotIn("rows", json.loads(self.manifest.read_text(encoding="utf-8")))
        shard = c.shard_directory(self.manifest) / "MathlibExt.json"
        self.assertEqual(c.shard_path(self.manifest, "MathlibExt/Identical.lean"), shard)
        self.assertEqual(c.base_problems(self.root, self.manifest, self.base), ([], []))
        self.assertEqual(quiet(c.main, ["--root", str(self.root), "--split-by-domain"])[0], 0)
        self.assertEqual(run_git(self.root, "status", "--porcelain"), "")

    def test_disjoint_domain_prs_git_merge_without_shared_changes(self) -> None:
        sharded = self.convert()
        first = "MathlibExt/Algebra/Fresh.lean"
        second = "MathlibExt/Topology/Fresh.lean"
        run_git(self.root, "switch", "-qc", "algebra")
        write(self.root, first, FRESH)
        self.record(first)
        left = self.commit("record algebra source")
        run_git(self.root, "switch", "-qc", "topology", sharded)
        write(self.root, second, FRESH.replace("fresh", "topology"))
        self.record(second)
        right = self.commit("record topology source")
        for revision, lean_path in ((left, first), (right, second)):
            shard = c.shard_path(Path(c.MANIFEST), lean_path).as_posix()
            self.assertEqual(set(run_git(self.root, "diff", "--name-only", sharded, revision).splitlines()),
                             {lean_path, shard})
        run_git(self.root, "merge", "--no-edit", "algebra")
        self.assertEqual(c.check(self.root, self.manifest)[0], [])
        self.assertEqual(c.base_problems(self.root, self.manifest, sharded), ([], []))

    def test_cutover_cannot_drop_retired_rows_or_repin(self) -> None:
        self.convert()
        manifest, _ = c.load(self.manifest)
        self.assertIsNotNone(manifest)
        tombstones = c.shard_path(self.manifest, "WantedExt/Retired.lean")
        tombstones.unlink()
        self.assertIn("preserve every existing row", c.base_problems(self.root, self.manifest, self.base)[0][0])
        c.write_manifest(self.manifest, manifest)
        changed = {**manifest, "upstream": {**manifest["upstream"], "commit": "b" * 40}}
        c.write_manifest(self.manifest, changed)
        self.assertIn("all shared metadata", c.base_problems(self.root, self.manifest, self.base)[0][0])

    def test_existing_shard_cannot_disappear_or_revert_layout(self) -> None:
        sharded = self.convert()
        tombstones = c.shard_path(self.manifest, "WantedExt/Retired.lean")
        tombstones.unlink()
        self.assertIn("WantedExt/Retired.lean: row removed", c.base_problems(self.root, self.manifest, sharded)[0][0])
        for path in c.worktree_shards(self.manifest):
            path.unlink()
        c.write_manifest(self.manifest, self.legacy)
        self.assertIn("cannot return to the monolithic layout", c.base_problems(self.root, self.manifest, sharded)[0][0])

    def test_cross_domain_misplacement_and_symlinks_are_rejected(self) -> None:
        self.convert()
        original = c.shard_path(self.manifest, "MathlibExt/Identical.lean")
        misplaced = c.shard_path(self.manifest, "MathlibExt/Algebra/Ghost.lean")
        misplaced.parent.mkdir(parents=True)
        misplaced.write_bytes(original.read_bytes())
        self.assertIn("row belongs in another shard", c.load(self.manifest)[1][0])
        misplaced.unlink()
        misplaced.symlink_to(original)
        self.assertIn("must not go through a symlink", c.load(self.manifest)[1][0])
        invalid = self.commit("symlink shard fixture")
        self.assertIn("expected a regular manifest file", c.load_revision(self.root, invalid)[1][0])

    def test_copy_protection_spans_shards(self) -> None:
        self.convert()
        target = self.root / "MathlibExt/Topology/Copied.lean"
        target.parent.mkdir()
        target.write_bytes((self.root / "MathlibExt/Identical.lean").read_bytes())
        self.assertTrue(any("exact copy of tracked" in problem for problem in c.check(self.root, self.manifest)[0]))


class SyncTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        base = Path(self.tmp.name)
        self.fm, self.atlas = base / "formal-math", base / "atlas"
        self.fm.mkdir()
        run_git(self.fm, "init", "-q")
        for name in ("Same", "Old", "Gone", "Edited"):
            write(self.fm, f"MathlibExt/{name}.lean", UPSTREAM)
        run_git(self.fm, "add", "-A")
        run_git(self.fm, "commit", "-qm", "one")
        self.first = run_git(self.fm, "rev-parse", "HEAD")
        write(self.fm, "MathlibExt/Old.lean", UPSTREAM + "\ndef later : Nat := 5\n")
        os.remove(self.fm / "MathlibExt/Gone.lean")
        run_git(self.fm, "add", "-A")
        run_git(self.fm, "commit", "-qm", "two")
        self.commit = run_git(self.fm, "rev-parse", "HEAD")
        for library in c.ROOTS:
            (self.atlas / library).mkdir(parents=True)
        write(self.atlas, "lean-toolchain", "leanprover/lean4:v4.35.0\n")
        for name in ("Same", "Old", "Gone"):
            write(self.atlas, f"MathlibExt/{name}.lean", c.META + "\n" + BODY)
        write(self.atlas, "MathlibExt/Edited.lean", c.META + "\n" + BODY + "\ndef fix : Nat := 6\n")
        write(self.atlas, "WantedExt/Mine.lean", c.META + "\ndef mine : Nat := 7\n")
        write(self.atlas, "MathlibExt/Flt.lean", "/-\nCopyright (c) 2026 Anthropic, PBC. All rights reserved.\n"
                                                 "Released under Apache 2.0 license.\n-/\n" + BODY)
        self.rationales = self.atlas.parent / "rationales.json"
        self.rationales.write_text(json.dumps({p: {"rationale": "reviewed", "backport": "pending"}
                                               for p in ("MathlibExt/Edited.lean", "MathlibExt/Gone.lean")}))

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def sync(self, *extra: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = s.main(["--formal-math", str(self.fm), "--commit", "HEAD", "--atlas", str(self.atlas), *extra])
        return code, out.getvalue(), err.getvalue()

    def rows(self) -> dict[str, dict]:
        return {row["path"]: row for row in json.loads((self.atlas / c.MANIFEST).read_text())["rows"]}

    def test_sync_report_failure_leaves_ledger_unchanged(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        path = self.atlas / c.MANIFEST
        self.assertEqual(quiet(c.main, ["--root", str(self.atlas), "--split-by-domain"])[0], 0)
        ledger, _ = c.load(path)
        original = c.manifest_documents(path, ledger)
        write(self.atlas, "lean-toolchain", "leanprover/lean4:v4.36.0\n")
        code, _, error = self.sync("--report", str(self.atlas), "--rationales", str(self.rationales))
        self.assertEqual(code, 1)
        self.assertIn("ledger not written", error)
        self.assertEqual({target: target.read_text(encoding="utf-8") for target in original}, original)
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        updated, _ = c.load(path)
        self.assertEqual(updated["lean_toolchain"], "leanprover/lean4:v4.36.0")

    def test_sync_report_cannot_overwrite_ledger(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        path = self.atlas / c.MANIFEST
        self.assertEqual(quiet(c.main, ["--root", str(self.atlas), "--split-by-domain"])[0], 0)
        old, _ = c.load(path)
        documents = c.manifest_documents(path, old)
        shard = c.shard_path(path, "MathlibExt/Same.lean")
        alias = path.parent / "report-alias.md"
        os.link(shard, alias)
        for target in (path, shard, alias):
            with self.subTest(target=target), self.assertRaises(SystemExit):
                self.sync("--report", str(target))
            self.assertEqual({t: t.read_text(encoding="utf-8") for t in documents}, documents)

    def test_sync_refuses_missing_committed_retirement_shard(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        path = self.atlas / c.MANIFEST
        manifest, _ = c.load(path)
        retired = "WantedExt/Combinatorics/Retired.lean"
        manifest["rows"].append({"path": retired, "disposition": "retired"})
        manifest["rows"].sort(key=lambda row: row["path"])
        manifest["schema_version"] = c.SHARDED_SCHEMA_VERSION
        c.write_manifest(path, manifest)
        run_git(self.atlas, "init", "-q")
        run_git(self.atlas, "add", "-A")
        run_git(self.atlas, "commit", "-qm", "sharded ledger with a retirement")
        c.shard_path(path, retired).unlink()
        header = path.read_bytes()
        with self.assertRaisesRegex(SystemExit, retired):
            self.sync("--rationales", str(self.rationales))
        self.assertEqual(path.read_bytes(), header)

    def test_sync_refuses_malformed_legacy_rows(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        path = self.atlas / c.MANIFEST
        manifest, _ = c.load(path)
        manifest["rows"].insert(0, manifest["rows"][0])
        text = c.dump_manifest(manifest)
        path.write_text(text, encoding="utf-8")
        with self.assertRaisesRegex(SystemExit, "sorted and unique"):
            self.sync("--rationales", str(self.rationales))
        self.assertEqual(path.read_text(encoding="utf-8"), text)

    def test_sync_preserves_sharded_layout_and_defers_failed_writes(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        path = self.atlas / c.MANIFEST
        self.assertEqual(quiet(c.main, ["--root", str(self.atlas), "--split-by-domain"])[0], 0)
        old, problems = c.load(path)
        self.assertEqual(problems, [])
        docs = {target: target.read_bytes() for target in c.manifest_documents(path, old)}
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        self.assertEqual({target: target.read_bytes() for target in docs}, docs)
        write(self.atlas, "MathlibExt/Same.lean", c.META + BODY + "\ndef changed : Nat := 9\n")
        report_path = self.atlas.parent / "failed-report.md"
        self.assertEqual(self.sync("--report", str(report_path))[0], 1)
        self.assertFalse(report_path.exists())
        self.assertEqual({target: target.read_bytes() for target in docs}, docs)

    def test_fails_closed_then_classifies_and_verifies(self) -> None:
        report_path = self.atlas.parent / "report.md"
        code, _, err = self.sync("--report", str(report_path))
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Edited.lean", err)
        self.assertIn("MathlibExt/Gone.lean", err)  # deleted upstream, still published: needs a reason
        self.assertFalse((self.atlas / c.MANIFEST).exists(), "fail-closed run must not write the manifest")
        self.assertFalse(report_path.exists(), "fail-closed run must not write the report")

        for bad in ({"rationale": " ", "backport": "pending"}, {"rationale": "fix", "backport": ["pending"]},
                    {"rationale": "fix"}, {"rationale": "fix", "backport": "pending: later"}):
            bad_file = self.atlas.parent / "bad.json"
            bad_file.write_text(json.dumps({"MathlibExt/Edited.lean": bad, "MathlibExt/Gone.lean": bad}))
            self.assertEqual(self.sync("--rationales", str(bad_file))[0], 1, bad)
            self.assertFalse((self.atlas / c.MANIFEST).exists(), bad)

        code, report, _ = self.sync("--rationales", str(self.rationales))
        self.assertEqual(code, 0)
        manifest = json.loads((self.atlas / c.MANIFEST).read_text())
        self.assertEqual(set(manifest), {"schema_version", "upstream", "lean_toolchain", "roots", "rows"})
        got = {path: row["disposition"] for path, row in self.rows().items()}
        self.assertEqual(got, {"MathlibExt/Same.lean": "identical", "MathlibExt/Old.lean": "behind",
                               "MathlibExt/Gone.lean": "diverged", "MathlibExt/Edited.lean": "diverged"})
        self.assertEqual(manifest["upstream"]["commit"], self.commit)
        self.assertEqual(self.rows()["MathlibExt/Old.lean"]["upstream_commit"], self.first)
        self.assertIn("| local (no row) | 2 |", report)
        self.assertEqual(c.check(self.atlas, self.atlas / c.MANIFEST)[0], [])

        # Deterministic, and a second run keeps the recorded rationale without --rationales.
        first_bytes = (self.atlas / c.MANIFEST).read_bytes()
        code, report, _ = self.sync()
        self.assertEqual(code, 0)
        self.assertEqual((self.atlas / c.MANIFEST).read_bytes(), first_bytes)
        self.assertIn("## Changed (0)", report)

        # A diverged file that changes again needs a fresh explanation.
        write(self.atlas, "MathlibExt/Edited.lean", c.META + "\n" + BODY + "\ndef fix : Nat := 9\n")
        code, _, err = self.sync()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Edited.lean", err)
        self.assertNotIn("MathlibExt/Gone.lean", err, "an unchanged divergence keeps its explanation")
        self.assertEqual((self.atlas / c.MANIFEST).read_bytes(), first_bytes, "rejected sync must not write")

    def test_third_party_headers_must_be_kept(self) -> None:
        third_party = {"Replaced": c.META + "\n" + BODY,                  # header swapped for Meta
                       "Kept": THIRD_PARTY + "\n" + BODY,                 # byte for byte
                       "Prefixed": c.META + "\n" + THIRD_PARTY + "\n" + BODY}  # Meta header added
        for name in third_party:
            write(self.fm, f"MathlibExt/{name}.lean", THIRD_PARTY + "\n" + BODY)
        run_git(self.fm, "add", "-A")
        run_git(self.fm, "commit", "-qm", "third-party files")
        for name, text in third_party.items():
            write(self.atlas, f"MathlibExt/{name}.lean", text)
        code, _, err = self.sync("--rationales", str(self.rationales))
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Replaced.lean", err)  # only a recorded divergence may drop the header
        self.assertNotIn("MathlibExt/Kept.lean", err)
        self.assertNotIn("MathlibExt/Prefixed.lean", err)
        rationales = json.loads(self.rationales.read_text())
        rationales["MathlibExt/Replaced.lean"] = {"rationale": "header replaced", "backport": "not-needed"}
        self.rationales.write_text(json.dumps(rationales))
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        rows = self.rows()
        self.assertEqual(rows["MathlibExt/Replaced.lean"]["disposition"], "diverged")
        self.assertEqual((rows["MathlibExt/Kept.lean"]["disposition"], rows["MathlibExt/Kept.lean"]["header"]),
                         ("identical", "upstream"))
        self.assertEqual(rows["MathlibExt/Prefixed.lean"]["disposition"], "identical")
        self.assertNotIn("header", rows["MathlibExt/Prefixed.lean"])
        self.assertEqual(c.check(self.atlas, self.atlas / c.MANIFEST)[0], [])

    def test_formal_math_headers_may_be_replaced(self) -> None:
        own = "/-\nCopyright (c) 2026 Adam Kiezun. All rights reserved.\nReleased under Apache 2.0 license.\n-/\n"
        write(self.fm, "MathlibExt/Own.lean", own + BODY)
        run_git(self.fm, "add", "-A")
        run_git(self.fm, "commit", "-qm", "own header")
        write(self.atlas, "MathlibExt/Own.lean", c.META + "\n" + BODY)
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        self.assertEqual(self.rows()["MathlibExt/Own.lean"]["disposition"], "identical")

    def test_authors_blocks(self) -> None:
        cases = {"Authors: Adam Kiezun, Muse Spark 1.3": True,     # allowlisted: formal-math's own
                 "Author: @vonbo, Avocado": True,
                 "Authors: Codex Vale-62b0 (canonical root support)": True,
                 "Authors: Jane Doe": False,                       # third-party
                 "Authors: Adam Kiezun, Jane Doe": False,          # mixed counts as third-party
                 "Author(s): Jane Doe": False,
                 "Authors: Adam Kiezun (with Jane Doe)": False,     # a parenthetical cannot hide a name
                 "Authors: Muse Code powered by Meta Muse Spark (Muse Spark 1.3)": True}
        for line, own in cases.items():
            with self.subTest(line=line):
                self.assertEqual(c.is_formal_math_header(f"/-\n{line}\n-/"), own)
        third = "/-\nAuthors: Jane Doe\n-/\n"
        write(self.fm, "MathlibExt/Theirs.lean", third + BODY)
        write(self.fm, "MathlibExt/Kept2.lean", third + BODY)
        run_git(self.fm, "add", "-A")
        run_git(self.fm, "commit", "-qm", "third-party authors")
        write(self.atlas, "MathlibExt/Theirs.lean", c.META + "\n" + BODY)          # Authors block replaced
        write(self.atlas, "MathlibExt/Kept2.lean", c.META + "\n" + third + BODY)   # Authors block kept
        rationales = json.loads(self.rationales.read_text())
        rationales["MathlibExt/Theirs.lean"] = {"rationale": "Meta header in place of the Authors block",
                                                "backport": "not-needed"}
        self.rationales.write_text(json.dumps(rationales))
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        rows = self.rows()
        self.assertEqual(rows["MathlibExt/Theirs.lean"]["disposition"], "diverged")
        self.assertEqual(rows["MathlibExt/Kept2.lean"]["disposition"], "identical")
        self.assertEqual(rows["MathlibExt/Same.lean"]["disposition"], "identical")  # allowlisted block stripped

    def test_formal_math_holder_names_match_exactly(self) -> None:
        cases = {"Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.": True,
                 "Copyright (c) Meta Platforms, Inc. and affiliates.": True,
                 "Copyright 2026 Meta Platforms, Inc. and affiliates and Jane Doe.": False,
                 "Copyright (c) 2026 Adam Kiezun and Jane Doe. All rights reserved.": False,
                 "Copyright (c) 2026. All rights reserved.": False,
                 "Copyright (c) 2026\nAuthors: Jane Doe": False,
                 "Copyright (c) 2026 Adam Kiezun. All rights reserved.\nAuthor(s): Jane Doe": False}
        for line, own in cases.items():
            with self.subTest(line=line):
                self.assertEqual(c.is_formal_math_header(f"/-\n{line}\nReleased under Apache 2.0 license.\n-/"), own)

    def test_report_lists_every_field_change(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        manifest = json.loads((self.atlas / c.MANIFEST).read_text())
        for row in manifest["rows"]:
            if row["path"] == "MathlibExt/Old.lean":
                row["upstream_commit"] = "c" * 40  # stale: the sync recomputes it
        write(self.atlas, c.MANIFEST, c.dump_manifest(manifest))
        rationales = json.loads(self.rationales.read_text())
        rationales["MathlibExt/Gone.lean"]["rationale"] = "a better reason"
        self.rationales.write_text(json.dumps(rationales))
        code, report, _ = self.sync("--rationales", str(self.rationales))
        self.assertEqual(code, 0)
        self.assertIn("## Changed (2)", report)
        self.assertIn("- `MathlibExt/Old.lean`: behind -> behind", report)
        self.assertIn("- `MathlibExt/Gone.lean`: diverged -> diverged", report)

    def test_same_pin_sync_keeps_a_recorded_divergence(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        write(self.atlas, "MathlibExt/Old.lean", c.META + "\n" + BODY + "\n-- fix\n")  # was behind
        quiet(c.main, ["--root", str(self.atlas), "--record-divergence", "MathlibExt/Old.lean",
                       "--rationale", "fix", "--backport", "pending"])
        recorded = self.rows()["MathlibExt/Old.lean"]
        self.assertEqual(recorded["upstream_commit"], self.first)
        self.assertEqual(self.sync()[0], 0)  # no fresh rationale needed at the same pin
        self.assertEqual(self.rows()["MathlibExt/Old.lean"], recorded)

    def test_rows_never_disappear(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        os.remove(self.atlas / "MathlibExt/Same.lean")  # deleted without --retire: the sync retires it
        self.assertEqual(self.sync()[0], 0)
        retired = self.rows()["MathlibExt/Same.lean"]
        self.assertEqual((retired["disposition"], retired["published_sha256"]),
                         ("retired", c.sha256(c.META + "\n" + BODY)))
        self.assertEqual(self.sync()[0], 0)  # and keeps it retired
        retired = self.rows()["MathlibExt/Same.lean"]
        self.assertEqual((retired["disposition"], retired["published_sha256"]),
                         ("retired", c.sha256(c.META + "\n" + BODY)))
        self.assertEqual(self.rows()["MathlibExt/Same.lean"]["disposition"], "retired")
        write(self.atlas, "MathlibExt/Same.lean", c.META + "\n" + BODY)  # restored: synced again
        self.assertEqual(self.sync()[0], 0)
        self.assertEqual(self.rows()["MathlibExt/Same.lean"]["disposition"], "identical")
        write(self.atlas, "MathlibExt/Same.lean", "/-\nCopyright (c) 2026 Anthropic, PBC.\nApache license.\n-/\n" + BODY)
        with self.assertRaises(SystemExit) as raised:  # would turn local and drop its row
            self.sync()
        self.assertIn("MathlibExt/Same.lean", str(raised.exception))

    def test_ignores_git_replace_refs(self) -> None:
        run_git(self.fm, "replace", self.commit, self.first)  # make HEAD read as the first commit
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        self.assertEqual(json.loads((self.atlas / c.MANIFEST).read_text())["upstream"]["commit"], self.commit)
        self.assertEqual(self.rows()["MathlibExt/Old.lean"]["disposition"], "behind")
        self.assertEqual(self.rows()["MathlibExt/Gone.lean"]["disposition"], "diverged")

    def clone(self, name: str, *flags: str) -> None:
        run_git(self.fm, "config", "uploadpack.allowFilter", "true")
        target = self.fm.parent / name
        subprocess.run(["git", "clone", "-q", *flags, f"file://{self.fm}", str(target)], check=True, capture_output=True)
        self.fm = target

    def test_rejects_shallow_clone(self) -> None:
        self.clone("shallow", "--depth=1")
        with self.assertRaises(SystemExit) as raised:
            self.sync()
        self.assertIn("shallow clone", str(raised.exception))
        self.assertFalse((self.atlas / c.MANIFEST).exists())

    def test_never_lazy_fetches_from_a_partial_clone(self) -> None:
        self.clone("partial", "--filter=blob:none", "--no-checkout")
        blob = run_git(self.fm, "rev-parse", "HEAD:MathlibExt/Same.lean")
        missing = ["git", "-C", str(self.fm), "cat-file", "-e", blob]
        env = {**os.environ, "GIT_NO_LAZY_FETCH": "1"}
        self.assertNotEqual(subprocess.run(missing, env=env, capture_output=True).returncode, 0)
        with self.assertRaises(SystemExit) as raised:
            self.sync()
        self.assertIn("not in the local Formal-Math repository", str(raised.exception))
        self.assertNotEqual(subprocess.run(missing, env=env, capture_output=True).returncode, 0,
                            "sync must not have fetched the missing blob")
        self.assertFalse((self.atlas / c.MANIFEST).exists())

    def test_terminated_batch_reader_reports_missing_object(self) -> None:
        # Older git (2.39) ends `cat-file --batch` with no "missing" line when it may not lazy-fetch.
        blobs = s.Blobs(self.fm.parent / "not-a-repository")
        try:
            with self.assertRaises(SystemExit) as raised:
                blobs.read("0" * 39 + "1")
        finally:
            blobs.close()
        self.assertIn("not in the local Formal-Math repository", str(raised.exception))


if __name__ == "__main__":
    unittest.main()
