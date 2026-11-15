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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_formal_math_sync as c  # noqa: E402
import sync_formal_math as s  # noqa: E402

BODY = "module\n\ndef x : Nat := 1\n"
UPSTREAM = "/-\nAuthors: Someone\n-/\n" + BODY
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


class CheckerTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        for library in c.ROOTS:
            (self.root / library).mkdir()
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
            write(self.root, path, text)
            row = {"path": path, "published_sha256": c.sha256(text), **fields}
            if fields["disposition"] in c.SYNCED:
                row["upstream_sha256"] = c.sha256(BODY)
            rows.append(row)
        rows.append({"path": "WantedExt/Retired.lean", "disposition": "retired"})
        write(self.root, "CSLibExtTest/Local.lean", c.META + "\ndef z : Nat := 3\n")  # no row: ignored
        self.manifest = {
            "schema_version": 1,
            "upstream": {"repository": "fairinternal/formal-math", "commit": COMMIT},
            "lean_toolchain": "leanprover/lean4:v4.35.0",
            "roots": list(c.ROOTS),
            "rows": sorted(rows, key=lambda row: row["path"]),
        }
        self.save()

    def tearDown(self) -> None:
        self.tmp.cleanup()

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
        self.assertEqual(self.main(), (0, "ok [formal-math-sync]: 6 rows; synced files match the manifest.\n"))

    def test_files_without_a_row_are_ignored(self) -> None:
        write(self.root, "WantedExt/New.lean", c.META + BODY)
        write(self.root, "CSLibExtTest/Local.lean", c.META + "\ndef z : Nat := 4\n")
        self.assertEqual(self.problems(), [])

    def test_diverged_files_are_not_hashed(self) -> None:
        write(self.root, "CSLibExt/Diverged.lean", c.META + "\ndef y : Nat := 3\n")
        self.assertEqual(self.problems(), [])

    # Malformed manifest.
    def test_unreadable_manifest(self) -> None:
        self.assert_clean_then(lambda: write(self.root, c.MANIFEST, "{"), "cannot read manifest")

    def test_wrong_schema_version(self) -> None:
        self.assert_clean_then(lambda: (self.manifest.update(schema_version=2), self.save()), "schema_version is 2")

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

    def test_unknown_disposition(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", disposition="local"), "unknown disposition")

    def test_malformed_hash_field(self) -> None:
        self.assert_clean_then(lambda: self.set_row("CSLibExt/Diverged.lean", upstream_sha256="not-a-hash"),
                               "upstream_sha256 is not a SHA-256")

    # Synced rows.
    def test_synced_file_missing(self) -> None:
        self.assert_clean_then(lambda: os.remove(self.root / "MathlibExt/Identical.lean"), "synced file is missing")
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
        code, out = self.main("--record-divergence", "CSLibExtTest/Local.lean", "--rationale", "why", "--backport", "pending")
        self.assertEqual(code, 1)
        self.assertIn("no manifest row", out)
        os.remove(self.root / "MathlibExt/Identical.lean")
        code, out = self.main("--record-divergence", "MathlibExt/Identical.lean", "--rationale", "why", "--backport", "pending")
        self.assertEqual(code, 1)
        self.assertIn("use --retire", out)
        self.assertEqual((self.root / c.MANIFEST).read_bytes(), before)

    def test_retire_repairs_a_deleted_file(self) -> None:
        os.remove(self.root / "MathlibExt/Kept.lean")
        self.assertNotEqual(self.problems(), [])
        self.assertEqual(self.main("--retire", "MathlibExt/Kept.lean")[0], 0)
        self.assertEqual(self.problems(), [])
        self.assertEqual(self.row_on_disk("MathlibExt/Kept.lean"), {"path": "MathlibExt/Kept.lean", "disposition": "retired"})

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

    def test_retired_rows_carry_over_while_absent(self) -> None:
        self.assertEqual(self.sync("--rationales", str(self.rationales))[0], 0)
        os.remove(self.atlas / "MathlibExt/Same.lean")
        quiet(c.main, ["--root", str(self.atlas), "--retire", "MathlibExt/Same.lean"])
        self.assertEqual(self.sync()[0], 0)
        self.assertEqual(self.rows()["MathlibExt/Same.lean"], {"path": "MathlibExt/Same.lean", "disposition": "retired"})
        write(self.atlas, "MathlibExt/Same.lean", c.META + "\n" + BODY)  # restored: synced again
        self.assertEqual(self.sync()[0], 0)
        self.assertEqual(self.rows()["MathlibExt/Same.lean"]["disposition"], "identical")

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
