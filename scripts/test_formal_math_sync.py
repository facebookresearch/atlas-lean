#!/usr/bin/env python3
"""Offline tests for scripts/check_formal_math_sync.py and scripts/sync_formal_math.py.

    python3 -m unittest discover -s scripts -p test_formal_math_sync.py -v

Each checker test first asserts that the valid fixture passes (the positive case), then breaks one
thing and asserts the matching mismatch (the negative case). The sync tests build a throwaway
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


def finish(manifest: dict) -> dict:
    manifest["rows"].sort(key=lambda row: row["path"])
    manifest["counts"] = c.count_rows(manifest["rows"])
    manifest["total"] = len(manifest["rows"])
    manifest["rows_digest"] = c.rows_digest(manifest["rows"])
    return manifest


class CheckerTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        for library in c.ROOTS:
            (self.root / library).mkdir()
        write(self.root, "lean-toolchain", "leanprover/lean4:v4.35.0\n")
        files = {
            "MathlibExt/Identical.lean": (c.META + "\n" + BODY, {"disposition": "identical"}),
            "MathlibExt/Attributed.lean": (c.META + "\n" + NOTICE + "\n\n" + BODY,
                                           {"disposition": "attributed", "notice": NOTICE}),
            "MathlibExt/Kept.lean": (THIRD_PARTY + "\n" + BODY, {"disposition": "identical", "header": "upstream"}),
            "MathlibExtTest/Behind.lean": (c.META + BODY, {"disposition": "behind", "upstream_commit": COMMIT}),
            "CSLibExt/Diverged.lean": (c.META + "\ndef y : Nat := 2\n",
                                       {"disposition": "diverged", "upstream_sha256": c.sha256(BODY),
                                        "rationale": "ATLAS-only fix", "backport": "pending"}),
            "CSLibExtTest/Local.lean": (c.META + "\ndef z : Nat := 3\n", {"disposition": "local"}),
            "WantedExt/Retired.lean": (c.META + "\ndef w : Nat := 4\n", {"disposition": "retired", "upstream_commit": COMMIT}),
        }
        rows = []
        for path, (text, fields) in files.items():
            write(self.root, path, text)
            row = {"path": path, "published_sha256": c.sha256(text), **fields}
            if fields["disposition"] in c.HEADER_CHECKED:
                row["upstream_sha256"] = c.sha256(BODY)
            rows.append(row)
        self.manifest = finish({
            "schema_version": 1,
            "upstream": {"repository": "fairinternal/formal-math", "commit": COMMIT},
            "lean_toolchain": "leanprover/lean4:v4.35.0",
            "roots": list(c.ROOTS),
            "rows": rows,
        })
        self.save()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def save(self) -> None:
        write(self.root, c.MANIFEST, c.dump_manifest(finish(self.manifest)))

    def problems(self) -> list[str]:
        return c.check(self.root, self.root / c.MANIFEST)[0]

    def row(self, path: str) -> dict:
        return next(row for row in self.manifest["rows"] if row["path"] == path)

    def assert_clean_then(self, mutate, expected: str) -> None:
        self.assertEqual(self.problems(), [], "valid fixture must pass")
        mutate()
        found = self.problems()
        self.assertTrue(any(expected in p for p in found), f"expected {expected!r} in {found}")

    def test_valid_manifest_and_exit_codes(self) -> None:
        self.assertEqual(self.problems(), [])
        args = ["--root", str(self.root)]
        with redirect_stdout(io.StringIO()):
            self.assertEqual(c.main(args + ["--strict"]), 0)
        os.remove(self.root / "MathlibExt/Identical.lean")
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(c.main(args), 0)  # report-only: prints, still passes
            self.assertEqual(c.main(args + ["--strict"]), 1)
        self.assertIn("report-only", out.getvalue())
        self.assertIn("MathlibExt/Identical.lean: extra row", out.getvalue())

    def test_missing_row(self) -> None:
        self.assert_clean_then(lambda: write(self.root, "WantedExt/New.lean", c.META + BODY), "missing row")

    def test_extra_row(self) -> None:
        self.assert_clean_then(lambda: os.remove(self.root / "CSLibExtTest/Local.lean"), "extra row")

    def test_duplicate_row(self) -> None:
        def mutate() -> None:
            self.manifest["rows"].append(dict(self.row("CSLibExtTest/Local.lean")))
            self.save()
        self.assert_clean_then(mutate, "duplicate row")

    def test_absolute_path(self) -> None:
        def mutate() -> None:
            self.row("CSLibExtTest/Local.lean")["path"] = str(self.root / "CSLibExtTest/Local.lean")
            self.save()
        self.assert_clean_then(mutate, "absolute path")

    def test_escaping_path(self) -> None:
        def mutate() -> None:
            self.row("CSLibExtTest/Local.lean")["path"] = "CSLibExtTest/../../outside/Local.lean"
            self.save()
        self.assert_clean_then(mutate, "escaping path")

    def test_symlinked_path(self) -> None:
        def mutate() -> None:
            target = self.root / "CSLibExtTest/Local.lean"
            os.replace(target, self.root / "elsewhere.lean")
            target.symlink_to(self.root / "elsewhere.lean")
        self.assert_clean_then(mutate, "symlinked path")

    def test_symlinked_directory(self) -> None:
        def mutate() -> None:
            (self.root / "outside").mkdir()
            (self.root / "MathlibExt/Linked").symlink_to(self.root / "outside", target_is_directory=True)
        self.assert_clean_then(mutate, "symlinked path")

    def test_hash_mismatch(self) -> None:
        self.assert_clean_then(lambda: write(self.root, "CSLibExtTest/Local.lean", c.META + "\ndef z : Nat := 4\n"),
                               "published_sha256 mismatch")

    def test_header_only_violation_in_body(self) -> None:
        def mutate() -> None:
            text = c.META + "\n" + BODY.replace("1", "2")
            write(self.root, "MathlibExt/Identical.lean", text)
            self.row("MathlibExt/Identical.lean")["published_sha256"] = c.sha256(text)
            self.save()
        self.assert_clean_then(mutate, "header-only violation: body after the header")

    def test_header_only_violation_missing_meta_header(self) -> None:
        def mutate() -> None:
            text = UPSTREAM
            write(self.root, "MathlibExtTest/Behind.lean", text)
            self.row("MathlibExtTest/Behind.lean")["published_sha256"] = c.sha256(text)
            self.save()
        self.assert_clean_then(mutate, "header-only violation: does not start with the Meta header")

    def test_header_only_violation_notice_changed(self) -> None:
        def mutate() -> None:
            self.row("MathlibExt/Attributed.lean")["notice"] = NOTICE.replace("example", "other")
            self.save()
        self.assert_clean_then(mutate, "recorded notice does not follow the Meta header")

    def test_header_only_violation_kept_header_is_not_a_license(self) -> None:
        def mutate() -> None:
            text = "/-\nAuthors: Someone\n-/\n\n" + BODY
            write(self.root, "MathlibExt/Kept.lean", text)
            self.row("MathlibExt/Kept.lean")["published_sha256"] = c.sha256(text)
            self.save()
        self.assert_clean_then(mutate, "third-party copyright and license header")

    def test_divergence_without_rationale(self) -> None:
        def mutate() -> None:
            del self.row("CSLibExt/Diverged.lean")["rationale"]
            self.save()
        self.assert_clean_then(mutate, "diverged row has no rationale")

    def test_divergence_without_backport_status(self) -> None:
        def mutate() -> None:
            self.row("CSLibExt/Diverged.lean")["backport"] = " "
            self.save()
        self.assert_clean_then(mutate, "backport must be a non-empty string")

    def test_divergence_with_invalid_upstream_hash(self) -> None:
        def mutate() -> None:
            self.row("CSLibExt/Diverged.lean")["upstream_sha256"] = "not-a-hash"
            self.save()
        self.assert_clean_then(mutate, "CSLibExt/Diverged.lean: upstream_sha256 is not a SHA-256 hex digest")

    def test_divergence_without_upstream_hash(self) -> None:
        def mutate() -> None:
            del self.row("CSLibExt/Diverged.lean")["upstream_sha256"]
            self.save()
        self.assert_clean_then(mutate, "CSLibExt/Diverged.lean: upstream_sha256 is not a SHA-256 hex digest")

    def test_retired_with_invalid_commit(self) -> None:
        def mutate() -> None:
            self.row("WantedExt/Retired.lean")["upstream_commit"] = "abc"
            self.save()
        self.assert_clean_then(mutate, "retired row needs a full 40-hex upstream_commit")

    def test_retired_without_commit(self) -> None:
        def mutate() -> None:
            del self.row("WantedExt/Retired.lean")["upstream_commit"]
            self.save()
        self.assert_clean_then(mutate, "retired row needs a full 40-hex upstream_commit")

    def test_digest_and_counts(self) -> None:
        def mutate() -> None:
            text = (self.root / c.MANIFEST).read_text().replace('"disposition": "retired"', '"disposition": "local"')
            write(self.root, c.MANIFEST, text)
        self.assert_clean_then(mutate, "rows_digest does not match")
        self.assertTrue(any("counts do not match" in p for p in self.problems()))


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
        write(self.fm, "MathlibExt/Same.lean", UPSTREAM)
        write(self.fm, "MathlibExt/Old.lean", UPSTREAM)
        write(self.fm, "MathlibExt/Gone.lean", UPSTREAM)
        write(self.fm, "MathlibExt/Edited.lean", UPSTREAM)
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

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def sync(self, *extra: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = s.main(["--formal-math", str(self.fm), "--commit", "HEAD", "--atlas", str(self.atlas), *extra])
        return code, out.getvalue(), err.getvalue()

    def test_fails_closed_then_classifies_and_verifies(self) -> None:
        report_path = self.atlas.parent / "report.md"
        code, _, err = self.sync("--report", str(report_path))
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Edited.lean", err)
        self.assertFalse((self.atlas / c.MANIFEST).exists(), "fail-closed run must not write the manifest")
        self.assertFalse(report_path.exists(), "fail-closed run must not write the report")

        rationales = self.atlas.parent / "rationales.json"
        for bad in ({"rationale": " ", "backport": "pending"}, {"rationale": "fix", "backport": ["pending"]},
                    {"rationale": "fix"}):
            rationales.write_text(json.dumps({"MathlibExt/Edited.lean": bad}))
            code, _, err = self.sync("--rationales", str(rationales))
            self.assertEqual(code, 1, bad)
            self.assertIn("MathlibExt/Edited.lean", err)
            self.assertFalse((self.atlas / c.MANIFEST).exists(), bad)
        rationales.write_text(json.dumps({"MathlibExt/Edited.lean": {"rationale": "urgent fix", "backport": "pending"}}))
        code, report, _ = self.sync("--rationales", str(rationales))
        self.assertEqual(code, 0)
        manifest = json.loads((self.atlas / c.MANIFEST).read_text())
        got = {row["path"]: row["disposition"] for row in manifest["rows"]}
        self.assertEqual(got, {
            "MathlibExt/Same.lean": "identical", "MathlibExt/Old.lean": "behind",
            "MathlibExt/Gone.lean": "retired", "MathlibExt/Edited.lean": "diverged",
            "WantedExt/Mine.lean": "local", "MathlibExt/Flt.lean": "local",
        })
        self.assertEqual(manifest["upstream"]["commit"], self.commit)
        old = next(row for row in manifest["rows"] if row["path"] == "MathlibExt/Old.lean")
        self.assertEqual(old["upstream_commit"], self.first)
        self.assertIn("## Added (6)", report)
        self.assertEqual(c.check(self.atlas, self.atlas / c.MANIFEST)[0], [])

        # Deterministic, and a second run keeps the recorded rationale without --rationales.
        first_bytes = (self.atlas / c.MANIFEST).read_bytes()
        code, report, _ = self.sync()
        self.assertEqual(code, 0)
        self.assertEqual((self.atlas / c.MANIFEST).read_bytes(), first_bytes)
        self.assertIn("## Changed (0)", report)

        write(self.atlas, "MathlibExt/Same.lean", c.META + "\n" + BODY + "\ndef drift : Nat := 8\n")
        code, _, err = self.sync()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Same.lean", err)
        self.assertNotIn("MathlibExt/Edited.lean", err, "an unchanged divergence keeps its explanation")
        write(self.atlas, "MathlibExt/Same.lean", c.META + "\n" + BODY)

        # A diverged file that changes again needs a fresh explanation.
        write(self.atlas, "MathlibExt/Edited.lean", c.META + "\n" + BODY + "\ndef fix : Nat := 9\n")
        code, _, err = self.sync()
        self.assertEqual(code, 1)
        self.assertIn("MathlibExt/Edited.lean", err)
        self.assertEqual((self.atlas / c.MANIFEST).read_bytes(), first_bytes, "rejected sync must not write")

    def test_ignores_git_replace_refs(self) -> None:
        run_git(self.fm, "replace", self.commit, self.first)  # make HEAD read as the first commit
        rationales = self.atlas.parent / "rationales.json"
        rationales.write_text(json.dumps({"MathlibExt/Edited.lean": {"rationale": "urgent fix", "backport": "pending"}}))
        code, _, _ = self.sync("--rationales", str(rationales))
        self.assertEqual(code, 0)
        manifest = json.loads((self.atlas / c.MANIFEST).read_text())
        self.assertEqual(manifest["upstream"]["commit"], self.commit)
        got = {row["path"]: row["disposition"] for row in manifest["rows"]}
        self.assertEqual(got["MathlibExt/Old.lean"], "behind")
        self.assertEqual(got["MathlibExt/Gone.lean"], "retired")


if __name__ == "__main__":
    unittest.main()
