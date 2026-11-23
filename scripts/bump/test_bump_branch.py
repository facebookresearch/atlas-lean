#!/usr/bin/env python3
"""Tests for scripts/bump/bump_branch.py.

Run with: python3 scripts/bump/test_bump_branch.py
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import bump_branch as bb  # noqa: E402
import check_formal_math_sync as fms  # noqa: E402
from check_copyright import META  # noqa: E402

TOOL = HERE / "bump_branch.py"
BUMP = "Also adapted to the v9.9.0 toolchain bump."


def manifest(rows: list[dict], **top) -> str:
    data = {"schema_version": 1, "upstream": {"commit": "a" * 40, "repository": fms.UPSTREAM_REPOSITORY},
            "lean_toolchain": "leanprover/lean4:v9.8.0", "roots": list(fms.ROOTS), **top}
    data["rows"] = sorted(rows, key=lambda row: row["path"])
    return fms.dump_manifest(data)


def diverged(path: str, data: str, rationale: str, upstream: str = "e" * 64) -> dict:
    return {"path": path, "disposition": "diverged", "published_sha256": fms.sha256(data.encode()),
            "rationale": rationale, "backport": "pending", "upstream_sha256": upstream}


def merged_file(staged: bytes, ours=b"ours", theirs=b"theirs", base=b"base", auto=None) -> dict:
    """What `file_versions` reports; by default a staged file that is the automatic merge."""
    return {"staged": staged, "ours": ours, "theirs": theirs, "base": base,
            "auto": staged if auto is None else auto}


def versions_as(files: dict[str, dict]):
    return lambda path: files.get(path)


class MergeManifestTest(unittest.TestCase):
    def merge(self, base, ours, theirs, files=None):
        return bb.merge_manifest(manifest(base), manifest(ours), manifest(theirs), versions=versions_as(files or {}))

    def test_header_only_rows_retain_their_global_pin_binding(self) -> None:
        path = "MathlibExt/Algebra/New.lean"
        for disposition in ("identical", "attributed"):
            row = {"path": path, "disposition": disposition,
                   "published_sha256": "a" * 64, "upstream_sha256": "b" * 64}
            if disposition == "attributed":
                row["notice"] = "/- Portions adapted from a public source. -/"
            with self.subTest(disposition=disposition):
                self.assertTrue(bb.inherited_row_problems(
                    path, row, row, "a" * 40, same_pin=False, bound_at_pin=False,
                ))
                for same_pin, bound_at_pin in ((True, False), (False, True)):
                    self.assertEqual(bb.inherited_row_problems(
                        path, row, row, "a" * 40,
                        same_pin=same_pin, bound_at_pin=bound_at_pin,
                    ), [])
        behind = {**row, "disposition": "behind", "upstream_commit": "c" * 40}
        self.assertEqual(bb.inherited_row_problems(
            path, behind, behind, "a" * 40, same_pin=False, bound_at_pin=False,
        ), [])

    def test_one_sided_and_adjacent_rows_take_their_side(self):
        a, b, c = (diverged(f"MathlibExt/{n}.lean", n, f"edit {n}") for n in "ABC")
        a2, b2 = diverged(a["path"], "A2", "edit A, more"), diverged(b["path"], "B2", "edit B, main")
        text, counts, problems = self.merge([a, b, c], [a2, b, c], [a, b2, c])
        rows = bb.manifest_rows(text)
        self.assertEqual((rows[a["path"]], rows[b["path"]], rows[c["path"]]), (a2, b2, c))
        self.assertEqual((counts, problems), ({"main": 1, "bump": 1, "both": 0}, []))

    def test_row_both_sides_changed_is_rerecorded_from_the_merged_file(self):
        base = diverged("MathlibExt/A.lean", "A", "Port the lemma.")
        ours = {**diverged(base["path"], "A-bump", f"Port the lemma. {BUMP}"), "backport": "https://example.org/1"}
        theirs = diverged(base["path"], "A-main", "Restate docstrings (#961).")
        text, counts, problems = self.merge([base], [ours], [theirs], {base["path"]: merged_file(b"A-merged")})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual(problems, [])
        self.assertEqual(row["published_sha256"], fms.sha256(b"A-merged"))
        self.assertEqual(row["rationale"], f"Restate docstrings (#961). {BUMP}")
        self.assertEqual(row["backport"], "https://example.org/1", "only the bump changed it")
        self.assertEqual(row["upstream_sha256"], base["upstream_sha256"])
        self.assertEqual(counts["both"], 1)

    def test_a_resolution_that_keeps_one_side_keeps_that_sides_row(self):
        base = diverged("MathlibExt/A.lean", "A", "Port the lemma.")
        ours = diverged(base["path"], "A-bump", f"Port the lemma. {BUMP}")
        theirs = diverged(base["path"], "A-main", "Port the lemma. Change zero to two.")
        kept_main = merged_file(b"A-main", ours=b"A-bump", theirs=b"A-main", base=b"A", auto=b"x")
        text, counts, _ = self.merge([base], [ours], [theirs], {base["path"]: kept_main})
        self.assertEqual((bb.manifest_rows(text)[base["path"]], counts["main"]), (theirs, 1))
        kept_bump = merged_file(b"A-bump", ours=b"A-bump", theirs=b"A-main", base=b"A", auto=b"x")
        text, counts, _ = self.merge([base], [ours], [theirs], {base["path"]: kept_bump})
        self.assertEqual((bb.manifest_rows(text)[base["path"]], counts["bump"]), (ours, 1))
        # Keeping main's file drops the bump's change; a backport the bump set would go with it.
        ours_backport = {**ours, "backport": "https://example.org/2"}
        _, _, problems = self.merge([base], [ours_backport], [theirs], {base["path"]: kept_main})
        self.assertIn("also changed the row's other fields", problems[0])
        # A correction to the rationale made by the discarded side is not dropped silently.
        corrected = {**ours, "rationale": "Port the lemma from PR #21."}
        _, _, problems = self.merge([base], [corrected], [theirs], {base["path"]: kept_main})
        self.assertIn("the bump also rewrote the rationale", problems[0])
        corrected_main = {**theirs, "rationale": "Port the lemma from PR #21."}
        _, _, problems = self.merge([base], [ours], [corrected_main], {base["path"]: kept_bump})
        self.assertIn("main also rewrote the rationale", problems[0])

    def test_a_row_only_correction_on_one_side_survives(self):
        base = diverged("MathlibExt/A.lean", "A", "The local lemma is from PR #12.")
        ours = diverged(base["path"], "A-bump", "The local lemma is from PR #12. Adapted to the new toolchain.")
        theirs = {**base, "rationale": "The local lemma is from PR #21."}
        kept_bump = merged_file(b"A-bump", ours=b"A-bump", theirs=b"A", base=b"A", auto=b"A-bump")
        text, _, problems = self.merge([base], [ours], [theirs], {base["path"]: kept_bump})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual(problems, [])
        self.assertEqual(row["rationale"], "The local lemma is from PR #21. Also: Adapted to the new toolchain.")
        self.assertEqual(row["published_sha256"], ours["published_sha256"])
        # The mirror case: the bump only attributes, main changes the file.
        ours2 = {**base, "rationale": "The local lemma is from PR #12. Attributed to its authors."}
        theirs2 = diverged(base["path"], "A-main", "The local lemma is from PR #12; restated (#961).")
        kept_main = merged_file(b"A-main", ours=b"A", theirs=b"A-main", base=b"A", auto=b"A-main")
        text, _, problems = self.merge([base], [ours2], [theirs2], {base["path"]: kept_main})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual((problems, row["published_sha256"]), ([], theirs2["published_sha256"]))
        self.assertEqual(row["rationale"], "The local lemma is from PR #12; restated (#961). Also: Attributed to its authors.")

    def test_a_clean_merge_equal_to_one_side_keeps_both_accounts(self):
        base = diverged("MathlibExt/A.lean", "A", "Port the lemma.")
        ours = diverged(base["path"], "AX", "Port the lemma. Adapted for the bump.")
        theirs = diverged(base["path"], "AXY", "Port the lemma. Restated (#961).")
        clean = merged_file(b"AXY", ours=b"AX", theirs=b"AXY", base=b"A", auto=b"AXY")
        text, _, problems = self.merge([base], [ours], [theirs], {base["path"]: clean})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual(problems, [])
        self.assertEqual(row["rationale"], "Port the lemma. Restated (#961). Also: Adapted for the bump.")
        self.assertEqual(row["published_sha256"], fms.sha256(b"AXY"))
        # The mirror case: the bump's file contains main's change.
        ours = diverged(base["path"], "AXY", "Port the lemma. Adapted for the bump.")
        theirs = diverged(base["path"], "AX", "Port the lemma. Restated (#961).")
        clean = merged_file(b"AXY", ours=b"AXY", theirs=b"AX", base=b"A", auto=b"AXY")
        text, _, problems = self.merge([base], [ours], [theirs], {base["path"]: clean})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual((problems, row["published_sha256"]), ([], fms.sha256(b"AXY")))
        self.assertEqual(row["rationale"], "Port the lemma. Restated (#961). Also: Adapted for the bump.")
        # With no base rationale, two first accounts of overlapping changes go to a person.
        bare = {**base}
        del bare["rationale"]
        for o_file, t_file in ((b"AX", b"AXY"), (b"AXY", b"AX")):
            o_row = diverged(base["path"], o_file.decode(), "Ported solely from PR #12.")
            t_row = diverged(base["path"], t_file.decode(), "Ported solely from PR #21.")
            staged = max(o_file, t_file, key=len)
            files = {base["path"]: merged_file(staged, ours=o_file, theirs=t_file, base=b"A", auto=staged)}
            _, _, problems = self.merge([bare], [o_row], [t_row], files)
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("first rationales differ", problems[0])

    def test_metadata_only_changes_merge_field_by_field(self):
        base = diverged("MathlibExt/A.lean", "A", "Port the lemma.")
        ours = {**base, "backport": "https://example.org/3"}
        theirs = {**base, "rationale": "Port the lemma; see #12."}
        same = merged_file(b"A", ours=b"A", theirs=b"A", base=b"A")
        text, _, problems = self.merge([base], [ours], [theirs], {base["path"]: same})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual((problems, row["backport"], row["rationale"]), ([], ours["backport"], theirs["rationale"]))

    def test_hand_resolved_or_reverted_files_need_a_person(self):
        base = diverged("MathlibExt/A.lean", "A", "Set a to one.")
        ours = diverged(base["path"], "A2", "Set a to two.")
        theirs = diverged(base["path"], "A3", "Set a to three.")
        for staged, why in ((b"A", "back to the merge base"), (b"A4", "resolved by hand")):
            files = {base["path"]: merged_file(staged, ours=b"A2", theirs=b"A3", base=b"A", auto=b"A23")}
            _, _, problems = self.merge([base], [ours], [theirs], files)
            self.assertIn(why, problems[0])

    def test_rationale_boundaries(self):
        self.assertEqual(bb.appended("Base.", "Base. Also bump."), "Also bump.")
        self.assertIsNone(bb.appended("Replace Foo", "Replace Foobar with Baz."))
        self.assertIsNone(bb.appended("Use Foo", "Use Foo bar for the new toolchain"))
        self.assertEqual(bb.appended("Use Foo", "Use Foo. Also bump."), "Also bump.")
        self.assertIsNone(bb.appended("Use Foo", "Use Foo, also bump."))
        self.assertEqual(bb.appended("", "Adapted."), "Adapted.")
        self.assertEqual(bb.appended("Base.", "Base."), "")
        rows = lambda *texts: [{"rationale": text} for text in texts]
        self.assertEqual(bb.combine_rationales(*rows("PR #12.", "PR #12. Bump.", "PR #21."), "row"), "PR #21. Also: Bump.")
        self.assertEqual(bb.combine_rationales(*rows("PR #12.", "PR #21.", "PR #12. Main."), "row"), "PR #21. Also: Main.")
        self.assertEqual(bb.combine_rationales(*rows("A.", "A. Bump.", "A. Main."), "distinct"), "A. Main. Also: Bump.")
        self.assertEqual(bb.combine_rationales(*rows("", "Bump.", "Main."), "distinct"), "Main. Also: Bump.")
        self.assertIsNone(bb.combine_rationales(*rows("PR #12.", "PR #21.", "PR #13."), "distinct"), "two rewrites")
        self.assertIsNone(bb.combine_rationales(*rows("", "Solely #12.", "Solely #21."), "same"), "one change, two accounts")
        self.assertIsNone(bb.combine_rationales(*rows("A.", "A. From #12.", "A. From #21."), "same"))
        self.assertIsNone(bb.combine_rationales(*rows("", "Note.", "Main."), "row"))
        self.assertEqual(bb.combine_rationales(*rows("", "Same.", "Same."), "same"), "Same.")
        self.assertEqual(bb.join_rationale("Main.", "Also bump."), "Main. Also bump.")
        self.assertEqual(bb.join_rationale("Main", "Also bump."), "Main. Also bump.")
        self.assertEqual(bb.join_rationale("Main (#1).", "Adapted."), "Main (#1). Also: Adapted.")
        self.assertEqual(bb.join_rationale("", "Adapted."), "Adapted.")
        self.assertEqual(bb.join_rationale("A. Backport: PR #130.", "Backport: PR #13"),
                         "A. Backport: PR #130. Also: Backport: PR #13")
        self.assertEqual(bb.join_rationale("A. Also adapted MonoidHom.map_mul.", "map_mul."),
                         "A. Also adapted MonoidHom.map_mul. Also: map_mul.")
        # Only exactly equal additions from the two sides are deduplicated; otherwise both stay.
        rows = lambda *texts: [{"rationale": text} for text in texts]
        self.assertEqual(bb.combine_rationales(*rows("A.", "A. Same.", "A.  Same."), "distinct"), "A.  Same.")
        self.assertEqual(bb.combine_rationales(*rows("A.", "A. Same.", "A. Same. More."), "distinct"),
                         "A. Same. More. Also: Same.")

    def test_rows_needing_a_person_are_reported_and_the_text_still_parses(self):
        base = diverged("MathlibExt/A.lean", "A", "x.")
        cases = [
            ([base], [diverged(base["path"], "1", f"x. {BUMP}")], [diverged(base["path"], "2", "y.")], {},
             "not resolved and staged"),
            # The bump changed the file but kept the base rationale: nothing describes its change.
            ([base], [diverged(base["path"], "1", "x.")], [diverged(base["path"], "2", "y.")],
             {base["path"]: merged_file(b"3")}, "adds nothing"),
            ([base], [diverged(base["path"], "1", f"x. {BUMP}")],
             [{**base, "disposition": "retired", "line_fingerprint": []}], {base["path"]: merged_file(b"1")},
             "dispositions"),
            ([base], [diverged(base["path"], "1", f"x. {BUMP}", upstream="d" * 64)],
             [diverged(base["path"], "2", "y", upstream="f" * 64)], {base["path"]: merged_file(b"1")},
             "both sides changed its 'upstream_sha256'"),
            ([base], [], [base], {}, "the bump removed the row"),
            ([base], [base], [], {}, "main removed the row"),
            ([base], [], [], {}, "both sides removed the row"),
        ]
        for rows_b, rows_o, rows_t, files, why in cases:
            with self.subTest(why=why):
                text, _, problems = self.merge(rows_b, rows_o, rows_t, files)
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(why, problems[0])
                self.assertIn(base["path"], bb.manifest_rows(text))

    def test_added_rows(self):
        a = diverged("MathlibExt/A.lean", "A", "x")
        new = diverged("MathlibExt/New.lean", "N", "new")
        for ours, theirs in (([a], [a, new]), ([a, new], [a]), ([a, new], [a, new])):
            text, _, problems = self.merge([a], ours, theirs)
            self.assertEqual(problems, [])
            self.assertIn(new["path"], bb.manifest_rows(text))
        _, _, problems = self.merge([a], [a, new], [a, {**new, "rationale": "other"}])
        self.assertIn("both sides added a row", problems[0])

    def test_top_level_fields(self):
        a = diverged("MathlibExt/A.lean", "A", "x")
        base, ours = manifest([a]), manifest([a])
        theirs = manifest([a], lean_toolchain="leanprover/lean4:v9.9.0")
        text, _, problems = bb.merge_manifest(base, ours, theirs, versions=versions_as({}))
        self.assertEqual((json.loads(text)["lean_toolchain"], problems), ("leanprover/lean4:v9.9.0", []))
        _, _, problems = bb.merge_manifest(base, manifest([a], lean_toolchain="v9.7.0"), theirs, versions=versions_as({}))
        self.assertIn("lean_toolchain", problems[0])
        dropped = json.loads(base)
        dropped.pop("lean_toolchain")
        text, _, _ = bb.merge_manifest(base, fms.dump_manifest(dropped), base, versions=versions_as({}))
        self.assertNotIn("lean_toolchain", json.loads(text), "a field one side removed is removed, not null")


class MergeAdjacentTest(unittest.TestCase):
    BASE = "import A\n\n/-- doc -/\ndef x := 1\n\ntheorem t := rfl\n"

    def test_neighbouring_lines_merge(self):
        ours = self.BASE.replace("def x", "noncomputable def x")
        theirs = self.BASE.replace("/-- doc -/", "/-- A restated\ndocstring. -/")
        expected = "import A\n\n/-- A restated\ndocstring. -/\nnoncomputable def x := 1\n\ntheorem t := rfl\n"
        self.assertEqual(bb.merge_adjacent(self.BASE, ours, theirs), expected)
        self.assertEqual(bb.merge_conflicts_adjacent(self.BASE, ours, theirs), expected)

    def test_disjoint_changes(self):
        def disjoint(base, ours, theirs):
            return bb.disjoint_changes(base, ours, theirs, bb.auto_merge(base, ours, theirs) or b"")

        base = b"a\n/-- doc -/\ndef x := 1\nb\nc\n"
        neighbours = (b"a\n/-- doc -/\nnoncomputable def x := 1\nb\nc\n", b"a\n/-- new doc -/\ndef x := 1\nb\nc\n")
        self.assertTrue(disjoint(base, *neighbours), "edits on neighbouring lines are different edits")
        shared = (b"a\n/-- doc -/\nnoncomputable def x := 1\nB\nc\n", b"a\n/-- doc -/\nnoncomputable def x := 1\nb\nC\n")
        self.assertFalse(disjoint(base, *shared), "a line changed the same way on both sides")
        self.assertFalse(disjoint(base, b"a\nX\n/-- doc -/\ndef x := 1\nb\nc\n",
                                  b"a\nY\n/-- doc -/\ndef x := 1\nb\nc\n"), "insertions at one place")
        self.assertFalse(disjoint(base, b"a\nnew line\n/-- doc -/\ndef x := 1\nb\nc\n",
                                  b"a\n/-- doc -/\ndef x := 1\nb\nc\nnew line\n"), "a line added by both")
        self.assertFalse(disjoint(base, base, neighbours[1]), "one side changed nothing")
        # One of two repeated lines removed by both sides, plus an edit each: the edits as
        # aligned here would remove both lines, while git's merge removes one.
        base = b"by\n  skip\n  have h := 1\n  skip\n  skip\n  have k := 2\n  skip\n  done\n"
        ours = b"by\n  skip\n  have h := 1\n  skip\n  have k := 2\n  -- later\n  done\n"
        theirs = b"by\n  -- earlier\n  have h := 1\n  skip\n  have k := 2\n  skip\n  done\n"
        merged = bb.auto_merge(base, ours, theirs)
        self.assertIsNotNone(merged)
        self.assertEqual(merged.count(b"  skip\n"), 1, merged)
        self.assertFalse(bb.disjoint_changes(base, ours, theirs, merged))

    def test_what_needs_a_person(self):
        same_line = (self.BASE.replace("def x := 1", "noncomputable def x := 1"),
                     self.BASE.replace("def x := 1", "def x : Nat := 1"))
        # The bump inserts a theorem before `def f`; main inserts the same theorem and renames `f`.
        base = "a\ndef f := 0\nb\n"
        duplicate = ("a\ntheorem t : True := trivial\ndef f := 0\nb\n",
                     "a\ntheorem t : True := trivial\ndef g := 0\nb\n")
        insertion_by_a_deletion = ("a\nX\ndef f := 0\nb\n", "a\nb\n")
        for ours, theirs in (same_line, duplicate, insertion_by_a_deletion):
            with self.subTest(ours=ours):
                b = self.BASE if ours in same_line else base
                self.assertIsNone(bb.merge_conflicts_adjacent(b, ours, theirs))
        self.assertIsNone(bb.merge_adjacent("a\nb\n", "a\nX\nb\n", "a\nY\nb\n"))
        self.assertIsNone(bb.merge_adjacent("a\nb\nc\n", "a\nB\nc\n", "a\nb\nX\nc\n"))
        self.assertIsNone(bb.merge_adjacent("a\nb\nc\n", "a\nY\nc\n", "a\nb\nY\n"), "both sides write the same line")
        # Both replacements grow into their seam: two versions of `ready` would come out.
        base = "def f := 0\ndef g := 0\n"
        ours = "def f := 1\ntheorem ready : True := trivial\ndef g := 0\n"
        theirs = "def f := 0\ntheorem ready : True := by trivial\ndef g := 1\n"
        self.assertIsNone(bb.merge_conflicts_adjacent(base, ours, theirs))
        # The same with equal line counts: the bump also drops a comment above `f`.
        base = "-- Old comment\ndef f := 0\ndef g := 0\n"
        ours = "def f := 1\ntheorem ready : True := trivial\ndef g := 0\n"
        theirs = "-- Old comment\ndef f := 0\ntheorem ready : True := by trivial\ndef g := 1\n"
        self.assertIsNone(bb.merge_conflicts_adjacent(base, ours, theirs))
        # Only a whole doc comment beside one edited code line merges.
        self.assertIsNone(bb.merge_adjacent("/-- a\nb -/\ndef x := 1\n", "/-- a\nb -/\nnoncomputable def x := 1\n",
                                            "/-- a\nc\n"))
        self.assertIsNone(bb.merge_adjacent("-- note\ndef x := 1\n", "-- note\ndef y := 1\n", "-- better note\ndef x := 1\n"))

    def test_clean_regions_keep_gits_merge(self):
        lines = [f"line {i}\n" for i in range(30)]
        lines[4] = "/-- doc -/\n"
        base = "".join(lines)
        ours = "".join(lines[:5] + ["ours\n"] + lines[6:20] + ["far ours\n"] + lines[20:])
        theirs = "".join(lines[:4] + ["/-- new doc -/\n"] + lines[5:])
        self.assertEqual(bb.merge_conflicts_adjacent(base, ours, theirs),
                         "".join(lines[:4] + ["/-- new doc -/\n", "ours\n"] + lines[6:20] + ["far ours\n"] + lines[20:]))

    def test_marker_lines_in_the_file_are_left_alone(self):
        example = "".join(f"{c * 40} example\n" for c in "<|=>")
        base = example + "/-- doc -/\ndef x := 1\n"
        ours = example + "/-- doc -/\nnoncomputable def x := 1\n"
        theirs = example + "/-- new doc -/\ndef x := 1\n"
        self.assertEqual(bb.marker_size(base, ours, theirs), 41)
        self.assertEqual(bb.merge_conflicts_adjacent(base, ours, theirs),
                         example + "/-- new doc -/\nnoncomputable def x := 1\n")

    def test_only_lf_ends_a_line(self):
        # Git sees one line here, changed on both sides; U+2028 or a form feed must not split it.
        for sep in ("\u2028", "\x0c", "\x0b", "\x85"):
            base = f"/-- doc -/{sep}def x := 1\nrest\n"
            ours = f"/-- doc -/{sep}noncomputable def x := 1\nrest\n"
            theirs = f"/-- new doc -/{sep}def x := 1\nrest\n"
            self.assertIsNone(bb.merge_conflicts_adjacent(base, ours, theirs), repr(sep))
        self.assertEqual(bb.lines_of("a\r\nb\u2028c\nd"), ["a\r\n", "b\u2028c\n", "d"])
        self.assertEqual(bb.lines_of(""), [])

    def test_line_endings_are_kept(self):
        base = "a\r\n/-- doc -/\r\ndef x := 1\r\nb\r\n"
        ours = base.replace("def x", "noncomputable def x")
        theirs = base.replace("/-- doc -/", "/-- new -/")
        self.assertEqual(bb.merge_conflicts_adjacent(base, ours, theirs),
                         "a\r\n/-- new -/\r\nnoncomputable def x := 1\r\nb\r\n")


class GitTest(unittest.TestCase):
    """End to end on a scratch repository with the real manifest checker: main and a bump
    branch diverge from a common base."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.com")
        (self.repo / "scripts").mkdir()
        for name in ("check_formal_math_sync.py", "check_copyright.py"):
            shutil.copy(HERE.parent / name, self.repo / "scripts" / name)

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args, check=True):
        return subprocess.run(["git", *args], cwd=self.repo, check=check, capture_output=True, text=True)

    def tool(self, *args):
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        # These disposable repositories model a local bump, not the outer CI pull request.
        env.pop("GITHUB_ACTIONS", None)
        return subprocess.run([sys.executable, str(TOOL), *args], cwd=self.repo, capture_output=True,
                              text=True, env=env)

    def write(
        self, files: dict[str, str], rows: list[dict] | None = None, message: str = "edit", *,
        schema_version: int = 1, upstream_pin: str = "a" * 40,
    ) -> None:
        files = files.copy()
        if rows is not None:
            data = json.loads(manifest(
                rows, schema_version=schema_version,
                upstream={"commit": upstream_pin, "repository": fms.UPSTREAM_REPOSITORY},
            ))
            documents = fms.manifest_documents(Path(bb.MANIFEST), data)
            files.update({path.as_posix(): text for path, text in documents.items()})
        for path, text in files.items():
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def base_tree(self):
        files = {f"MathlibExt/{n}.lean": f"/-- {n} doc -/\ndef {n.lower()} := 1\n\n\ntheorem {n.lower()}_eq := rfl\n"
                 for n in "ABCD"}
        rows = [diverged(path, text, f"Port {path}.") for path, text in files.items()]
        self.write(files, rows, "base")
        return files, rows

    def edit(self, files, rows, path, text, rationale):
        files = dict(files, **{path: text})
        rows = [diverged(path, text, rationale) if row["path"] == path else row for row in rows]
        return files, rows

    def diverge(self, bump_edits, main_edits, main_message="Restate docstrings (#961)"):
        """Commit the bump's and main's edits on top of the base tree; end on the bump branch."""
        files, rows = self.base_tree()
        self.git("checkout", "-q", "-b", "bump")
        bf, br = files, rows
        for path, (old, new, rationale) in bump_edits.items():
            bf, br = self.edit(bf, br, path, bf[path].replace(old, new), rationale)
        self.write(bf, br, "bump")
        self.git("checkout", "-q", "main")
        mf, mr = files, rows
        for path, (old, new, rationale) in main_edits.items():
            mf, mr = self.edit(mf, mr, path, mf[path].replace(old, new), rationale)
        self.write(mf, mr, main_message)
        self.git("checkout", "-q", "bump")
        return files, br, mr

    def test_merge_main_resolves_manifest_and_commits(self):
        a, b, c = (f"MathlibExt/{n}.lean" for n in "ABC")
        _, br, mr = self.diverge(
            {a: ("theorem a_eq := rfl", "theorem a_eq : a = 1 := rfl", f"Port {a}. {BUMP}"),
             c: ("def c", "noncomputable def c", f"Port {c}. {BUMP}")},
            {a: ("/-- A doc -/", "/-- A, restated -/", "Restate docstrings (#961)."),
             b: ("/-- B doc -/", "/-- B, restated -/", "Restate docstrings (#961).")})
        status = json.loads(self.tool("status", "--main", "main", "--json").stdout)
        self.assertEqual((status["conflicts_with_main"], status["main_prs_since"]), ([bb.MANIFEST], [961]))
        self.assertEqual(status["manifest_rows_changed"], 2)
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("ok [formal-math-sync]", proc.stdout)
        self.assertEqual(self.git("rev-list", "--count", "--merges", "HEAD").stdout.strip(), "1")
        self.assertEqual(self.git("status", "--porcelain").stdout, "")
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        merged_a = (self.repo / a).read_bytes()
        self.assertIn(b"/-- A, restated -/", merged_a)
        self.assertIn(b"a_eq : a = 1", merged_a)
        self.assertEqual(merged[a]["published_sha256"], fms.sha256(merged_a))
        self.assertEqual(merged[a]["rationale"], f"Restate docstrings (#961). {BUMP}")
        self.assertEqual((merged[b], merged[c]), (mr[1], br[2]))
        self.assertEqual(self.tool("merge-main", "--main", "main").stdout.strip(), "main is already merged")

    def test_sharded_status_and_row_merge(self) -> None:
        domain, root = "MathlibExt/Algebra/A.lean", "MathlibExt/B.lean"
        shard = "provenance/formal-math-sync.d/MathlibExt/Algebra.json"
        files = {
            domain: "/-- A doc -/\ndef a := 1\n\n\ntheorem a_eq := rfl\n",
            root: "def b := 1\n",
        }
        rows = [diverged(path, text, f"Port {path}.") for path, text in files.items()]
        sharded = fms.SHARDED_SCHEMA_VERSION
        self.write(files, rows, "sharded base", schema_version=sharded)
        self.git("checkout", "-q", "-b", "bump")
        bump_files, bump_rows = self.edit(
            files, rows, domain, files[domain].replace("a_eq :=", "a_eq : a = 1 :="),
            f"Port {domain}. {BUMP}",
        )
        bump_files, bump_rows = self.edit(bump_files, bump_rows, root, "def b : Nat := 1\n", BUMP)
        self.write(bump_files, bump_rows, "bump", schema_version=sharded)
        root_shard = self.repo / "provenance/formal-math-sync.d/MathlibExt.json"
        root_bytes = root_shard.read_bytes()
        self.git("checkout", "-q", "main")
        self.write(*self.edit(files, rows, domain, files[domain].replace("A doc", "A, restated"),
                              "Restate A (#961)."), schema_version=sharded)
        self.git("checkout", "-q", "bump")
        status = self.tool("status", "--main", "main", "--json")
        self.assertEqual(status.returncode, 0, status.stdout + status.stderr)
        report = json.loads(status.stdout)
        self.assertEqual(report["manifest_rows_changed"], 2)
        self.assertEqual(report["conflicts_with_main"], [shard])

        merged = self.tool("merge-main", "--main", "main")
        self.assertEqual(merged.returncode, 0, merged.stdout + merged.stderr)
        self.assertIn("ok [formal-math-sync]", merged.stdout)
        self.assertEqual(self.git("status", "--porcelain").stdout, "")
        self.assertEqual(root_shard.read_bytes(), root_bytes)
        self.assertNotIn("rows", json.loads((self.repo / bb.MANIFEST).read_text()))
        row = bb.manifest_rows((self.repo / shard).read_text())[domain]
        self.assertEqual(row["rationale"], f"Restate A (#961). {BUMP}")
        self.assertEqual(row["published_sha256"], fms.sha256((self.repo / domain).read_bytes()))

    def test_sharded_add_add_merges_disjoint_rows(self) -> None:
        sharded = fms.SHARDED_SCHEMA_VERSION
        self.write({}, [], "sharded base", schema_version=sharded)
        self.git("checkout", "-q", "-b", "bump")
        bump_path, main_path = "MathlibExt/Algebra/A.lean", "MathlibExt/Algebra/B.lean"
        bump_text, main_text = "def a := 1\n", "def b := 2\n"
        bump_row = diverged(bump_path, bump_text, "Create A.")
        main_row = diverged(main_path, main_text, "Create B.")
        self.write({bump_path: bump_text}, [bump_row], schema_version=sharded)
        self.git("checkout", "-q", "main")
        self.write({main_path: main_text}, [main_row], schema_version=sharded)
        self.git("checkout", "-q", "bump")

        merged = self.tool("merge-main", "--main", "main")
        self.assertEqual(merged.returncode, 0, merged.stdout + merged.stderr)
        ledger, errors = fms.load_revision(self.repo, "HEAD")
        self.assertEqual(errors, [])
        self.assertEqual(ledger["rows"], [bump_row, main_row])

    def test_sharded_merge_keeps_manual_index_and_worktree_resolutions(self) -> None:
        files = {f"MathlibExt/{domain}/{domain}.lean": f"def {domain.lower()} := 1\n"
                 for domain in ("Algebra", "Topology")}
        rows = [diverged(path, text, "Base account.") for path, text in files.items()]
        sharded = fms.SHARDED_SCHEMA_VERSION
        self.write(files, rows, "sharded base", schema_version=sharded)
        self.git("checkout", "-q", "-b", "bump")
        bump_rows = [{**row, "rationale": "Bump account."} for row in rows]
        self.write({}, bump_rows, schema_version=sharded)
        self.git("checkout", "-q", "main")
        main_rows = [{**row, "rationale": "Main account."} for row in rows]
        self.write({}, main_rows, schema_version=sharded)
        self.git("checkout", "-q", "bump")

        merge = self.tool("merge-main", "--main", "main")
        self.assertEqual(merge.returncode, 3, merge.stdout + merge.stderr)
        shards = fms.shard_directory(self.repo / bb.MANIFEST) / "MathlibExt"
        algebra, topology = (shards / f"{domain}.json" for domain in ("Algebra", "Topology"))
        algebra_edit = algebra.read_text().replace("Main account.", "Manual Algebra resolution.")
        topology_draft = topology.read_text()
        topology_edit = topology_draft.replace("Main account.", "Manual Topology resolution.")
        self.assertNotEqual(algebra.read_text(), algebra_edit)
        self.assertNotEqual(topology_draft, topology_edit)
        algebra.write_text(algebra_edit)
        self.git("add", str(algebra))
        topology.write_text(topology_edit)

        resolve = self.tool("resolve-manifest")
        self.assertEqual(resolve.returncode, 3, resolve.stdout + resolve.stderr)
        self.assertIn("changes this tool did not make", resolve.stdout)
        self.assertEqual(topology.read_text(), topology_edit)
        resolve = self.tool("resolve-manifest", "--regenerate")
        self.assertEqual(resolve.returncode, 3, resolve.stdout + resolve.stderr)
        backup = Path(resolve.stdout.split("saved as ", 1)[1].splitlines()[0])
        self.assertEqual(backup.read_text(), topology_edit)
        self.assertEqual(topology.read_text(), topology_draft)
        self.assertEqual(algebra.read_text(), algebra_edit)
        staged_path = algebra.relative_to(self.repo).as_posix()
        self.assertEqual(self.git("show", f":0:{staged_path}").stdout, algebra_edit)
        topology.write_text(topology_edit)
        self.git("add", str(topology))
        resolve = self.tool("resolve-manifest")
        self.assertEqual(resolve.returncode, 0, resolve.stdout + resolve.stderr)
        self.assertEqual(self.git("status", "--porcelain").stdout, "")

    def test_manual_sharded_merge_rejects_dropped_bump_only_rows(self) -> None:
        main_path, new_path, retired_path = (
            f"MathlibExt/Algebra/{name}.lean" for name in "ABC"
        )
        base_text, main_text = "def a := 1\n", "def a : Nat := 1\n"
        new_text, retired_text = "def b := 2\n", "def c := 3\n"
        base_row = diverged(main_path, base_text, "Port A.")
        main_row = diverged(main_path, main_text, "Type A.")
        new_row = diverged(new_path, new_text, "Add B on the bump.")
        retired_row = diverged(retired_path, retired_text, "Add C on the bump.")
        sharded = fms.SHARDED_SCHEMA_VERSION
        self.write({main_path: base_text}, [base_row], "base", schema_version=sharded)
        self.git("checkout", "-q", "-b", "bump")
        self.write({new_path: new_text, retired_path: retired_text},
                   [base_row, new_row, retired_row], "add B and C", schema_version=sharded)
        (self.repo / retired_path).unlink()
        tombstone = fms.retired_row(retired_row, retired_path, retired_text)
        self.write({}, [base_row, new_row, tombstone], "retire C", schema_version=sharded)
        self.git("checkout", "-q", "main")
        self.write({main_path: main_text}, [main_row], "type A", schema_version=sharded)
        self.git("checkout", "-q", "bump")
        original_head = self.git("rev-parse", "HEAD").stdout
        merge = self.git("merge", "--no-ff", "--no-commit", "main", check=False)
        self.assertEqual(merge.returncode, 1, merge.stdout + merge.stderr)
        shard = fms.shard_path(Path(bb.MANIFEST), main_path)
        self.git("checkout", "--theirs", "--", str(shard))
        self.git("add", "--", str(shard))
        staged = self.git("write-tree").stdout
        shard_bytes = (self.repo / shard).read_bytes()

        # Main has neither row. The canonical main-relative check alone misses the loss.
        main_check = subprocess.run(
            [sys.executable, bb.CHECKER, "--base", "MERGE_HEAD"], cwd=self.repo,
            capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        )
        self.assertEqual(main_check.returncode, 0, main_check.stdout + main_check.stderr)
        blocked = self.tool("resolve-manifest")
        self.assertEqual(blocked.returncode, 2, blocked.stdout + blocked.stderr)
        self.assertIn(new_path, blocked.stderr)
        self.assertIn(retired_path, blocked.stderr)
        self.assertEqual(self.git("write-tree").stdout, staged)
        self.assertEqual((self.repo / shard).read_bytes(), shard_bytes)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, original_head)

        fixed = fms.dump_manifest({"rows": [main_row, new_row, tombstone]}) + "\n"
        (self.repo / shard).write_text(fixed)
        self.git("add", "--", str(shard))
        resolved = self.tool("resolve-manifest")
        self.assertEqual(resolved.returncode, 0, resolved.stdout + resolved.stderr)
        self.assertIn("ok [formal-math-sync]", resolved.stdout)
        self.assertEqual(self.git("show", f"HEAD:{shard}").stdout, fixed)

    def test_mixed_layout_is_reported_and_left_for_manual_merge(self) -> None:
        files, rows = self.base_tree()
        path, bump_only_path = "MathlibExt/A.lean", "MathlibExt/OnlyBump.lean"
        self.git("checkout", "-q", "-b", "bump")
        bump_files, bump_rows = self.edit(files, rows, path, files[path] + "-- bump\n", BUMP)
        bump_only_text = "def onlyBump := 5\n"
        bump_only_row = diverged(bump_only_path, bump_only_text, "Add module only on the bump.")
        self.write(
            {**bump_files, bump_only_path: bump_only_text}, [*bump_rows, bump_only_row], "bump"
        )
        self.git("checkout", "-q", "main")
        self.write({}, rows, "shard the ledger", schema_version=fms.SHARDED_SCHEMA_VERSION)
        status = self.tool("status", "--main", "bump", "--json")
        self.assertEqual(status.returncode, 0, status.stdout + status.stderr)
        self.assertEqual(json.loads(status.stdout)["manifest_rows_changed"], 0)
        self.git("checkout", "-q", "bump")
        original_head = self.git("rev-parse", "HEAD").stdout
        merged = self.tool("merge-main", "--main", "main")
        self.assertEqual(merged.returncode, 2, merged.stdout + merged.stderr)
        self.assertIn("provenance sharding cutover", merged.stderr)
        self.assertIn("resolve-manifest --check-only", merged.stderr)
        self.assertEqual(self.git("status", "--porcelain").stdout, "")
        merge_head = self.git("rev-parse", "--verify", "MERGE_HEAD", check=False)
        self.assertNotEqual(merge_head.returncode, 0)

        self.git("merge", "--no-ff", "--no-commit", "main", check=False)
        before = self.git("status", "--porcelain").stdout
        original_manifest = (self.repo / bb.MANIFEST).read_bytes()
        resolved = self.tool("resolve-manifest", "--regenerate")
        self.assertEqual(resolved.returncode, 2, resolved.stdout + resolved.stderr)
        self.assertIn("open merge by hand", resolved.stderr)
        self.assertEqual(self.git("status", "--porcelain").stdout, before)
        self.assertEqual((self.repo / bb.MANIFEST).read_bytes(), original_manifest)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, original_head)
        unresolved = self.tool("resolve-manifest", "--check-only")
        self.assertEqual(unresolved.returncode, 2, unresolved.stdout + unresolved.stderr)
        self.assertIn("unresolved conflicts", unresolved.stderr)
        self.assertEqual(self.git("status", "--porcelain").stdout, before)
        self.assertEqual((self.repo / bb.MANIFEST).read_bytes(), original_manifest)

        self.git("checkout", "--theirs", "--", bb.MANIFEST)
        self.git("add", "--", bb.MANIFEST)
        shard = fms.shard_path(Path(bb.MANIFEST), path)
        shard_file = self.repo / shard
        shard_file.write_text(fms.dump_manifest({"rows": bump_rows}))
        self.git("add", "--", str(shard))
        staged = self.git("write-tree").stdout
        blocked = self.tool("resolve-manifest", "--check-only")
        self.assertEqual(blocked.returncode, 2, blocked.stdout + blocked.stderr)
        self.assertIn(bump_only_path, blocked.stderr)
        self.assertEqual(self.git("write-tree").stdout, staged)

        fixed = fms.dump_manifest({"rows": [*bump_rows, bump_only_row]}) + "\n"
        shard_file.write_text(fixed)
        self.git("add", "--", str(shard))
        staged = self.git("write-tree").stdout
        metadata = (self.repo / bb.MANIFEST).read_bytes()
        checked = self.tool("resolve-manifest", "--check-only")
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertIn("ok [formal-math-sync]", checked.stdout)
        self.assertEqual(self.git("write-tree").stdout, staged)
        self.assertEqual(shard_file.read_text(), fixed)
        self.assertEqual((self.repo / bb.MANIFEST).read_bytes(), metadata)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, original_head)
        self.assertEqual(self.git("rev-parse", "MERGE_HEAD").stdout,
                         self.git("rev-parse", "main").stdout)

    def test_staged_merge_validates_inherited_row_contents(self) -> None:
        for mixed, repinned in ((False, False), (True, False), (True, True)):
            with self.subTest(mixed=mixed, repinned=repinned):
                self.tearDown()
                self.setUp()
                self.check_inherited_row_contents(mixed=mixed, repinned=repinned)

    def check_inherited_row_contents(self, *, mixed: bool, repinned: bool) -> None:
        shared, active, retired = (f"MathlibExt/Algebra/{name}.lean" for name in "ABC")
        main_pin, bump_pin = "a" * 40, ("b" if repinned else "a") * 40
        sharded = fms.SHARDED_SCHEMA_VERSION
        base_schema = fms.SCHEMA_VERSION if mixed else sharded
        main_row = diverged(shared, "def a := 1\n", "Record A on main.")
        bump_row = {**main_row, "upstream_sha256": "a" * 64} if repinned else main_row
        active_row = {**diverged(active, "def b := 2\n", "Record B on the bump."),
                      "upstream_commit": "d" * 40}
        retired_text = "theorem c : True := by trivial\n"
        retired_source = {**diverged(retired, retired_text, "Record C on the bump."),
                          "upstream_commit": "e" * 40}
        tombstone = fms.retired_row(retired_source, retired, retired_text)
        self.write({shared: "def a := 1\n"}, [main_row], "base", schema_version=base_schema)
        self.git("checkout", "-q", "-b", "bump")
        self.write({active: "def b := 2\n"}, [bump_row, active_row, tombstone], "bump",
                   schema_version=base_schema, upstream_pin=bump_pin)
        self.git("checkout", "-q", "main")
        if mixed:
            self.write({}, [main_row], "main", schema_version=sharded)
        else:
            self.git("commit", "--allow-empty", "-q", "-m", "main")
        self.git("checkout", "-q", "bump")
        self.git("merge", "--no-ff", "--no-commit", "main", check=False)
        original_head = self.git("rev-parse", "HEAD").stdout
        shard = fms.shard_path(Path(bb.MANIFEST), shared)

        def stage(rows: list[dict], pin: str = bump_pin) -> None:
            data = json.loads(manifest(
                rows, schema_version=sharded,
                upstream={"repository": fms.UPSTREAM_REPOSITORY, "commit": pin},
            ))
            for path, text in fms.manifest_documents(Path(bb.MANIFEST), data).items():
                target = self.repo / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(text)
                self.git("add", "--", str(path))

        def reject(rows: list[dict], path: str, diagnostic: str, pin: str = bump_pin) -> None:
            stage(rows, pin)
            staged = self.git("write-tree").stdout
            physical = (self.repo / shard).read_bytes()
            checked = self.tool("resolve-manifest", "--check-only")
            self.assertEqual(checked.returncode, 2, checked.stdout + checked.stderr)
            self.assertIn(path, checked.stderr)
            self.assertIn(diagnostic, checked.stderr)
            self.assertEqual(self.git("write-tree").stdout, staged)
            self.assertEqual((self.repo / shard).read_bytes(), physical)
            self.assertEqual(self.git("rev-parse", "HEAD").stdout, original_head)

        for field, changed in (("published_sha256", "9" * 64), ("upstream_sha256", "9" * 64),
                               ("upstream_commit", "9" * 40), ("line_fingerprint", ["9" * 12])):
            with self.subTest(field=field):
                reject([bump_row, active_row, {**tombstone, field: changed}], retired, "retired")
        for field, changed in (("upstream_sha256", "9" * 64), ("upstream_commit", "9" * 40)):
            with self.subTest(field=field):
                reject([bump_row, {**active_row, field: changed}, tombstone], active, field)
        if repinned:
            reject([main_row, active_row, tombstone], shared, "upstream_sha256")
            reject([main_row, active_row, {**tombstone, "published_sha256": "9" * 64}],
                   retired, "retired", main_pin)
            reject([main_row, {**active_row, "rationale": "Rewrite across pins."}, tombstone],
                   active, "pin", main_pin)
            stage([main_row, active_row, tombstone], main_pin)
            checked = self.tool("resolve-manifest", "--check-only")
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

        # A real same-pin transition is allowed, not just exact provenance snapshots.
        updated_active = {**active_row, "rationale": "Clarify the local divergence."}
        stage([bump_row, updated_active, tombstone])
        checked = self.tool("resolve-manifest", "--check-only")
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, original_head)

    def test_lean_conflict_is_left_to_the_user(self):
        d = "MathlibExt/D.lean"
        files, _, _ = self.diverge({d: ("def d := 1", "noncomputable def d := 1", f"Port {d}. {BUMP}")},
                                   {d: ("def d := 1", "def d : Nat := 1", "Type d (#5).")}, "Type d (#5)")
        proc = self.tool("merge-main", "--main", "main", "--adjacent")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn(d, proc.stdout)
        resolved = files[d].replace("def d := 1", "noncomputable def d : Nat := 1")
        (self.repo / d).write_text(resolved)
        self.git("add", d)
        (self.repo / d).write_text(resolved + "-- not staged\n")
        proc = self.tool("resolve-manifest")
        self.assertNotEqual(proc.returncode, 0, "an unstaged edit must not be checked in place of the staged file")
        (self.repo / d).write_text(resolved)
        # A file resolved by hand gets its rationale from the person, not from the two rows.
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("resolved by hand", proc.stdout)
        rationale = f"Type d (#5); noncomputable for the v9.9.0 bump."
        record = subprocess.run([sys.executable, "scripts/check_formal_math_sync.py", "--record-divergence", d,
                                 "--rationale", rationale, "--backport", "pending"], cwd=self.repo,
                                capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        self.assertEqual(record.returncode, 0, record.stdout + record.stderr)
        self.git("add", bb.MANIFEST)
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        self.assertEqual(merged[d]["published_sha256"], fms.sha256(resolved.encode()))
        self.assertEqual(merged[d]["rationale"], rationale)
        self.assertEqual(self.git("status", "--porcelain").stdout, "")

    def test_adjacent_resolves_neighbouring_edits(self):
        d = "MathlibExt/D.lean"
        self.diverge({d: ("def d := 1", "noncomputable def d := 1", f"Port {d}. {BUMP}")},
                     {d: ("/-- D doc -/", "/-- D, restated -/", "Restate docstrings (#7).")}, "Restate docstrings (#7)")
        self.assertEqual(self.tool("merge-main", "--main", "main", "--no-commit").returncode, 3)
        self.git("merge", "--abort")
        proc = self.tool("merge-main", "--main", "main", "--adjacent")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn(f"{d}: merged changes to neighbouring lines", proc.stdout)
        text = (self.repo / d).read_text()
        self.assertIn("/-- D, restated -/\nnoncomputable def d := 1", text)
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        self.assertEqual(merged[d]["published_sha256"], fms.sha256(text.encode()))
        self.assertEqual(merged[d]["rationale"], f"Restate docstrings (#7). {BUMP}")

    def test_adjacent_leaves_a_file_without_a_final_newline(self):
        files, rows = self.base_tree()
        e = "MathlibExt/E.lean"
        self.write({e: "/-- E doc -/\ndef e := 1"}, rows + [diverged(e, "/-- E doc -/\ndef e := 1", "Port E.")], "add E")
        rows = rows + [diverged(e, "/-- E doc -/\ndef e := 1", "Port E.")]
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit({e: ""}, rows, e, "/-- E doc -/\nnoncomputable def e := 1", f"Port E. {BUMP}"))
        self.git("checkout", "-q", "main")
        self.write(*self.edit({e: ""}, rows, e, "/-- E, restated -/\ndef e := 1", "Restate (#8)."))
        self.git("checkout", "-q", "bump")
        proc = self.tool("merge-main", "--main", "main", "--adjacent")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn(e, proc.stdout)

    def test_a_merge_the_checker_rejects_is_not_committed(self):
        a = "MathlibExt/A.lean"
        files, rows = self.base_tree()
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit(files, rows, a, files[a].replace("theorem a_eq", "theorem a_eq'"), f"Port {a}. {BUMP}"))
        self.git("checkout", "-q", "main")
        # Main edits the file without recording it: git merges the file, the row stays the bump's.
        self.write({a: files[a].replace("/-- A doc -/", "/-- A, unrecorded -/")}, message="Unrecorded edit (#9)")
        self.git("checkout", "-q", "bump")
        head = self.git("rev-parse", "HEAD").stdout
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
        self.assertIn("does not pass", proc.stderr)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)

    def test_removed_row_leaves_a_parseable_manifest(self):
        files, rows = self.base_tree()
        a, b = "MathlibExt/A.lean", "MathlibExt/B.lean"
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit(files, [r for r in rows if r["path"] != a], b, files[b] + "-- x\n", f"Port {b}. {BUMP}"))
        self.git("checkout", "-q", "main")
        self.write(*self.edit(files, rows, a, files[a] + "-- y\n", "Edit (#3)."))
        self.git("checkout", "-q", "bump")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("removed the row", proc.stdout)
        draft = (self.repo / bb.MANIFEST).read_text()
        self.assertIn(a, bb.manifest_rows(draft))
        # A rerun keeps the person's edits to the draft, even unfinished ones.
        for edited in (draft.replace("Edit (#3).", "Edit (#3), kept."), draft.rstrip().rstrip("}")):
            (self.repo / bb.MANIFEST).write_text(edited)
            proc = self.tool("resolve-manifest")
            self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
            self.assertIn("changes this tool did not make", proc.stdout)
            self.assertEqual((self.repo / bb.MANIFEST).read_text(), edited)
        # Deleting it starts over.
        (self.repo / bb.MANIFEST).unlink()
        self.assertEqual(self.tool("resolve-manifest").returncode, 3)
        self.assertEqual((self.repo / bb.MANIFEST).read_text(), draft)

    def test_a_bracketed_file_name_is_not_a_pattern(self):
        self.base_tree()
        fancy, plain = "MathlibExt/Notes[1].lean", "MathlibExt/Notes1.lean"
        self.write({fancy: "/-- doc -/\ndef n := 1\n", plain: "def m := 1\n"}, message="notes")
        self.git("checkout", "-q", "-b", "bump")
        self.write({fancy: "/-- doc -/\nnoncomputable def n := 1\n", plain: "def m := 2\n"}, message="bump")
        self.git("checkout", "-q", "main")
        self.write({fancy: "/-- new doc -/\ndef n := 1\n", plain: "def m := 3\n"}, message="Notes (#4)")
        self.git("checkout", "-q", "bump")
        head = self.git("rev-parse", "HEAD").stdout
        proc = self.tool("merge-main", "--main", "main", "--adjacent")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn(f"{fancy}: merged changes to neighbouring lines", proc.stdout)
        self.assertNotEqual(self.git("ls-files", "-u", "--", plain).stdout, "", "the other file must stay unmerged")
        self.assertEqual(self.tool("resolve-manifest").returncode, 3)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)

    def test_a_correction_on_main_survives_a_clean_merge(self):
        files, rows = self.base_tree()
        a = "MathlibExt/A.lean"
        rows = [{**r, "rationale": "The local lemma is from PR #12."} if r["path"] == a else r for r in rows]
        self.write({}, rows, "provenance")
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit(files, rows, a, files[a].replace("def a", "noncomputable def a"),
                              "The local lemma is from PR #12. Adapted to the new toolchain."))
        self.git("checkout", "-q", "main")
        self.write({}, [{**r, "rationale": "The local lemma is from PR #21."} if r["path"] == a else r for r in rows],
                   "Correct a transposed reference (#5)")
        self.git("checkout", "-q", "bump")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        self.assertEqual(merged[a]["rationale"], "The local lemma is from PR #21. Also: Adapted to the new toolchain.")

    def test_a_correction_on_the_bump_survives_a_change_on_main(self):
        files, rows = self.base_tree()
        a = "MathlibExt/A.lean"
        rows = [{**r, "rationale": "The local lemma is from PR #12."} if r["path"] == a else r for r in rows]
        self.write({}, rows, "provenance")
        self.git("checkout", "-q", "-b", "bump")
        self.write({}, [{**r, "rationale": "The local lemma is from PR #21."} if r["path"] == a else r for r in rows],
                   "bump: correct a transposed reference")
        self.git("checkout", "-q", "main")
        self.write(*self.edit(files, rows, a, files[a].replace("def a", "noncomputable def a"),
                              "The local lemma is from PR #12. Adapted its definition (#6)."), message="Adapt (#6)")
        self.git("checkout", "-q", "bump")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        self.assertEqual(merged[a]["rationale"], "The local lemma is from PR #21. Also: Adapted its definition (#6).")

    def test_an_unstaged_manual_manifest_is_never_replaced(self):
        d = "MathlibExt/D.lean"
        files, _, mr = self.diverge({d: ("def d := 1", "noncomputable def d := 1", f"Port {d}. {BUMP}")},
                                    {d: ("def d := 1", "def d : Nat := 1", "Type d (#5).")}, "Type d (#5)")
        self.assertEqual(self.tool("merge-main", "--main", "main").returncode, 3)
        resolved = files[d].replace("def d := 1", "noncomputable def d : Nat := 1")
        (self.repo / d).write_text(resolved)
        self.git("add", d)
        # The person writes the manifest themselves before the tool has written any draft.
        mine = json.loads(self.git("show", f":3:{bb.MANIFEST}").stdout)
        for row in mine["rows"]:
            if row["path"] == d:
                row.update(published_sha256=fms.sha256(resolved.encode()), rationale="Type d (#5); noncomputable.")
        (self.repo / bb.MANIFEST).write_text(fms.dump_manifest(mine))
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("changes this tool did not make", proc.stdout)
        self.assertEqual((self.repo / bb.MANIFEST).read_text(), fms.dump_manifest(mine))
        self.git("add", bb.MANIFEST)
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(bb.manifest_rows(self.git("show", f"HEAD:{bb.MANIFEST}").stdout)[d]["rationale"],
                         "Type d (#5); noncomputable.")

    def test_a_merge_can_be_aborted_and_retried(self):
        a = "MathlibExt/A.lean"
        self.diverge({a: ("theorem a_eq := rfl", "theorem a_eq : a = 1 := rfl", f"Port {a}. {BUMP}")},
                     {a: ("/-- A doc -/", "/-- A, restated -/", "Restate docstrings (#961).")})
        self.assertEqual(self.tool("merge-main", "--main", "main", "--no-commit").returncode, 0)
        self.git("merge", "--abort")
        proc = self.tool("merge-main", "--main", "main", "--no-commit")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        # After a merge the person started with git, the tool asks before replacing git's file.
        self.git("merge", "--abort")
        self.git("merge", "--no-ff", "--no-commit", "main", check=False)
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        proc = self.tool("resolve-manifest", "--regenerate")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("saved as", proc.stdout)

    def test_two_accounts_of_the_same_change_need_a_person(self):
        files, rows = self.base_tree()
        i = "MathlibExt/I.lean"
        body = "def i := 1\n"
        synced = META + "\n" + body
        identical = {"path": i, "disposition": "identical", "published_sha256": fms.sha256(synced.encode()),
                     "upstream_sha256": fms.sha256(body.encode())}
        self.write({i: synced}, rows + [identical], "sync I")
        changed = synced.replace("def i", "noncomputable def i")
        rows = rows + [identical]

        def diverge_i(rationale):
            row = {**identical, "disposition": "diverged", "published_sha256": fms.sha256(changed.encode()),
                   "rationale": rationale, "backport": "pending"}
            return [row if r["path"] == i else r for r in rows]

        self.git("checkout", "-q", "-b", "bump")
        self.write({i: changed}, diverge_i("Ported solely from PR #12."), "bump")
        self.git("checkout", "-q", "main")
        self.write({i: changed}, diverge_i("Ported solely from PR #21."), "Port I (#21)")
        self.git("checkout", "-q", "bump")
        head = self.git("rev-parse", "HEAD").stdout
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("describe the same change differently", proc.stdout)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)
        record = subprocess.run([sys.executable, "scripts/check_formal_math_sync.py", "--record-divergence", i,
                                 "--rationale", "Ported from PR #21 (first proposed in PR #12).", "--backport",
                                 "pending"], cwd=self.repo, capture_output=True, text=True,
                                env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        self.assertEqual(record.returncode, 0, record.stdout + record.stderr)
        self.git("add", bb.MANIFEST)
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_adjacent_never_overwrites_an_edited_conflict_file(self):
        d = "MathlibExt/D.lean"
        self.diverge({d: ("def d := 1", "noncomputable def d := 1", f"Port {d}. {BUMP}")},
                     {d: ("/-- D doc -/", "/-- D, restated -/", "Restate docstrings (#7).")}, "Restate docstrings (#7)")
        head = self.git("rev-parse", "HEAD").stdout
        self.assertEqual(self.tool("merge-main", "--main", "main").returncode, 3)
        edited = (self.repo / d).read_text() + "-- my note, outside the conflict\n"
        (self.repo / d).write_text(edited)
        proc = self.tool("resolve-manifest", "--adjacent")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("leaves it to you", proc.stdout)
        self.assertEqual((self.repo / d).read_text(), edited)
        self.assertNotEqual(self.git("ls-files", "-u", "--", d).stdout, "")
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)

    def test_a_reference_inside_a_longer_one_is_kept(self):
        for bump_note, main_note, kept in (("Backport: PR #13", "Backport: PR #130.", ("PR #13", "PR #130")),
                                           ("Reference: Theorem 4.", "Reference: Theorem 4 bis.",
                                            ("Theorem 4.", "Theorem 4 bis.")),
                                           ("map_mul.", "Also adapted MonoidHom.map_mul.",
                                            ("map_mul.", "MonoidHom.map_mul."))):
            with self.subTest(bump_note=bump_note):
                self.tearDown()
                self.setUp()
                files, rows = self.base_tree()
                a = "MathlibExt/A.lean"
                rows = [{**r, "rationale": "Port the lemma."} if r["path"] == a else r for r in rows]
                self.write({}, rows, "provenance")
                self.git("checkout", "-q", "-b", "bump")
                self.write({}, [{**r, "rationale": f"Port the lemma. {bump_note}"} if r["path"] == a else r
                                for r in rows], "bump: add a note")
                self.git("checkout", "-q", "main")
                self.write(*self.edit(files, rows, a, files[a].replace("def a", "noncomputable def a"),
                                      f"Port the lemma. {main_note}"), message="Adapt (#130)")
                self.git("checkout", "-q", "bump")
                proc = self.tool("merge-main", "--main", "main")
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                rationale = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())[a]["rationale"]
                self.assertIn(kept[1], rationale)
                self.assertIn(kept[0], rationale.replace(kept[1], ""), rationale)

    def test_a_mode_change_counts_as_an_edit(self):
        d = "MathlibExt/D.lean"
        self.diverge({d: ("def d := 1", "noncomputable def d := 1", f"Port {d}. {BUMP}")},
                     {d: ("/-- D doc -/", "/-- D, restated -/", "Restate docstrings (#7).")}, "Restate docstrings (#7)")
        head = self.git("rev-parse", "HEAD").stdout
        self.assertEqual(self.tool("merge-main", "--main", "main").returncode, 3)
        (self.repo / d).chmod(0o755)
        proc = self.tool("resolve-manifest", "--adjacent")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("leaves it to you", proc.stdout)
        self.assertNotEqual(self.git("ls-files", "-u", "--", d).stdout, "")
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)

    def test_a_clean_merge_equal_to_mains_file_keeps_the_bumps_account(self):
        files, rows = self.base_tree()
        a = "MathlibExt/A.lean"
        same = files[a].replace("def a := 1", "noncomputable def a := 1")
        more = same.replace("theorem a_eq := rfl", "theorem a_eq : a = 1 := rfl")
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit(files, rows, a, same, f"Port {a}. {BUMP}"))
        self.git("checkout", "-q", "main")
        self.write(*self.edit(files, rows, a, more, f"Port {a}. Type a_eq (#8)."), message="Type a_eq (#8)")
        self.git("checkout", "-q", "bump")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual((self.repo / a).read_text(), more)
        row = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())[a]
        self.assertEqual(row["rationale"], f"Port {a}. Type a_eq (#8). {BUMP}")
        self.assertEqual(row["published_sha256"], fms.sha256(more.encode()))

    def test_first_accounts_of_contained_changes_need_a_person(self):
        for bump_more in (False, True):
            with self.subTest(bump_more=bump_more):
                self.tearDown()
                self.setUp()
                files, rows = self.base_tree()
                i = "MathlibExt/I.lean"
                body = "def i := 1\n\n\ntheorem i_eq := rfl\n"
                synced = META + "\n" + body
                identical = {"path": i, "disposition": "identical", "published_sha256": fms.sha256(synced.encode()),
                             "upstream_sha256": fms.sha256(body.encode())}
                rows = rows + [identical]
                self.write({i: synced}, rows, "sync I")
                annotated = synced.replace("def i", "noncomputable def i")
                typed = annotated.replace("theorem i_eq := rfl", "theorem i_eq : i = 1 := rfl")

                def diverge_i(text, rationale):
                    row = {**identical, "disposition": "diverged", "published_sha256": fms.sha256(text.encode()),
                           "rationale": rationale, "backport": "pending"}
                    return [row if r["path"] == i else r for r in rows]

                bump_text, main_text = (typed, annotated) if bump_more else (annotated, typed)
                self.git("checkout", "-q", "-b", "bump")
                self.write({i: bump_text}, diverge_i(bump_text, "Annotation solely from PR #12."), "bump")
                self.git("checkout", "-q", "main")
                self.write({i: main_text}, diverge_i(main_text, "Annotation solely from PR #21."), "Port I (#21)")
                self.git("checkout", "-q", "bump")
                head = self.git("rev-parse", "HEAD").stdout
                proc = self.tool("merge-main", "--main", "main")
                self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
                self.assertIn("first rationales differ", proc.stdout)
                self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)

    def test_a_shared_edit_beside_independent_edits_needs_a_person(self):
        files, rows = self.base_tree()
        i = "MathlibExt/I.lean"
        body = "".join(f"def i{n} := {n}\n" for n in range(20))
        synced = META + "\n" + body
        identical = {"path": i, "disposition": "identical", "published_sha256": fms.sha256(synced.encode()),
                     "upstream_sha256": fms.sha256(body.encode())}
        rows = rows + [identical]
        self.write({i: synced}, rows, "sync I")
        shared = synced.replace("def i9 ", "noncomputable def i9 ")

        def diverge_i(text, rationale):
            row = {**identical, "disposition": "diverged", "published_sha256": fms.sha256(text.encode()),
                   "rationale": rationale, "backport": "pending"}
            return [row if r["path"] == i else r for r in rows]

        bump_text = shared.replace("def i1 := 1", "def i1 : Nat := 1")
        main_text = shared.replace("def i17 := 17", "def i17 : Nat := 17")
        self.git("checkout", "-q", "-b", "bump")
        self.write({i: bump_text}, diverge_i(bump_text, "Annotation on i9 solely from PR #12."), "bump")
        self.git("checkout", "-q", "main")
        self.write({i: main_text}, diverge_i(main_text, "Annotation on i9 solely from PR #21."), "Port I (#21)")
        self.git("checkout", "-q", "bump")
        head = self.git("rev-parse", "HEAD").stdout
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("edits may overlap", proc.stdout)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)

    def test_first_accounts_of_disjoint_edits_are_combined(self):
        files, rows = self.base_tree()
        i = "MathlibExt/I.lean"
        body = "".join(f"def i{n} := {n}\n" for n in range(20))
        synced = META + "\n" + body
        identical = {"path": i, "disposition": "identical", "published_sha256": fms.sha256(synced.encode()),
                     "upstream_sha256": fms.sha256(body.encode())}
        rows = rows + [identical]
        self.write({i: synced}, rows, "sync I")

        def diverge_i(text, rationale):
            row = {**identical, "disposition": "diverged", "published_sha256": fms.sha256(text.encode()),
                   "rationale": rationale, "backport": "pending"}
            return [row if r["path"] == i else r for r in rows]

        bump_text = synced.replace("def i1 := 1", "noncomputable def i1 := 1")
        main_text = synced.replace("def i17 := 17", "def i17 : Nat := 17")
        self.git("checkout", "-q", "-b", "bump")
        self.write({i: bump_text}, diverge_i(bump_text, "Adapted i1 to the new toolchain."), "bump")
        self.git("checkout", "-q", "main")
        self.write({i: main_text}, diverge_i(main_text, "Typed i17 (#22)."), "Type i17 (#22)")
        self.git("checkout", "-q", "bump")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        row = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())[i]
        self.assertEqual(row["rationale"], "Typed i17 (#22). Also: Adapted i1 to the new toolchain.")

    def test_a_shared_deletion_among_repeated_lines_needs_a_person(self):
        files, rows = self.base_tree()
        i = "MathlibExt/I.lean"
        body = "theorem t : True := by\n  skip\n  have h := 1\n  skip\n  skip\n  have k := 2\n  skip\n  trivial\n"
        synced = META + "\n" + body
        identical = {"path": i, "disposition": "identical", "published_sha256": fms.sha256(synced.encode()),
                     "upstream_sha256": fms.sha256(body.encode())}
        rows = rows + [identical]
        self.write({i: synced}, rows, "sync I")

        def diverge_i(text, rationale):
            row = {**identical, "disposition": "diverged", "published_sha256": fms.sha256(text.encode()),
                   "rationale": rationale, "backport": "pending"}
            return [row if r["path"] == i else r for r in rows]

        middle = "  skip\n  skip\n  have k"
        bump_text = synced.replace(middle, "  skip\n  have k").replace("  have k := 2\n  skip\n", "  have k := 2\n  -- later\n")
        main_text = synced.replace(middle, "  skip\n  have k").replace("by\n  skip\n", "by\n  -- earlier\n")
        self.git("checkout", "-q", "-b", "bump")
        self.write({i: bump_text}, diverge_i(bump_text, "Removal of the redundant skip solely from PR #12."), "bump")
        self.git("checkout", "-q", "main")
        self.write({i: main_text}, diverge_i(main_text, "Removal of the redundant skip solely from PR #21."), "I (#21)")
        self.git("checkout", "-q", "bump")
        head = self.git("rev-parse", "HEAD").stdout
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn("edits may overlap", proc.stdout)
        self.assertEqual(self.git("rev-parse", "HEAD").stdout, head)

    def test_refuses_a_dirty_tree(self):
        self.base_tree()
        self.git("checkout", "-q", "-b", "bump")
        (self.repo / "MathlibExt/A.lean").write_text("changed\n")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 2)
        self.assertIn("uncommitted changes", proc.stderr)

    def test_breakage_names_candidate_pull_requests(self):
        files, _ = self.base_tree()
        self.git("checkout", "-q", "-b", "bump")
        self.write({"MathlibExt/A.lean": files["MathlibExt/A.lean"] + "-- bump\n"}, message="bump")
        log = self.repo.parent / f"{self.repo.name}-build.log"
        log.write_text("✖ [2/3] Building MathlibExt.B (2.0s)\n")
        proc = self.tool("breakage", str(log), "--main", "main")
        self.assertEqual(proc.returncode, 2, "no merge of main on the branch yet")
        self.assertIn("--since", proc.stderr)
        self.git("checkout", "-q", "main")
        self.write({"MathlibExt/B.lean": files["MathlibExt/B.lean"] + "theorem new := rfl\n"},
                   message="Prove a new theorem (#123)")
        self.git("checkout", "-q", "bump")
        self.git("merge", "-q", "--no-edit", "main")
        log.write_text("✔ [1/3] Built MathlibExt.A (1.0s)\n"
                       "✖ [2/3] Building MathlibExt.B (2.0s)\n"
                       "✖ [3/4] Building MathlibExt.Étale (2.0s)\n"
                       "error: ././././MathlibExt/C.lean:3:4: unknown identifier\n")
        self.assertEqual(bb.failing_modules(log.read_text()), ["MathlibExt.B", "MathlibExt.Étale", "MathlibExt.C"])
        proc = self.tool("breakage", str(log), "--main", "main")
        log.unlink()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("candidate pull requests", proc.stdout)
        self.assertIn("Prove a new theorem (#123)", proc.stdout)
        self.assertIn("MathlibExt.C\n  not changed on main", proc.stdout)
        self.assertIn("MathlibExt.Étale\n  not a file of this repository", proc.stdout)

    def test_breakage_during_a_merge_sees_files_main_added(self):
        files, _ = self.base_tree()
        self.git("checkout", "-q", "-b", "bump")
        self.write({"MathlibExt/A.lean": files["MathlibExt/A.lean"] + "-- bump\n"}, message="bump")
        self.git("checkout", "-q", "main")
        self.write({"MathlibExt/New.lean": "theorem new := rfl\n"}, message="Add a new module (#124)")
        self.git("checkout", "-q", "bump")
        self.git("merge", "-q", "--no-commit", "main")
        log = self.repo.parent / f"{self.repo.name}-merge.log"
        log.write_text("✖ [2/3] Building MathlibExt.New (2.0s)\n")
        proc = self.tool("breakage", str(log), "--main", "main")
        log.unlink()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("MathlibExt.New\n  ", proc.stdout)
        self.assertIn("Add a new module (#124)", proc.stdout)


if __name__ == "__main__":
    unittest.main()
