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
        theirs = diverged(base["path"], "A-main", "Change zero to two.")
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
        clean = merged_file(b"AX", ours=b"AX", theirs=b"A1", base=b"A", auto=b"AX")
        text, _, problems = self.merge([base], [ours], [theirs], {base["path"]: clean})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual((problems, row["published_sha256"]), ([], fms.sha256(b"AX")))
        self.assertEqual(row["rationale"], "Port the lemma. Restated (#961). Also: Adapted for the bump.")

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
        return subprocess.run([sys.executable, str(TOOL), *args], cwd=self.repo, capture_output=True,
                              text=True, env=env)

    def write(self, files: dict[str, str], rows: list[dict] | None = None, message="edit"):
        for path, text in files.items():
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        if rows is not None:
            (self.repo / bb.MANIFEST).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / bb.MANIFEST).write_text(manifest(rows))
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
