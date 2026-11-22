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


def staged_as(files: dict[str, tuple[str, bytes]]):
    return lambda path: files.get(path, (None, None))


class MergeManifestTest(unittest.TestCase):
    def merge(self, base, ours, theirs, files=None):
        return bb.merge_manifest(manifest(base), manifest(ours), manifest(theirs), staged=staged_as(files or {}))

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
        text, counts, problems = self.merge([base], [ours], [theirs], {base["path"]: ("merged", b"A-merged")})
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
        text, counts, _ = self.merge([base], [ours], [theirs], {base["path"]: ("theirs", b"A-main")})
        self.assertEqual((bb.manifest_rows(text)[base["path"]], counts["main"]), (theirs, 1))
        text, counts, _ = self.merge([base], [ours], [theirs], {base["path"]: ("ours", b"A-bump")})
        self.assertEqual((bb.manifest_rows(text)[base["path"]], counts["bump"]), (ours, 1))

    def test_rationale_boundaries(self):
        self.assertEqual(bb.bump_rationale({"rationale": "Base."}, {"rationale": "Base. Also bump."}), "Also bump.")
        self.assertEqual(bb.bump_rationale({"rationale": "Replace Foo"}, {"rationale": "Replace Foobar with Baz."}),
                         "Replace Foobar with Baz.")
        self.assertEqual(bb.bump_rationale({"rationale": "Use Foo"}, {"rationale": "Use Foo bar for the new toolchain"}),
                         "Use Foo bar for the new toolchain")
        self.assertEqual(bb.bump_rationale({"rationale": "Use Foo"}, {"rationale": "Use Foo. Also bump."}), "Also bump.")
        self.assertEqual(bb.bump_rationale({"rationale": "Use Foo"}, {"rationale": "Use Foo, also bump."}),
                         "Use Foo, also bump.")
        self.assertEqual(bb.bump_rationale(None, {"rationale": "Adapted."}), "Adapted.")
        self.assertEqual(bb.join_rationale("Main.", "Also bump."), "Main. Also bump.")
        self.assertEqual(bb.join_rationale("Main", "Also bump."), "Main. Also bump.")
        self.assertEqual(bb.join_rationale("Main (#1).", "Adapted."), "Main (#1). Also: Adapted.")
        self.assertEqual(bb.join_rationale("", "Adapted."), "Adapted.")
        self.assertEqual(bb.join_rationale("Main. Also bump.", "Also bump."), "Main. Also bump.")

    def test_rows_needing_a_person_are_reported_and_the_text_still_parses(self):
        base = diverged("MathlibExt/A.lean", "A", "x.")
        cases = [
            ([base], [diverged(base["path"], "1", f"x. {BUMP}")], [diverged(base["path"], "2", "y.")], {},
             "not resolved and staged"),
            ([base], [diverged(base["path"], "1", f"x. {BUMP}")], [diverged(base["path"], "2", f"y. {BUMP}")],
             {base["path"]: ("merged", b"3")}, "adds nothing"),
            ([base], [diverged(base["path"], "1", f"x. {BUMP}")],
             [{**base, "disposition": "retired", "line_fingerprint": []}], {base["path"]: ("merged", b"1")},
             "dispositions"),
            ([base], [diverged(base["path"], "1", f"x. {BUMP}", upstream="d" * 64)],
             [diverged(base["path"], "2", "y", upstream="f" * 64)], {base["path"]: ("merged", b"1")},
             "both sides changed its 'upstream_sha256'"),
            ([base], [], [base], {}, "the bump removed the row"),
            ([base], [base], [], {}, "main removed the row"),
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
        text, _, problems = bb.merge_manifest(base, ours, theirs, staged=staged_as({}))
        self.assertEqual((json.loads(text)["lean_toolchain"], problems), ("leanprover/lean4:v9.9.0", []))
        _, _, problems = bb.merge_manifest(base, manifest([a], lean_toolchain="v9.7.0"), theirs, staged=staged_as({}))
        self.assertIn("lean_toolchain", problems[0])
        dropped = json.loads(base)
        dropped.pop("lean_toolchain")
        text, _, _ = bb.merge_manifest(base, fms.dump_manifest(dropped), base, staged=staged_as({}))
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

    def test_clean_regions_keep_gits_merge(self):
        lines = [f"line {i}\n" for i in range(30)]
        base = "".join(lines)
        ours = "".join(lines[:5] + ["ours\n"] + lines[6:20] + ["far ours\n"] + lines[20:])
        theirs = "".join(lines[:4] + ["theirs\n"] + lines[5:])
        self.assertEqual(bb.merge_conflicts_adjacent(base, ours, theirs),
                         "".join(lines[:4] + ["theirs\n", "ours\n"] + lines[6:20] + ["far ours\n"] + lines[20:]))

    def test_marker_lines_in_the_file_are_left_alone(self):
        example = "".join(f"{c * 40} example\n" for c in "<|=>")
        base = example + "/-- doc -/\ndef x := 1\n"
        ours = example + "/-- doc -/\nnoncomputable def x := 1\n"
        theirs = example + "/-- new doc -/\ndef x := 1\n"
        self.assertEqual(bb.marker_size(base, ours, theirs), 41)
        self.assertEqual(bb.merge_conflicts_adjacent(base, ours, theirs),
                         example + "/-- new doc -/\nnoncomputable def x := 1\n")

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
        files = {f"MathlibExt/{n}.lean": f"-- {n} doc\ndef {n.lower()} := 1\n\n\ntheorem {n.lower()}_eq := rfl\n"
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
            {a: ("-- A doc", "-- A, restated", "Restate docstrings (#961)."),
             b: ("-- B doc", "-- B, restated", "Restate docstrings (#961).")})
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
        self.assertIn(b"-- A, restated", merged_a)
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
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        self.assertEqual(merged[d]["published_sha256"], fms.sha256(resolved.encode()))
        self.assertEqual(merged[d]["rationale"], f"Type d (#5). {BUMP}")
        self.assertEqual(self.git("status", "--porcelain").stdout, "")

    def test_adjacent_resolves_neighbouring_edits(self):
        d = "MathlibExt/D.lean"
        self.diverge({d: ("def d := 1", "noncomputable def d := 1", f"Port {d}. {BUMP}")},
                     {d: ("-- D doc", "-- D, restated", "Restate docstrings (#7).")}, "Restate docstrings (#7)")
        self.assertEqual(self.tool("merge-main", "--main", "main", "--no-commit").returncode, 3)
        self.git("merge", "--abort")
        proc = self.tool("merge-main", "--main", "main", "--adjacent")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn(f"{d}: merged changes to neighbouring lines", proc.stdout)
        text = (self.repo / d).read_text()
        self.assertIn("-- D, restated\nnoncomputable def d := 1", text)
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        self.assertEqual(merged[d]["published_sha256"], fms.sha256(text.encode()))
        self.assertEqual(merged[d]["rationale"], f"Restate docstrings (#7). {BUMP}")

    def test_adjacent_leaves_a_file_without_a_final_newline(self):
        files, rows = self.base_tree()
        e = "MathlibExt/E.lean"
        self.write({e: "-- E doc\ndef e := 1"}, rows + [diverged(e, "-- E doc\ndef e := 1", "Port E.")], "add E")
        rows = rows + [diverged(e, "-- E doc\ndef e := 1", "Port E.")]
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit({e: ""}, rows, e, "-- E doc\nnoncomputable def e := 1", f"Port E. {BUMP}"))
        self.git("checkout", "-q", "main")
        self.write(*self.edit({e: ""}, rows, e, "-- E, restated\ndef e := 1", "Restate (#8)."))
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
        self.write({a: files[a].replace("-- A doc", "-- A, unrecorded")}, message="Unrecorded edit (#9)")
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
        self.assertIn(a, bb.manifest_rows((self.repo / bb.MANIFEST).read_text()))

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


if __name__ == "__main__":
    unittest.main()
