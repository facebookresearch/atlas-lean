#!/usr/bin/env python3
"""Tests for scripts/bump/bump_branch.py.

Run with: python3 scripts/bump/test_bump_branch.py
"""

from __future__ import annotations

import json
import os
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
    data = {"schema_version": 1, "upstream": {"commit": "a" * 40, "repository": "example/upstream"},
            "lean_toolchain": "leanprover/lean4:v9.8.0", "roots": ["MathlibExt"], **top}
    data["rows"] = sorted(rows, key=lambda row: row["path"])
    return fms.dump_manifest(data)


def diverged(path: str, data: str, rationale: str, upstream: str = "u" * 64) -> dict:
    return {"path": path, "disposition": "diverged", "published_sha256": fms.sha256(data.encode()),
            "rationale": rationale, "backport": "pending", "upstream_sha256": upstream}


class MergeManifestTest(unittest.TestCase):
    def merge(self, base, ours, theirs, files=None):
        files = files or {}
        return bb.merge_manifest(manifest(base), manifest(ours), manifest(theirs),
                                 read_file=lambda path: files.get(path))

    def test_one_sided_and_adjacent_rows_take_their_side(self):
        a, b, c = (diverged(f"MathlibExt/{n}.lean", n, f"edit {n}") for n in "ABC")
        a2, b2 = diverged(a["path"], "A2", "edit A, more"), diverged(b["path"], "B2", "edit B, main")
        text, counts = self.merge([a, b, c], [a2, b, c], [a, b2, c])
        rows = bb.manifest_rows(text)
        self.assertEqual(rows[a["path"]], a2)
        self.assertEqual(rows[b["path"]], b2)
        self.assertEqual(rows[c["path"]], c)
        self.assertEqual(counts, {"main": 1, "bump": 1, "both": 0})

    def test_row_both_sides_changed_is_rerecorded_from_the_merged_file(self):
        base = diverged("MathlibExt/A.lean", "A", "Port the lemma.")
        ours = diverged(base["path"], "A-bump", f"Port the lemma. {BUMP}")
        theirs = diverged(base["path"], "A-main", "Restate docstrings (#961).")
        text, counts = self.merge([base], [ours], [theirs], files={base["path"]: b"A-merged"})
        row = bb.manifest_rows(text)[base["path"]]
        self.assertEqual(row["published_sha256"], fms.sha256(b"A-merged"))
        self.assertEqual(row["rationale"], f"Restate docstrings (#961). {BUMP}")
        self.assertEqual(row["backport"], "pending")
        self.assertEqual(row["upstream_sha256"], base["upstream_sha256"])
        self.assertEqual(counts["both"], 1)

    def test_rewritten_bump_rationale_is_kept_whole(self):
        base = diverged("MathlibExt/A.lean", "A", "Port the lemma.")
        ours = diverged(base["path"], "A-bump", "Rename Foo to Bar for the v9.9.0 API (moved upstream)")
        theirs = diverged(base["path"], "A-main", "Restate docstrings (#961)")
        text, _ = self.merge([base], [ours], [theirs], files={base["path"]: b"m"})
        self.assertEqual(bb.manifest_rows(text)[base["path"]]["rationale"],
                         "Restate docstrings (#961). Also: Rename Foo to Bar for the v9.9.0 API (moved upstream)")

    def test_unresolved_file_stops(self):
        base = diverged("MathlibExt/A.lean", "A", "x")
        with self.assertRaisesRegex(bb.Stop, "not resolved and staged"):
            self.merge([base], [diverged(base["path"], "1", f"x {BUMP}")], [diverged(base["path"], "2", "y")])

    def test_rationale_main_already_has_stops(self):
        base = diverged("MathlibExt/A.lean", "A", "x.")
        ours = diverged(base["path"], "1", f"x. {BUMP}")
        theirs = diverged(base["path"], "2", f"y. {BUMP}")
        with self.assertRaisesRegex(bb.Stop, "already says"):
            self.merge([base], [ours], [theirs], files={base["path"]: b"3"})

    def test_other_dispositions_and_upstream_changes_stop(self):
        base = diverged("MathlibExt/A.lean", "A", "x")
        retired = {"path": base["path"], "disposition": "retired", "published_sha256": base["published_sha256"],
                   "upstream_sha256": base["upstream_sha256"], "line_fingerprint": []}
        with self.assertRaisesRegex(bb.Stop, "dispositions"):
            self.merge([base], [diverged(base["path"], "1", f"x {BUMP}")], [retired], files={base["path"]: b"1"})
        with self.assertRaisesRegex(bb.Stop, "upstream versions"):
            self.merge([base], [diverged(base["path"], "1", f"x {BUMP}")],
                       [diverged(base["path"], "2", "y", upstream="v" * 64)], files={base["path"]: b"1"})

    def test_added_rows(self):
        a = diverged("MathlibExt/A.lean", "A", "x")
        new = diverged("MathlibExt/New.lean", "N", "new")
        text, _ = self.merge([a], [a], [a, new])
        self.assertIn(new["path"], bb.manifest_rows(text))
        text, _ = self.merge([a], [a, new], [a, new])
        self.assertIn(new["path"], bb.manifest_rows(text))
        with self.assertRaisesRegex(bb.Stop, "dispositions|resolve"):
            self.merge([a], [a, new], [a, {**new, "disposition": "identical"}], files={new["path"]: b"N"})

    def test_top_level_fields(self):
        a = diverged("MathlibExt/A.lean", "A", "x")
        base, ours, theirs = manifest([a]), manifest([a]), manifest([a], lean_toolchain="leanprover/lean4:v9.9.0")
        text, _ = bb.merge_manifest(base, ours, theirs, read_file=lambda p: None)
        self.assertEqual(json.loads(text)["lean_toolchain"], "leanprover/lean4:v9.9.0")
        clash = manifest([a], lean_toolchain="leanprover/lean4:v9.7.0")
        with self.assertRaisesRegex(bb.Stop, "lean_toolchain"):
            bb.merge_manifest(base, clash, theirs, read_file=lambda p: None)

    def test_join_rationale(self):
        self.assertEqual(bb.join_rationale("Main.", "Also bump."), "Main. Also bump.")
        self.assertEqual(bb.join_rationale("Main", "Also bump."), "Main. Also bump.")
        self.assertEqual(bb.join_rationale("Main (#1).", "Adapted."), "Main (#1). Also: Adapted.")
        self.assertEqual(bb.join_rationale("", "Adapted."), "Adapted.")
        self.assertEqual(bb.join_rationale("Main. Also bump.", "Also bump."), "Main. Also bump.")
        self.assertEqual(bb.bump_rationale({"rationale": "Base."}, {"rationale": "Base. Also bump."}), "Also bump.")
        self.assertEqual(bb.bump_rationale(None, {"rationale": "Adapted."}), "Adapted.")


class MergeAdjacentTest(unittest.TestCase):
    BASE = "import A\n\n/-- doc -/\ndef x := 1\n\ntheorem t := rfl\n"

    def test_neighbouring_lines_merge(self):
        ours = self.BASE.replace("def x", "noncomputable def x")
        theirs = self.BASE.replace("/-- doc -/", "/-- A restated\ndocstring. -/")
        expected = "import A\n\n/-- A restated\ndocstring. -/\nnoncomputable def x := 1\n\ntheorem t := rfl\n"
        self.assertEqual(bb.merge_adjacent(self.BASE, ours, theirs), expected)
        self.assertEqual(bb.merge_conflicts_adjacent(self.BASE, ours, theirs), expected)

    def test_same_lines_or_same_place_need_a_person(self):
        ours = self.BASE.replace("def x := 1", "noncomputable def x := 1")
        theirs = self.BASE.replace("def x := 1", "def x : Nat := 1")
        self.assertIsNone(bb.merge_adjacent(self.BASE, ours, theirs))
        self.assertIsNone(bb.merge_conflicts_adjacent(self.BASE, ours, theirs))
        self.assertIsNone(bb.merge_adjacent("a\nb\n", "a\nX\nb\n", "a\nY\nb\n"))
        self.assertIsNone(bb.merge_adjacent("a\nb\nc\n", "a\nX\nb\nc\n", "a\nc\n"))

    def test_clean_regions_keep_gits_merge(self):
        lines = [f"line {i}\n" for i in range(30)]
        base = "".join(lines)
        ours = "".join(lines[:5] + ["ours\n"] + lines[6:20] + ["far ours\n"] + lines[20:])
        theirs = "".join(lines[:4] + ["theirs\n"] + lines[5:])
        merged = bb.merge_conflicts_adjacent(base, ours, theirs)
        self.assertEqual(merged, "".join(lines[:4] + ["theirs\n", "ours\n"] + lines[6:20] + ["far ours\n"] + lines[20:]))


class GitTest(unittest.TestCase):
    """End to end on a scratch repository: main and a bump branch diverge from a common base."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.com")

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

    def lean(self, name: str, *lines: str) -> str:
        return "\n".join(lines) + "\n"

    def base_tree(self):
        files = {f"MathlibExt/{n}.lean": self.lean(n, f"-- {n} doc", f"def {n.lower()} := 1", "", "", f"theorem {n.lower()}_eq := rfl")
                 for n in "ABCD"}
        rows = [diverged(path, text, f"Port {path}.") for path, text in files.items()]
        self.write(files, rows, "base")
        return files, rows

    def edit(self, files, rows, path, text, rationale):
        files = dict(files, **{path: text})
        rows = [diverged(path, text, rationale) if row["path"] == path else row for row in rows]
        return files, rows

    def test_merge_main_resolves_manifest_and_commits(self):
        files, rows = self.base_tree()
        a, b, c = (f"MathlibExt/{n}.lean" for n in "ABC")
        self.git("checkout", "-q", "-b", "bump")
        # The bump edits A's last line and C; main edits A's first line and B.
        bf, br = self.edit(files, rows, a, files[a].replace("theorem a_eq := rfl", "theorem a_eq : a = 1 := rfl"),
                           f"Port {a}. {BUMP}")
        bf, br = self.edit(bf, br, c, files[c].replace("def c", "noncomputable def c"), f"Port {c}. {BUMP}")
        self.write(bf, br, "bump")
        self.git("checkout", "-q", "main")
        mf, mr = self.edit(files, rows, a, files[a].replace("-- A doc", "-- A, restated"), "Restate docstrings (#961).")
        mf, mr = self.edit(mf, mr, b, files[b].replace("-- B doc", "-- B, restated"), "Restate docstrings (#961).")
        self.write(mf, mr, "Restate docstrings (#961)")
        self.git("checkout", "-q", "bump")

        status = json.loads(self.tool("status", "--main", "main", "--json").stdout)
        self.assertEqual(status["conflicts_with_main"], [bb.MANIFEST])
        self.assertEqual(status["main_prs_since"], [961])
        self.assertEqual(status["manifest_rows_changed"], 2)

        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(self.git("rev-list", "--count", "--merges", "HEAD").stdout.strip(), "1")
        self.assertEqual(self.git("status", "--porcelain").stdout, "")
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        merged_a = (self.repo / a).read_bytes()
        self.assertIn("-- A, restated", merged_a.decode())
        self.assertIn("a_eq : a = 1", merged_a.decode())
        self.assertEqual(merged[a]["published_sha256"], fms.sha256(merged_a))
        self.assertEqual(merged[a]["rationale"], f"Restate docstrings (#961). {BUMP}")
        self.assertEqual(merged[b], mr[1])
        self.assertEqual(merged[c], br[2])
        self.assertEqual(self.tool("merge-main", "--main", "main").stdout.strip(), "main is already merged")

    def test_lean_conflict_is_left_to_the_user(self):
        files, rows = self.base_tree()
        d = "MathlibExt/D.lean"
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit(files, rows, d, files[d].replace("def d := 1", "noncomputable def d := 1"),
                              f"Port {d}. {BUMP}"), message="bump")
        self.git("checkout", "-q", "main")
        self.write(*self.edit(files, rows, d, files[d].replace("def d := 1", "def d : Nat := 1"),
                              "Type d (#5)."), message="Type d (#5)")
        self.git("checkout", "-q", "bump")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 3, proc.stdout + proc.stderr)
        self.assertIn(d, proc.stdout)
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 3)
        resolved = files[d].replace("def d := 1", "noncomputable def d : Nat := 1")
        (self.repo / d).write_text(resolved)
        self.git("add", d)
        proc = self.tool("resolve-manifest")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        merged = bb.manifest_rows((self.repo / bb.MANIFEST).read_text())
        self.assertEqual(merged[d]["published_sha256"], fms.sha256(resolved.encode()))
        self.assertEqual(merged[d]["rationale"], f"Type d (#5). {BUMP}")
        self.assertEqual(self.git("status", "--porcelain").stdout, "")

    def test_adjacent_resolves_neighbouring_edits(self):
        files, rows = self.base_tree()
        d = "MathlibExt/D.lean"
        self.git("checkout", "-q", "-b", "bump")
        self.write(*self.edit(files, rows, d, files[d].replace("def d := 1", "noncomputable def d := 1"),
                              f"Port {d}. {BUMP}"), message="bump")
        self.git("checkout", "-q", "main")
        self.write(*self.edit(files, rows, d, files[d].replace("-- D doc", "-- D, restated"),
                              "Restate docstrings (#7)."), message="Restate docstrings (#7)")
        self.git("checkout", "-q", "bump")
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

    def test_refuses_a_dirty_tree(self):
        self.base_tree()
        self.git("checkout", "-q", "-b", "bump")
        (self.repo / "MathlibExt/A.lean").write_text("changed\n")
        proc = self.tool("merge-main", "--main", "main")
        self.assertEqual(proc.returncode, 2)
        self.assertIn("uncommitted changes", proc.stderr)

    def test_breakage_names_the_pull_requests(self):
        files, rows = self.base_tree()
        self.git("checkout", "-q", "-b", "bump")
        self.write({"MathlibExt/A.lean": files["MathlibExt/A.lean"] + "-- bump\n"}, message="bump")
        self.git("checkout", "-q", "main")
        self.write({"MathlibExt/B.lean": files["MathlibExt/B.lean"] + "theorem new := rfl\n"},
                   message="Prove a new theorem (#123)")
        self.git("checkout", "-q", "bump")
        self.git("merge", "-q", "--no-edit", "main")
        log = self.repo / "build.log"
        log.write_text("✔ [1/3] Built MathlibExt.A (1.0s)\n"
                       "✖ [2/3] Building MathlibExt.B (2.0s)\n"
                       "error: ././././MathlibExt/C.lean:3:4: unknown identifier\n")
        self.assertEqual(bb.failing_modules(log.read_text()), ["MathlibExt.B", "MathlibExt.C"])
        proc = self.tool("breakage", str(log), "--main", "main")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("Prove a new theorem (#123)", proc.stdout)
        self.assertIn("MathlibExt.C\n  not changed on main", proc.stdout)


if __name__ == "__main__":
    unittest.main()
