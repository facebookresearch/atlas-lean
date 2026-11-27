#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Tests for scripts/quality_review.py; no model calls."""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import quality_review as qr  # noqa: E402

MODULE = """module

public import Mathlib.Data.Nat.Basic

theorem hidden_by_module : True := trivial

@[expose] public section

namespace A

/-- An example that must not be scanned:
```
theorem in_docstring : True := trivial
end A
```
-/
theorem documented : True := trivial

/-- **Doubling.** -/
@[simp]
theorem same (n : ℕ) : 2 * n = n + n := by
  omega

private lemma helper : True := trivial

end A

namespace B

theorem same : True := trivial

/- a comment
theorem in_comment : True := trivial
-/

theorem _root_.rooted : True := trivial

private section

theorem in_private_section : True := trivial

end

theorem after_private_section : True := trivial

end B

end
"""

PLAIN = """namespace C

lemma moved : 1 = 1 := rfl

end C
"""


def good(score: int = 5) -> str:
    return json.dumps(dict(is_error=False, total_cost_usd=0.1,
                           structured_output={r: dict(score=score, reason="because") for r in qr.RUBRICS}))


def git(repo: Path, *args: str, date: str = "") -> None:
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@t")
    if date:
        env.update(GIT_AUTHOR_DATE=date, GIT_COMMITTER_DATE=date)
    subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, env=env)


class StatementsTest(unittest.TestCase):
    def test_qualified_names_and_module_visibility(self):
        rows = qr.statements(MODULE, "MathlibExt/X.lean")
        self.assertEqual([r["id"] for r in rows], ["A.documented", "A.same", "B.same", "rooted", "B.after_private_section"])
        self.assertTrue(rows[1]["text"].startswith("/-- **Doubling.**"))
        self.assertIn("omega", rows[1]["text"])
        self.assertNotIn("helper", rows[1]["text"])

    def test_non_module_files_are_public_by_default(self):
        self.assertEqual([r["id"] for r in qr.statements(PLAIN, "MathlibExt/C.lean")], ["C.moved"])


class VerdictTest(unittest.TestCase):
    def test_only_complete_valid_verdicts_count(self):
        verdict, error = qr.parse_verdict(0, good(4))
        self.assertIsNone(error)
        self.assertEqual(verdict["scores"]["tactics"]["score"], 4)
        bad = json.loads(good())
        cases = {
            "exit": (1, good()),
            "json": (0, "not json"),
            "array": (0, "[]"),
            "is_error": (0, json.dumps(dict(json.loads(good()), is_error=True))),
            "missing": (0, json.dumps(dict(bad, structured_output={"faithfulness": {"score": 5, "reason": "r"}}))),
            "range": (0, good(6)),
            "bool": (0, good().replace('"score": 5', '"score": true')),
            "reason": (0, good().replace('"because"', '"  "')),
        }
        for name, (code, stdout) in cases.items():
            with self.subTest(name):
                self.assertIsNone(qr.parse_verdict(code, stdout)[0])


class RunTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.mathlib = root / "mathlib"
        self.mathlib.mkdir()
        git(self.mathlib, "init", "-q")
        (self.mathlib / "Mathlib").mkdir()
        (self.mathlib / "Mathlib" / "Basic.lean").write_text("theorem m : True := trivial\n")
        git(self.mathlib, "add", "-A"); git(self.mathlib, "commit", "-qm", "m")
        pin = subprocess.run(["git", "-C", str(self.mathlib), "rev-parse", "HEAD"],
                             capture_output=True, text=True).stdout.strip()
        self.repo = root / "repo"
        (self.repo / "MathlibExt").mkdir(parents=True)
        git(self.repo, "init", "-q")
        (self.repo / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": pin}]}))
        (self.repo / "MathlibExt" / "X.lean").write_text(MODULE)
        (self.repo / "MathlibExt" / "C.lean").write_text(PLAIN)
        git(self.repo, "add", "-A"); git(self.repo, "commit", "-qm", "base", date="2020-01-01T00:00:00")
        # Move C.moved to another file and add a new statement in an existing namespace.
        (self.repo / "MathlibExt" / "C.lean").unlink()
        (self.repo / "MathlibExt" / "D.lean").write_text(PLAIN + "\nnamespace C\n\ntheorem fresh : True := trivial\n\nend C\n")
        git(self.repo, "add", "-A"); git(self.repo, "commit", "-qm", "more")
        self.out = root / "out"

    def tearDown(self):
        self.tmp.cleanup()

    def args(self, **kw):
        base = dict(out=str(self.out), mathlib=str(self.mathlib), random=0, new=10, since="2021-01-01",
                    model="m", jobs=2)
        base.update(kw)
        return argparse.Namespace(**base)

    def test_run_freezes_sources_and_finds_new_by_qualified_name(self):
        with mock.patch.object(qr, "judge", lambda *a: qr.parse_verdict(0, good())):
            summary = qr.run(self.args(), self.repo)
        samples = [json.loads(line) for line in (self.out / "samples.jsonl").read_text().splitlines()]
        self.assertEqual([(s["stratum"], s["id"]) for s in samples], [("new", "C.fresh")])
        self.assertEqual((summary["status"], summary["population"]), ("complete", 7))
        self.assertTrue((self.out / "source" / "MathlibExt" / "D.lean").is_file())
        self.assertTrue((self.out / "mathlib" / "Mathlib" / "Basic.lean").is_file())
        self.assertFalse((self.out / "source" / ".git").exists())
        self.assertFalse((self.out / "source" / "lake-manifest.json").exists())
        with self.assertRaises(SystemExit):  # one run per directory
            qr.run(self.args(), self.repo)

    def test_run_rejects_unpinned_mathlib(self):
        (self.mathlib / "x").write_text("x")
        git(self.mathlib, "add", "-A"); git(self.mathlib, "commit", "-qm", "drift")
        with self.assertRaises(SystemExit):
            qr.run(self.args(), self.repo)
        self.assertFalse(self.out.exists())

    def test_unusable_cost_is_unknown_not_fatal(self):
        response = json.dumps(dict(json.loads(good(3)), total_cost_usd="0.10"))
        with mock.patch.object(qr, "judge", lambda *a: qr.parse_verdict(0, response)):
            summary = qr.run(self.args(random=2, new=0), self.repo)
        self.assertEqual((summary["status"], summary["judged"], summary["cost_usd"]), ("complete", 2, 0))
        self.assertEqual(summary["strata"]["random"]["all"]["mean"]["tactics"], 3.0)

    def test_run_aborts_if_a_checkout_moves_while_freezing(self):
        real = qr.snapshot
        for moved in ("source", "mathlib"):
            with self.subTest(moved):
                out = Path(str(self.out) + "-" + moved)

                def snap(repo, dest, roots, moved=moved):
                    row = real(repo, dest, roots)
                    return dict(row, commit="0" * 40) if dest.name == moved else row

                with mock.patch.object(qr, "snapshot", snap), \
                        mock.patch.object(qr, "judge", lambda *a: self.fail("judged after a moved checkout")), \
                        self.assertRaisesRegex(SystemExit, "moved while freezing"):
                    qr.run(self.args(out=str(out)), self.repo)
                self.assertFalse((out / "summary.json").exists())

    def test_run_rejects_uncommitted_sources(self):
        (self.repo / "MathlibExt" / "D.lean").write_text("theorem edited : True := trivial\n")
        with self.assertRaisesRegex(SystemExit, "uncommitted"):
            qr.run(self.args(), self.repo)
        self.assertFalse(self.out.exists())

    def test_failed_and_malformed_judgments_make_the_run_incomplete(self):
        responses = iter([(0, good(4)), (0, "[]")])

        def fake(*a):
            code, stdout = next(responses)
            return qr.parse_verdict(code, stdout)

        with mock.patch.object(qr, "judge", fake):
            summary = qr.run(self.args(random=2, new=0, jobs=1), self.repo)
        self.assertEqual(summary["status"], "incomplete")
        self.assertEqual((summary["sampled"], summary["judged"], summary["missing"]), (2, 1, 1))
        block = summary["strata"]["random"]["all"]
        self.assertEqual((block["sampled"], block["judged"], block["missing"]), (2, 1, 1))
        self.assertEqual(block["mean"]["faithfulness"], 4.0)
        self.assertEqual(json.loads((self.out / "summary.json").read_text()), summary)
        self.assertEqual(len((self.out / "results.jsonl").read_text().splitlines()), 1)
        self.assertEqual(len((self.out / "failures.jsonl").read_text().splitlines()), 1)
        with mock.patch.object(qr, "judge", lambda *a: (_ for _ in ()).throw(RuntimeError("boom"))):
            summary = qr.run(self.args(out=str(self.out) + "-2", random=2, new=0), self.repo)
        self.assertEqual((summary["status"], summary["judged"]), ("incomplete", 0))
        with mock.patch.object(qr, "REPO", self.repo), \
                mock.patch.object(qr, "judge", lambda *a: qr.parse_verdict(0, "[]")), \
                self.assertRaisesRegex(SystemExit, "lack a valid verdict"):
            qr.main(["--out", str(self.out) + "-3", "--mathlib", str(self.mathlib), "--random", "1", "--new", "0"])

if __name__ == "__main__":
    unittest.main()
