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

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import quality_review as qr  # noqa: E402

LEAN = """module

/-- **Doubling.** -/
@[simp]
theorem two_mul' (n : ℕ) : 2 * n = n + n := by
  omega

private lemma helper : True := trivial

/- comment
theorem hidden : True := trivial
-/

public lemma succ_pos' (n : ℕ) : 0 < n + 1 := Nat.succ_pos n

def bar : ℕ := 3
"""


class QualityReviewTest(unittest.TestCase):
    def test_statements(self):
        rows = qr.statements(LEAN, "MathlibExt/A.lean")
        self.assertEqual([r["name"] for r in rows], ["two_mul'", "succ_pos'"])
        self.assertTrue(rows[0]["text"].startswith("/-- **Doubling.**"))
        self.assertIn("omega", rows[0]["text"])
        self.assertNotIn("helper", rows[0]["text"])

    def test_sample_and_summary(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            (repo / "MathlibExt").mkdir(parents=True)
            git = lambda *a: subprocess.run(["git", "-C", str(repo), *a], check=True, capture_output=True)
            git("init", "-q"); git("config", "user.email", "t@t"); git("config", "user.name", "t")
            (repo / "MathlibExt" / "A.lean").write_text(LEAN)
            git("add", "-A"); git("commit", "-qm", "a", "--date=2020-01-01T00:00:00")
            subprocess.run(["git", "-C", str(repo), "commit", "--amend", "-qm", "a"], check=True,
                           env={"GIT_COMMITTER_DATE": "2020-01-01T00:00:00", "PATH": "/usr/bin:/bin",
                                "HOME": tmp}, capture_output=True)
            (repo / "MathlibExt" / "B.lean").write_text("theorem fresh : 1 = 1 := rfl\n")
            git("add", "-A"); git("commit", "-qm", "b")
            fresh = qr.sample(repo, Path(tmp) / "fresh", qr.argparse.Namespace(random=0, new=5, since="2021-01-01", seed=0))
            self.assertEqual([(r["stratum"], r["name"]) for r in fresh], [("new", "fresh")])
            out = Path(tmp) / "out"
            args = qr.argparse.Namespace(random=2, new=0, since="2021-01-01", seed=0)
            rows = qr.sample(repo, out, args)
            self.assertEqual(qr.sample(repo, out, args), rows)  # frozen on rerun
            with (out / "results.jsonl").open("w") as fh:
                for k, r in enumerate(rows):
                    scores = {name: dict(score=5 if k else 2, reason="r") for name in qr.RUBRICS}
                    fh.write(json.dumps(dict(r, model="m", cost_usd=0.1, **scores)) + "\n")
            summary = qr.summarize(out)
            self.assertEqual(summary["judged"], len(rows))
            random_all = summary["strata"]["random"]["all"]
            self.assertEqual(random_all["n"], 2)
            self.assertEqual(random_all["mean"]["faithfulness"], 3.5)
            self.assertEqual(random_all["serious"], 0.5)
            self.assertEqual(set(summary["strata"]["random"]["by_library"]), set(qr.LIBRARIES))


if __name__ == "__main__":
    unittest.main()
