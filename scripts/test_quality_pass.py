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
"""Deterministic tests for scripts/quality_pass.py (no model calls)."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import quality_pass as qp  # noqa: E402

LEAN = """/-
Copyright (c) Meta Platforms, Inc. and affiliates.
-/
module

public import Mathlib.Data.Nat.Basic

@[expose] public section

namespace Foo

/-- **Doubling.** Twice `n` is `n + n`. -/
@[simp]
theorem two_mul' (n : ℕ) : 2 * n = n + n := by
  omega

private lemma helper (n : ℕ) : n = n := rfl

/- a block comment
theorem not_a_decl : True := trivial
-/

public lemma succ_pos' (n : ℕ) : 0 < n + 1 :=
  Nat.succ_pos n

def bar : ℕ := 3

end Foo
"""


def verdict(scores, flags=(False, False, False), quote="theorem two_mul'"):
    return dict(
        statement_summary="s", confidence="high",
        rubrics={r: dict(score=s, rationale="r",
                         findings=[] if s == 5 else [dict(severity="minor", summary="x", quote=quote, suggestion="y")])
                 for r, s in zip(qp.RUBRICS, scores)},
        indicators={i: dict(flag=f, evidence="") for i, f in zip(qp.INDICATORS, flags)},
    )


class ExtractTest(unittest.TestCase):
    def test_public_declarations_only(self):
        rows = qp.extract_declarations(LEAN, "MathlibExt/Foo.lean", "MathlibExt")
        self.assertEqual([r["name"] for r in rows], ["two_mul'", "succ_pos'"])

    def test_docstring_and_attributes_included(self):
        first = qp.extract_declarations(LEAN, "MathlibExt/Foo.lean", "MathlibExt")[0]
        self.assertTrue(first["text"].startswith("/-- **Doubling.**"))
        self.assertIn("@[simp]", first["text"])
        self.assertIn("omega", first["text"])
        self.assertNotIn("helper", first["text"])
        self.assertLess(first["start_line"], first["decl_line"])

    def test_block_comment_is_skipped(self):
        names = [r["name"] for r in qp.extract_declarations(LEAN, "X/A.lean", "X")]
        self.assertNotIn("not_a_decl", names)


class RepoTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name) / "repo"
        (self.repo / "MathlibExt").mkdir(parents=True)
        run = lambda *a: subprocess.run(["git", "-C", str(self.repo), *a], check=True, capture_output=True)
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        run("config", "user.email", "t@example.com"); run("config", "user.name", "t")
        (self.repo / "MathlibExt" / "A.lean").write_text(LEAN)
        run("add", "-A"); run("commit", "-qm", "base")
        self.base = subprocess.run(["git", "-C", str(self.repo), "rev-parse", "HEAD"],
                                   capture_output=True, text=True).stdout.strip()
        (self.repo / "MathlibExt" / "A.lean").write_text(LEAN.replace("def bar", "theorem added : True := trivial\n\ndef bar"))
        (self.repo / "MathlibExt" / "B.lean").write_text("theorem fresh : 1 = 1 := rfl\n")
        run("add", "-A"); run("commit", "-qm", "more")

    def tearDown(self):
        self.tmp.cleanup()

    def test_new_since_base(self):
        pop = qp.population(self.repo, ("MathlibExt",))
        self.assertEqual(len(pop), 4)
        fresh = qp.new_since(self.repo, self.base, ("MathlibExt",), pop)
        self.assertEqual(sorted(r["name"] for r in fresh), ["added", "fresh"])

    def test_prepare_is_deterministic_and_stratified(self):
        runs = []
        for k in range(2):
            run_dir = Path(self.tmp.name) / f"run{k}"
            qp.main(["prepare", "--repo", str(self.repo), "--run-dir", str(run_dir), "--random", "2",
                     "--new", "2", "--since-ref", self.base, "--libraries", "MathlibExt"])
            runs.append(qp.read_jsonl(run_dir / "samples.jsonl"))
        self.assertEqual(runs[0], runs[1])
        ids = [s["id"] for s in runs[0]]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual({s["stratum"] for s in runs[0]}, {"random", "new"})
        manifest = json.loads((Path(self.tmp.name) / "run0" / "manifest.json").read_text())
        self.assertEqual(manifest["base_commit"], self.base)
        with self.assertRaises(SystemExit):
            qp.main(["prepare", "--repo", str(self.repo), "--run-dir", str(Path(self.tmp.name) / "run0"),
                     "--since-ref", self.base])

    def test_report_aggregates(self):
        run_dir = Path(self.tmp.name) / "run"
        qp.main(["prepare", "--repo", str(self.repo), "--run-dir", str(run_dir), "--random", "4",
                 "--new", "0", "--since-ref", self.base, "--libraries", "MathlibExt"])
        samples = qp.read_jsonl(run_dir / "samples.jsonl")
        qp.write_json(run_dir / "judges" / "t.json", dict(model="m"))
        for k, s in enumerate(samples):
            v = verdict([5, 4, 3, 2, 1] if k % 2 else [5, 5, 5, 5, 5], flags=(k == 0, False, False))
            qp.write_json(run_dir / "results" / "t" / f"{s['id']}.json", dict(id=s["id"], ok=True, verdict=v, cost_usd=0.1))
        hist = Path(self.tmp.name) / "history.jsonl"
        qp.main(["report", "--run-dir", str(run_dir), "--label", "t", "--history", str(hist), "--require-complete"])
        summary = json.loads((run_dir / "reports" / "t" / "summary.json").read_text())
        allr = summary["strata"]["random"]["all"]
        self.assertEqual(allr["n"], 4)
        self.assertEqual(allr["rubrics"]["faithfulness"]["mean"], 5.0)
        self.assertEqual(allr["rubrics"]["reuse"]["mean"], 3.0)
        self.assertEqual(allr["rubrics"]["code_quality"]["share_le2"], 0.5)
        self.assertEqual(allr["indicators"]["removable_hypothesis"]["flagged"], 1)
        self.assertEqual(summary["cost_usd"], 0.4)
        findings = qp.read_jsonl(run_dir / "reports" / "t" / "findings.jsonl")
        self.assertEqual(len(findings), 8)
        self.assertEqual(findings[0]["score"], 1)
        self.assertEqual(len(qp.read_jsonl(hist)), 1)


class ValidateTest(unittest.TestCase):
    def test_quotes_and_scores(self):
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
            f.write(LEAN)
        v = verdict([4, 5, 5, 5, 5])
        self.assertEqual(qp.validate_verdict(v, Path(f.name)), [])
        self.assertTrue(v["rubrics"]["faithfulness"]["findings"][0]["quote_verified"])
        bad = verdict([4, 5, 5, 5, 5], quote="not in the file")
        qp.validate_verdict(bad, Path(f.name))
        self.assertFalse(bad["rubrics"]["faithfulness"]["findings"][0]["quote_verified"])
        missing = verdict([3, 5, 5, 5, 5]); missing["rubrics"]["faithfulness"]["findings"] = []
        self.assertTrue(qp.validate_verdict(missing, Path(f.name)))
        self.assertEqual(qp.validate_verdict(None, Path(f.name)), ["no structured output"])

    def test_wilson(self):
        lo, hi = qp.wilson(0, 10)
        self.assertEqual(lo, 0.0)
        self.assertGreater(hi, 0.2)
        self.assertEqual(qp.wilson(0, 0), (0.0, 0.0))

    def test_rubric_files_match_schema(self):
        schema = json.loads((qp.RUBRIC_DIR / "verdict.schema.json").read_text())
        self.assertEqual(tuple(schema["properties"]["rubrics"]["required"]), qp.RUBRICS)
        self.assertEqual(tuple(schema["properties"]["indicators"]["required"]), qp.INDICATORS)
        for name in qp.RUBRICS:
            self.assertTrue((qp.RUBRIC_DIR / f"{name}.md").is_file(), name)


if __name__ == "__main__":
    unittest.main()
