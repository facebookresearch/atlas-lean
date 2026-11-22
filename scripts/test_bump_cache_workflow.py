#!/usr/bin/env python3
"""Keep .github/workflows/bump-cache.yml in step with ci.yml's build job.

bump-cache.yml warms ci.yml's build cache for a Lean/Mathlib bump: it builds a
bump's head and saves .lake/build where ci.yml's restore step finds it. That
only helps while the two agree on the cache path and key prefix and on what
the build runs, and it is only safe while the workflow stays dispatch-only,
read-only, and passes its inputs to scripts through the environment.

Run with: python3 -m unittest discover -s scripts -p test_bump_cache_workflow.py
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github" / "workflows"
CI = WORKFLOWS / "ci.yml"
WARM = WORKFLOWS / "bump-cache.yml"

KEY_PREFIX = "lake-build-${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}-"
HEAVY = re.compile(r"for module in \\\n((?:[ \t]+[A-Za-z0-9_.']+ \\\n)*[ \t]+[A-Za-z0-9_.']+); do")


def heavy_modules(text: str) -> list[list[str]]:
    """Each `for module in ...; do` list of memory-heavy modules, in order."""
    return [[line.strip().rstrip("\\").strip() for line in match.group(1).splitlines()]
            for match in HEAVY.finditer(text)]


def top_level_block(lines: list[str], key: str) -> list[str]:
    """The lines nested under the top-level `key:`, or [] when it is absent."""
    for index, line in enumerate(lines):
        if re.match(re.escape(key) + r":(\s.*)?$", line):
            body = []
            for nested in lines[index + 1:]:
                if nested.strip() and not nested.startswith((" ", "#")):
                    break
                body.append(nested)
            return body
    return []


def run_blocks(lines: list[str]) -> list[str]:
    """The text of every `run:` script, inline or block."""
    scripts = []
    for index, line in enumerate(lines):
        match = re.match(r"(\s*)(?:- )?run:\s*(.*)$", line)
        if not match:
            continue
        indent, rest = len(match.group(1)), match.group(2)
        if rest not in ("|", ">", "|-", ">-"):
            scripts.append(rest)
            continue
        body = []
        for nested in lines[index + 1:]:
            if nested.strip() and len(nested) - len(nested.lstrip()) <= indent:
                break
            body.append(nested)
        scripts.append("\n".join(body))
    return scripts


class BumpCacheWorkflowTest(unittest.TestCase):
    def setUp(self) -> None:
        self.ci = CI.read_text(encoding="utf-8")
        self.warm = WARM.read_text(encoding="utf-8")
        self.warm_lines = self.warm.splitlines()

    def test_dispatch_only(self) -> None:
        on = top_level_block(self.warm_lines, "on")
        events = [m.group(1) for m in (re.match(r"  ([a-z_]+):", line) for line in on) if m]
        self.assertEqual(events, ["workflow_dispatch"],
                         "bump-cache.yml saves a cache main's builds restore: only a maintainer's dispatch may run it")

    def test_read_only_token(self) -> None:
        permissions = top_level_block(self.warm_lines, "permissions")
        granted = dict(re.findall(r"^  ([a-z-]+): (\S+)", "\n".join(permissions), re.M))
        self.assertEqual(granted, {"contents": "read", "pull-requests": "read", "checks": "read"})
        self.assertIsNone(re.search(r"(?m)^[ \t]+permissions:", self.warm), "no job may widen the token")
        self.assertNotIn("write", "\n".join(permissions))

    def test_inputs_reach_scripts_only_through_the_environment(self) -> None:
        for script in run_blocks(self.warm_lines):
            self.assertNotIn("${{", script, f"interpolated expression in a run script:\n{script}")

    def test_same_heavy_modules_as_ci(self) -> None:
        ci_lists, warm_lists = heavy_modules(self.ci), heavy_modules(self.warm)
        self.assertEqual(len(ci_lists), 1, "ci.yml's memory-heavy module list moved; update this test")
        self.assertEqual(len(warm_lists), 1, "bump-cache.yml's memory-heavy module list moved; update this test")
        self.assertEqual(warm_lists[0], ci_lists[0],
                         "build the same memory-heavy modules one at a time as ci.yml")

    def test_same_build_as_ci(self) -> None:
        self.assertIn("run: scripts/check.sh build", self.ci)
        self.assertIn("scripts/check.sh build", "\n".join(run_blocks(self.warm_lines)))

    def test_same_cache_path_and_key_prefix_as_ci(self) -> None:
        ci_restore = self.ci.split("actions/cache/restore@", 1)[1].split("\n      - ", 1)[0]
        self.assertIn("path: .lake/build", ci_restore)
        self.assertIn(KEY_PREFIX, ci_restore, "ci.yml's restore key changed; update bump-cache.yml and this test")
        self.assertIn(f"PREFIX: {KEY_PREFIX}", self.warm)
        for action in ("actions/cache/restore@", "actions/cache/save@"):
            step = self.warm.split(action, 1)[1].split("\n      - ", 1)[0]
            self.assertIn("path: .lake/build", step, action)

    def test_head_checked_before_it_is_checked_out(self) -> None:
        check = self.warm.index("name: Check the pull request and its head")
        checkout = self.warm.index("uses: actions/checkout@")
        pins = self.warm.index("name: Require new pins")
        build = self.warm.index("name: Build and check the head")
        self.assertLess(check, checkout)
        self.assertLess(checkout, pins)
        self.assertLess(pins, build)


if __name__ == "__main__":
    unittest.main()
