#!/usr/bin/env python3
"""The Autoform index workflow and CI's pull-request indexing check must agree.

`.github/workflows/autoform-index.yml` builds and indexes the root libraries of
`main` once a day; CI's "Check that the libraries can be indexed" step runs the
same generator on every pull request and merge group. If the step selected fewer
libraries than the workflow indexes, a tree the generator refuses could merge
and leave `main` without an index. Both select exactly the package's default
targets in `lakefile.toml`, and both install the generator pinned in
`.github/autoform-ref`.

Run with: python3 -m unittest discover -s scripts -p test_autoform_index_workflow.py
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github" / "workflows"
PIN = 'rev="$(cat .github/autoform-ref)"'
PIN_CHECK = '[[ "$rev" =~ ^[0-9a-f]{40}$ ]]'
INSTALL = '"autoform @ git+https://github.com/facebookresearch/autoform-bot@${rev}"'


def step(workflow: str, name: str) -> str:
    """The text of the step called `name` in `workflow`, up to the next step."""
    text = (WORKFLOWS / workflow).read_text()
    match = re.search(r"^( *)- name: " + re.escape(name) + r"\n(.*?)(?=^\1- |\Z)", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"{workflow} has no step {name!r}")
    return match.group(0)


def selected(text: str) -> list[str]:
    """The libraries an `autoform library index` command in `text` selects with --lib."""
    command = re.search(r"autoform\"? library index \.(.*?)--timeout", text, re.S)
    if command is None:
        raise AssertionError("no `autoform library index .` command")
    return re.findall(r"--lib (\S+)", command.group(1))


def default_targets() -> list[str]:
    match = re.search(r"^defaultTargets = \[(.*)\]$", (ROOT / "lakefile.toml").read_text(), re.M)
    if match is None:
        raise AssertionError("lakefile.toml has no defaultTargets")
    return re.findall(r'"([^"]+)"', match.group(1))


class AutoformIndexWorkflowTests(unittest.TestCase):
    def test_both_select_the_default_targets(self):
        targets = default_targets()
        self.assertTrue(targets)
        published = selected(step("autoform-index.yml", "Write the index"))
        checked = selected(step("ci.yml", "Check that the libraries can be indexed"))
        self.assertEqual(published, targets)
        self.assertEqual(checked, targets)

    def test_the_index_workflow_builds_what_it_indexes(self):
        build = step("autoform-index.yml", "Build the indexed libraries")
        command = re.search(r"run: lake build (.*)$", build, re.M)
        self.assertIsNotNone(command)
        self.assertEqual(command.group(1).split(), default_targets())

    def test_both_install_the_reviewed_pin(self):
        for workflow, name in (("autoform-index.yml", "Install Autoform"),
                               ("ci.yml", "Check that the libraries can be indexed")):
            with self.subTest(workflow=workflow):
                text = step(workflow, name)
                self.assertIn(PIN, text)
                self.assertIn(PIN_CHECK, text)
                self.assertIn(INSTALL, text)
        self.assertRegex((ROOT / ".github" / "autoform-ref").read_text(), r"^[0-9a-f]{40}\n?$")

    def test_ci_checks_pull_requests_and_merge_groups_only(self):
        text = step("ci.yml", "Check that the libraries can be indexed")
        self.assertIn("if: github.event_name == 'pull_request' || github.event_name == 'merge_group'", text)


if __name__ == "__main__":
    unittest.main()
