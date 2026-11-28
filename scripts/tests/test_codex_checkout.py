#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.
"""Exercise the actual Codex checkout/guide steps against local filtered Git servers."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

WORKFLOW = Path(os.environ.get(
    "ATLAS_CODEX_TEST_WORKFLOW",
    Path(__file__).resolve().parents[2] / ".github/workflows/codex.yml",
))


def run(argv, cwd, env=None):
    result = subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True)
    if result.returncode:
        raise AssertionError(
            f"Command failed ({result.returncode}): {argv}\n{result.stderr}"
        )
    return result.stdout.strip()


def step_script(workflow, name):
    lines = workflow.splitlines()
    start = next(i for i, line in enumerate(lines) if line == f"      - name: {name}")
    end = next(
        (i for i in range(start + 1, len(lines)) if lines[i].startswith("      - name:")),
        len(lines),
    )
    run_line = next(i for i in range(start, end) if lines[i] == "        run: |")
    return "\n".join(line[10:] for line in lines[run_line + 1:end]) + "\n"


class CodexFilteredBaseFetchTest(unittest.TestCase):
    def test_full_review_scope_without_deleted_historical_blob(self):
        workflow = WORKFLOW.read_text()
        checkout = step_script(workflow, "Checkout request target")
        guide = step_script(workflow, "Load trusted review guide")
        filtered = 'git fetch --no-tags --filter=blob:none '
        self.assertIn(filtered, checkout)
        self.assertIn(filtered, guide)
        self.assertNotIn("--depth", checkout + guide)
        self.assertIn('git show "$BASE_SHA:REVIEWING.md"', guide)
        self.assertIn('max_kib=2097152', workflow)
        self.assertIn('"$BASE_SHA"...HEAD', workflow)

        # Substitute only the public transport URLs; execute the real step bodies.
        head_url = '"https://github.com/${TARGET_REPO}.git"'
        base_url = '"https://github.com/${{ github.repository }}.git"'
        self.assertIn(head_url, checkout)
        self.assertIn(base_url, guide)
        checkout = checkout.replace(head_url, '"$ATLAS_TEST_HEAD_URL"')
        guide = guide.replace(base_url, '"$ATLAS_TEST_BASE_URL"')
        unfiltered = guide.replace(
            'git fetch --no-tags --filter=blob:none ', 'git fetch --no-tags ', 1
        )

        for fork in (False, True):
            with self.subTest(fork=fork), tempfile.TemporaryDirectory(
                prefix="atlas-codex-checkout-"
            ) as directory:
                root = Path(directory)
                environment = {
                    "PATH": os.environ["PATH"],
                    "LANG": "C",
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_CONFIG_GLOBAL": os.devnull,
                    "GIT_TERMINAL_PROMPT": "0",
                    "GIT_ALLOW_PROTOCOL": "file",
                    "GIT_CONFIG_COUNT": "1",
                    "GIT_CONFIG_KEY_0": "pack.threads",
                    "GIT_CONFIG_VALUE_0": "1",
                }

                def git(*args, cwd):
                    return run(["git", *args], cwd, environment)

                source = root / "source"
                source.mkdir()
                git("init", "-q", "-b", "main", cwd=source)
                git("config", "user.name", "Checkout regression", cwd=source)
                git("config", "user.email", "checkout-test@example.invalid", cwd=source)
                git("config", "commit.gpgsign", "false", cwd=source)
                git("config", "core.hooksPath", os.devnull, cwd=source)

                def commit(message):
                    git("add", "-A", cwd=source)
                    git("commit", "-qm", message, cwd=source)
                    return git("rev-parse", "HEAD", cwd=source)

                (source / "REVIEWING.md").write_text("Trusted common guide.\n")
                (source / "source.txt").write_text("common\n")
                commit("common history")
                # Incompressible but modest: one MiB, only in an intermediate tree.
                (source / "retired.bin").write_bytes(os.urandom(1024 * 1024))
                commit("temporary historical payload")
                blob = git("rev-parse", "HEAD:retired.bin", cwd=source)
                (source / "retired.bin").unlink()
                common = commit("remove historical payload")
                git("checkout", "-qb", "pull-request", cwd=source)
                (source / "source.txt").write_text("pull request\n")
                (source / "REVIEWING.md").write_text("Untrusted head instructions.\n")
                head = commit("pull request changes")
                git("checkout", "-q", "main", cwd=source)
                trusted_guide = "Trusted advanced-base guide.\n"
                (source / "REVIEWING.md").write_text(trusted_guide)
                (source / "base-only.txt").write_text("advanced main only\n")
                base = commit("main advances after the PR branches")
                expected = git(
                    "diff", "--no-ext-diff", "--no-textconv", "--find-renames",
                    f"{base}...{head}", cwd=source,
                )
                self.assertNotIn("base-only.txt", expected)
                self.assertEqual(git("merge-base", base, head, cwd=source), common)

                def server(path, reference):
                    path.mkdir()
                    git("init", "-q", "--bare", cwd=path)
                    git("config", "uploadpack.allowFilter", "true", cwd=path)
                    git("config", "uploadpack.allowAnySHA1InWant", "true", cwd=path)
                    git("push", "-q", path.as_uri(),
                        f"{reference}:refs/heads/main", cwd=source)
                    return path.as_uri()

                base_server = root / "base.git"
                base_uri = server(base_server, base)
                if fork:
                    head_uri = server(root / "fork.git", head)
                else:
                    git("push", "-q", base_uri,
                        f"{head}:refs/heads/pull-request", cwd=source)
                    head_uri = base_uri

                results = {}
                # The control reproduces the old unfiltered-base behavior.
                for label, guide_script in (("control", unfiltered), ("filtered", guide)):
                    review = root / label
                    review.mkdir()
                    temporary = root / f"{label}-io"
                    temporary.mkdir()
                    env = dict(environment, TARGET_REPO="test/source", TARGET_REF=head,
                               BASE_SHA=base, RUNNER_TEMP=str(temporary),
                               ATLAS_TEST_HEAD_URL=head_uri, ATLAS_TEST_BASE_URL=base_uri)
                    run(["bash", "-euo", "pipefail", "-c", checkout], review, env)
                    run(["bash", "-euo", "pipefail", "-c", guide_script], review, env)
                    self.assertEqual((temporary / "REVIEWING.md").read_text(), trusted_guide)
                    self.assertEqual(git("rev-parse", "HEAD", cwd=review), head)
                    self.assertEqual(git("merge-base", base, "HEAD", cwd=review), common)
                    self.assertEqual(git("rev-parse", "--is-shallow-repository",
                                         cwd=review), "false")
                    actual = git("diff", "--no-ext-diff", "--no-textconv", "--find-renames",
                                 f"{base}...HEAD", cwd=review)
                    self.assertEqual(actual, expected)
                    missing = git("rev-list", "--objects", "--missing=print",
                                  base, "HEAD", cwd=review).splitlines()
                    results[label] = any(line == f"?{blob}" for line in missing)
                self.assertFalse(results["control"], "control must fetch the historical blob")
                self.assertTrue(results["filtered"], "filtered base must omit historical blobs")


if __name__ == "__main__":
    unittest.main()
