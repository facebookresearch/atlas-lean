#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Lean thread and Lake job controls.

Lean and Lake are mocked, except for one real child process that reports the
arguments and environment it received.
"""

from __future__ import annotations

import ast
import contextlib
import io
import json
import os
import re
import sys
import tempfile
import unittest
from collections.abc import Iterator
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_compiler_commands as compiler_commands
import test_import_optimizer_evidence as evidence
import test_import_optimizer_recovery as recovery

HELPERS = Path(optimizer.__file__).resolve().parent / "import_optimizer"


def saved_commands(output: Path) -> list[list[str]]:
    """Every command receipt the run saved, read back from disk."""
    commands = []
    for path in sorted(output.rglob("*.json")):
        value = json.loads(path.read_text())
        if isinstance(value, dict) and isinstance(value.get("argv"), list):
            commands.append(value["argv"])
    return commands


def lean_thread_arguments(source: str) -> list[str]:
    arguments = []
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.List):
            for index, element in enumerate(node.elts):
                if ast.unparse(element) == "str(tools.lean)":
                    arguments.append(ast.unparse(node.elts[index + 1])
                                     if index + 1 < len(node.elts) else "<missing>")
    return arguments


class ThreadArgumentTests(unittest.TestCase):
    def test_cli_rejects_invalid_counts_before_any_output_or_child(self) -> None:
        invalid = ("0", "-1", "01", "+2", " 2", "1.5", "abc", "", "\u0663", "1025", "99999999999")
        for flag in ("--lean-threads", "--lake-jobs"):
            for value in invalid:
                with self.subTest(flag=flag, value=value), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arguments = recovery.main_inputs(root, ("A",))
                    child = AssertionError("Invalid thread settings started a child process")
                    with patch.object(sys, "argv", [*arguments, f"{flag}={value}"]), \
                            patch.object(optimizer, "run_command", side_effect=child), \
                            patch.object(optimizer.Tools, "run", side_effect=child), \
                            contextlib.redirect_stderr(io.StringIO()) as stderr, \
                            self.assertRaises(SystemExit) as raised:
                        optimizer.main()
                    self.assertEqual(raised.exception.code, 2)
                    self.assertIn(flag, stderr.getvalue())
                    self.assertFalse((root / "output").exists())
                    self.assertEqual(list((root / ".lake").glob("lakefile-lean-*.toml")), [])

    def test_every_lean_command_takes_the_configured_thread_argument(self) -> None:
        # Covers command sites the mocked runs below do not reach (private
        # imports, legacy and header helpers): no hardcoded thread count.
        source = Path(optimizer.__file__).read_text()
        arguments = lean_thread_arguments(source)
        self.assertGreaterEqual(len(arguments), 17)
        self.assertEqual(set(arguments), {"tools.lean_thread_argument"})
        self.assertIsNone(re.search(r"[\"']-j[0-9]", source))
        self.assertNotIn('LEAN_NUM_THREADS"] = "', source)

    def test_command_scan_ignores_cache_keys_but_keeps_bad_or_missing_flags(self) -> None:
        source = '''
key = (str(tools.lean), tuple(sorted(tools.environment.items())))
good = [str(tools.lean), tools.lean_thread_argument]
bad = [str(tools.lean), "-j2"]
missing = [str(tools.lean)]
'''
        self.assertEqual(lean_thread_arguments(source),
                         ["tools.lean_thread_argument", repr("-j2"), "<missing>"])

    def test_cli_accepts_the_bounds(self) -> None:
        self.assertEqual(optimizer.thread_count_argument("1"), 1)
        self.assertEqual(optimizer.thread_count_argument("1024"), 1024)

    def test_tools_reject_invalid_counts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            recovery.main_inputs(root, ("A",))
            for field in ("lean_threads", "lake_jobs"):
                for value in (0, -1, 1025, True, 2.0, "2", None):
                    with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                        optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                        HELPERS, {}, 5, root / "bin/time", **{field: value})

    def test_saved_fixture_view_keeps_thread_settings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            recovery.main_inputs(root, ("A",))
            tools = optimizer.Tools(root, root, root / "bin/lake", root / "bin/lean", HELPERS, {}, 5,
                                    root / "bin/time", lean_threads=7, lake_jobs=3)
            view = optimizer.computation_paths_without_output(tools)
            self.assertNotEqual(view.output, tools.output)
            self.assertEqual((view.lean_threads, view.lake_jobs, view.lean_thread_argument),
                             (7, 3, "-j7"))

    def test_bounded_lake_config_is_separate_per_lean_thread_count(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / ".lake").mkdir()
            (root / "lakefile.toml").write_bytes(b'name = "fixture"\n\n[[lean_lib]]\nname = "A"\n')
            default = optimizer.bounded_lake_config(root)
            self.assertEqual(default, root / ".lake/lakefile-lean-j2.toml")
            self.assertEqual(default.read_bytes(),
                             b'name = "fixture"\nmoreLeanArgs = ["-j2"]\n\n[[lean_lib]]\nname = "A"\n')
            before = default.read_bytes()
            custom = optimizer.bounded_lake_config(root, 6)
            self.assertEqual(custom, root / ".lake/lakefile-lean-j6.toml")
            self.assertEqual(custom.read_bytes(),
                             b'name = "fixture"\nmoreLeanArgs = ["-j6"]\n\n[[lean_lib]]\nname = "A"\n')
            self.assertEqual(default.read_bytes(), before)
            for value in (0, True, 1025):
                with self.subTest(value=value), self.assertRaises(ValueError):
                    optimizer.bounded_lake_config(root, value)

    def test_real_child_receives_lean_threads_and_lake_jobs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            recovery.main_inputs(root, ("A",))
            lean = root / "bin/lean"
            lean.write_text(f"#!{sys.executable}\nimport json, os, sys\n"
                            "print(json.dumps({'argv': sys.argv[1:], "
                            "'threads': os.environ.get('LEAN_NUM_THREADS')}))\n")
            lean.chmod(0o755)
            # A stale caller value must not reach the child.
            environment = {"PATH": os.environ.get("PATH", ""), "LEAN_NUM_THREADS": "1"}
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", lean, HELPERS,
                                    environment, 30, root / "bin/time", lean_threads=5, lake_jobs=3)
            for name, override in (("inherited", None), ("override", {**environment, "LEAN_PATH": ""})):
                with self.subTest(environment=name):
                    command = tools.run([str(lean), tools.lean_thread_argument, "--version"],
                                        root / "output" / name, override)
                    optimizer.require_success(command)
                    received = json.loads(Path(str(command["stdout"])).read_text())
                    self.assertEqual(received, {"argv": ["-j5", "--version"], "threads": "3"})
            self.assertEqual(environment["LEAN_NUM_THREADS"], "1")


class ThreadSettingRunTests(unittest.TestCase):
    @contextlib.contextmanager
    def run_fixture(self, root: Path, names: tuple[str, ...] = ("A", "B")
                    ) -> Iterator[tuple[object, list[tuple[str, object]], list[dict[str, str]]]]:
        environments: list[dict[str, str]] = []

        def capture_environment(argv, cwd, label, environment, timeout):
            environments.append(dict(environment))
            return recovery.environment_stub(argv, cwd, label, environment, timeout)

        with compiler_commands.external_cli(root, names) as (invoke, _, calls), \
                patch.object(optimizer, "run_command", side_effect=capture_environment):
            yield invoke, calls, environments

    def assert_commands_use(self, root: Path, lean_threads: int) -> set[str]:
        lean, lake = str(root / "bin/lean"), str(root / "bin/lake")
        config = str(root / f".lake/lakefile-lean-j{lean_threads}.toml")
        kinds = set()
        for argv in saved_commands(root / "output"):
            flags = {word for word in argv if re.fullmatch(r"-j[0-9]+", word)}
            self.assertLessEqual(flags, {f"-j{lean_threads}"}, argv)
            if lean in argv:
                index = argv.index(lean)
                self.assertEqual(argv[index + 1], f"-j{lean_threads}", argv)
                kinds.add("compile" if "-R" in argv else "deps" if "--deps" in argv else "run")
            elif argv[0] == lake:
                self.assertEqual(argv[1:4], ["--no-cache", "-f", config], argv)
                kinds.add("shake" if "shake" in argv else "build")
        return kinds

    def test_default_run_keeps_existing_settings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.run_fixture(root) as (invoke, _, environments):
                self.assertEqual(invoke([]), 0)
            run = optimizer.read_json(root / "output/run.json")
            self.assertEqual((run["lean_threads"], run["lake_scheduler_threads"]), (2, 1))
            config = root / ".lake/lakefile-lean-j2.toml"
            self.assertEqual(run["effective_lake_config_sha256"], optimizer.sha256(config))
            self.assertIn(b'moreLeanArgs = ["-j2"]\n', config.read_bytes())
            self.assertEqual(self.assert_commands_use(root, 2),
                             {"compile", "deps", "run", "shake", "build"})
            self.assertEqual([value["LEAN_NUM_THREADS"] for value in environments], ["1"])

    def test_nondefault_singleton_run_propagates(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.run_fixture(root, ("A",)) as (invoke, _, environments):
                self.assertEqual(invoke(["--lean-threads", "5", "--lake-jobs", "3"]), 0)
                self.assertEqual(invoke(["--lean-threads", "5", "--lake-jobs", "3", "--resume"]), 0)
            row, = [json.loads(line) for line in (root / "output/results.jsonl").read_bytes().splitlines()]
            self.assertEqual(row["status"], "verified")
            self.assertEqual(self.assert_commands_use(root, 5),
                             {"compile", "deps", "run", "shake", "build"})
            self.assertEqual([value["LEAN_NUM_THREADS"] for value in environments], ["3", "3"])

    def test_nondefault_legacy_evidence_is_bound_to_lean_threads(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = recovery.main_inputs(root, ("A",))
            evidence.AnalysisResumeTests.change_source(root, recovery.ORIGINAL.removeprefix(b"module\n"), False)
            fixture = evidence.AnalysisResumeTests()
            with fixture.external_cli(root, {"A"}, []):
                self.assertEqual(fixture.invoke([*arguments, "--lean-threads", "5", "--lake-jobs", "3"]), 0)
                row = json.loads((root / "output/results.jsonl").read_bytes())
                self.assertEqual(row["status"], "no_change")
                self.assertEqual(self.assert_commands_use(root, 5), {"run", "build"})
                saved = optimizer.read_json(root / "output/environment.stdout")
                for lean_threads, accepted in ((5, True), (4, False)):
                    tools = optimizer.Tools(
                        root, root / "output", root / "bin/lake", root / "bin/lean", HELPERS,
                        {"LEAN_NUM_THREADS": "3", **saved}, 5, root / "bin/time",
                        root / ".lake/lakefile-lean-j5.toml", lean_threads=lean_threads, lake_jobs=3)
                    with self.subTest(lean_threads=lean_threads):
                        if accepted:
                            optimizer.verify_saved_no_change(row, tools)
                        else:
                            with self.assertRaises(ValueError):
                                optimizer.verify_saved_no_change(row, tools)

    def test_nondefault_run_propagates_and_changed_resume_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            settings = ["--lean-threads", "5", "--lake-jobs", "3"]
            with self.run_fixture(root) as (invoke, calls, environments):
                self.assertEqual(invoke(settings), 0)
                journal = root / "output/results.jsonl"
                before = journal.read_bytes()
                rows = [json.loads(line) for line in before.splitlines()]
                self.assertEqual([row["status"] for row in rows], ["verified", "verified"])
                run = optimizer.read_json(root / "output/run.json")
                config = root / ".lake/lakefile-lean-j5.toml"
                self.assertEqual((run["lean_threads"], run["lake_scheduler_threads"]), (5, 3))
                self.assertEqual(run["effective_lake_config_sha256"], optimizer.sha256(config))
                self.assertIn(b'moreLeanArgs = ["-j5"]\n', config.read_bytes())
                self.assertFalse((root / ".lake/lakefile-lean-j2.toml").exists())
                self.assertEqual(self.assert_commands_use(root, 5),
                                 {"compile", "deps", "run", "shake", "build"})
                self.assertEqual([value["LEAN_NUM_THREADS"] for value in environments], ["3"])
                analysis = optimizer.read_json(root / "output/batches/0/analysis.json")
                self.assertEqual((analysis["inputs"]["lean_threads"], analysis["inputs"]["lake_jobs"]),
                                 (5, 3))

                self.assertEqual(invoke(settings + ["--resume"]), 0)
                self.assertEqual(journal.read_bytes(), before)
                prior_calls, prior_environments = list(calls), len(environments)

                for changed in ([], ["--lean-threads", "4", "--lake-jobs", "3"],
                                ["--lean-threads", "5", "--lake-jobs", "4"], ["--lake-jobs", "3"]):
                    with self.subTest(early_guard=changed), \
                            self.assertRaisesRegex(ValueError, "Resume thread settings differ"):
                        invoke([*changed, "--resume"])
                    self.assertEqual(calls, prior_calls)
                    self.assertEqual(len(environments), prior_environments)
                    self.assertEqual(journal.read_bytes(), before)
                self.assertFalse((root / ".lake/lakefile-lean-j2.toml").exists())
                self.assertFalse((root / ".lake/lakefile-lean-j4.toml").exists())

                # Without the early guard, the full run identity still rejects
                # either changed setting before any build or analysis child.
                with patch.object(optimizer, "verify_resume_thread_settings"):
                    for changed in (["--lean-threads", "4", "--lake-jobs", "3"],
                                    ["--lean-threads", "5", "--lake-jobs", "4"]):
                        with self.subTest(identity=changed), \
                                self.assertRaisesRegex(ValueError, "Resume inputs"):
                            invoke([*changed, "--resume"])
                        self.assertEqual(calls, prior_calls)
                        self.assertEqual(journal.read_bytes(), before)

    def test_saved_evidence_rejects_tools_with_other_thread_settings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.run_fixture(root) as (invoke, _, _):
                self.assertEqual(invoke(["--lean-threads", "5", "--lake-jobs", "3"]), 0)
                rows = [json.loads(line) for line in
                        (root / "output/results.jsonl").read_bytes().splitlines()]
                saved = optimizer.read_json(root / "output/environment.stdout")

                def tools(lean_threads: int, lake_jobs: int, config_threads: int) -> optimizer.Tools:
                    return optimizer.Tools(
                        root, root / "output", root / "bin/lake", root / "bin/lean", HELPERS,
                        {"LEAN_NUM_THREADS": str(lake_jobs), **saved}, 5, root / "bin/time",
                        root / f".lake/lakefile-lean-j{config_threads}.toml",
                        lean_threads=lean_threads, lake_jobs=lake_jobs)

                def verify(candidate: optimizer.Tools) -> None:
                    with optimizer.analysis_validation_phase(candidate):
                        for row in rows:
                            optimizer.verify_saved_candidate(row, root / "output", candidate)

                verify(tools(5, 3, 5))
                optimizer.bounded_lake_config(root, 4)
                for lean_threads, lake_jobs, config_threads in ((4, 3, 5), (4, 3, 4), (5, 4, 5)):
                    with self.subTest(lean_threads=lean_threads, lake_jobs=lake_jobs,
                                      config_threads=config_threads), self.assertRaises(ValueError):
                        verify(tools(lean_threads, lake_jobs, config_threads))


if __name__ == "__main__":
    unittest.main()
