#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Saved invocation controls; Lean and Lake execution is explicitly mocked."""

from __future__ import annotations

import contextlib
import json
import os
import signal
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_outputs as outputs
import test_import_optimizer_proposal_evidence as proposals
import test_import_optimizer_recovery as recovery


def bind_mock_command(tools: optimizer.Tools, relative: Path, arm: Path,
                      result: dict[str, object]) -> None:
    prefix = Path(result["artifact_root"]) / relative.with_suffix("")
    argv = [str(tools.time_binary), "-f",
            '{"wall_seconds":%e,"user_seconds":%U,"system_seconds":%S,"max_rss_kib":%M}',
            "-o", str(arm / "time.json"), str(tools.lean), f"-j{tools.lean_threads}", "-R",
            str(arm / "source"), str(arm / "source" / relative), "--setup", str(arm / "setup.json"),
            "-o", str(prefix) + ".olean", "-i", str(prefix) + ".ilean", "-c", str(prefix) + ".c"]
    label = arm / "compile"
    stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
    stdout.write_text("External compiler output explicitly mocked\n")
    stderr.write_text("")
    command = {"argv": argv, "cwd": str(tools.root), "exit_code": 0,
               "timed_out": False, "remaining_group_killed": False,
               "stdout": str(stdout), "stderr": str(stderr), "external_compiler_mock": True}
    optimizer.write_json(Path(str(label) + ".json"), command)
    result["command"] = command
    result["command_evidence"] = optimizer.analysis_evidence(tools, label, "compile", {
        "compiler": optimizer.file_pin(tools.lean), "time_binary": optimizer.file_pin(tools.time_binary)})


@contextlib.contextmanager
def external_cli(root: Path, names: tuple[str, ...] = ("A",)):
    fixture = proposals.ChangedProposalEvidenceTests()
    with fixture.external_cli(root, names) as values:
        original = optimizer.compile_arm.side_effect

        def compile_stub(tools, relative, setup, arm, artifact_root=None, source_bytes=None,
                         *, header_is_module=True):
            result = original(tools, relative, setup, arm, artifact_root, source_bytes,
                              header_is_module=header_is_module)
            bind_mock_command(tools, relative, arm, result)
            return result

        with patch.object(optimizer, "compile_arm", side_effect=compile_stub):
            yield values


class SavedCompilerCommandTests(unittest.TestCase):
    def test_forced_compile_pins_actual_command_and_both_streams(self) -> None:
        for name, source in (("baseline", recovery.ORIGINAL), ("candidate", recovery.CANDIDATE)):
            with self.subTest(arm=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                recovery.main_inputs(root, ("A",))
                tools = proposals.ChangedProposalEvidenceTests.tools(root)
                arm = tools.output / name

                def external(argv, label, environment=None):
                    outputs.physical_parts(arm / "artifacts", Path("A.lean"))
                    Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
                    stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                    stdout.write_text("External compiler output explicitly mocked\n")
                    stderr.write_text("")
                    command = {"argv": argv, "cwd": str(root), "exit_code": 0,
                               "timed_out": False, "remaining_group_killed": False,
                               "stdout": str(stdout), "stderr": str(stderr)}
                    optimizer.write_json(Path(str(label) + ".json"), command)
                    return command

                with patch.object(optimizer.Tools, "run", side_effect=external):
                    result = optimizer.compile_arm(tools, Path("A.lean"), root / ".lake/build/ir/A.setup.json",
                                                   arm, source_bytes=source)
                self.assertEqual(len(result["artifacts"]), 7)
                self.assertEqual(Path(result["source_path"]).read_bytes(), source)
                self.assertIsInstance(result.get("command_evidence"), dict)
                evidence = result["command_evidence"]
                self.assertEqual(evidence["kind"], "compile")
                self.assertEqual(evidence["inputs"], {"compiler": optimizer.file_pin(tools.lean),
                                                     "time_binary": optimizer.file_pin(tools.time_binary)})
                for suffix in ("json", "stdout", "stderr"):
                    self.assertEqual(evidence[suffix], optimizer.file_pin(arm / ("compile." + suffix)))
                self.assertEqual(optimizer.read_json(arm / "compile.json"), result["command"])

    def test_single_and_shared_resume_reject_missing_retained_command(self) -> None:
        for names in (("A",), ("A", "B")):
            for name in ("baseline", "candidate"):
                with self.subTest(targets=names, arm=name), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    with external_cli(root, names) as (invoke, _, calls):
                        self.assertEqual(invoke([]), 0)
                        journal = root / "output/results.jsonl"
                        before = journal.read_bytes()
                        rows = [json.loads(line) for line in before.splitlines()]
                        self.assertEqual([row["status"] for row in rows], ["verified"] * len(names))
                        self.assertTrue(all(row["declaration_count"] == 1 for row in rows))
                        self.assertEqual(invoke(["--resume"]), 0)
                        prior_calls = list(calls)
                        (Path(rows[0]["attempt_directory"]) / name / "compile.json").unlink()
                        with self.assertRaises((ValueError, OSError)):
                            invoke(["--resume"])
                        self.assertEqual(calls, prior_calls)
                        self.assertEqual(journal.read_bytes(), before)

    def test_standalone_saved_check_rejects_changed_measurement_executable_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with external_cli(root) as (invoke, _, calls):
                self.assertEqual(invoke([]), 0)
                result = json.loads((root / "output/results.jsonl").read_bytes())
                tools = proposals.ChangedProposalEvidenceTests.tools(root)
                optimizer.verify_saved_candidate(result, tools.output, tools)
                before = list(calls)
                tools.time_binary.write_text("Changed measurement executable bytes\n")
                with self.assertRaises((ValueError, OSError)):
                    optimizer.verify_saved_candidate(result, tools.output, tools)
                self.assertEqual(calls, before)

    def test_resume_rejects_changed_streams_and_detached_embedded_command(self) -> None:
        for name in ("baseline", "candidate"):
            for mutation in ("json", "stdout", "stderr", "embedded", "missing_evidence"):
                with self.subTest(arm=name, mutation=mutation), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    with external_cli(root) as (invoke, _, calls):
                        self.assertEqual(invoke([]), 0)
                        journal = root / "output/results.jsonl"
                        result = json.loads(journal.read_bytes())
                        arm = Path(result["attempt_directory"]) / name
                        if mutation == "embedded":
                            result[name]["command"] = {"exit_code": 0, "timed_out": False,
                                                       "remaining_group_killed": False}
                            journal.write_text(json.dumps(result) + "\n")
                        elif mutation == "missing_evidence":
                            del result[name]["command_evidence"]
                            journal.write_text(json.dumps(result) + "\n")
                        else:
                            target = arm / ("compile." + mutation)
                            target.write_bytes(target.read_bytes() + b"Changed saved compiler evidence\n")
                        before, prior_calls = journal.read_bytes(), list(calls)
                        with self.assertRaises((ValueError, OSError)):
                            invoke(["--resume"])
                        self.assertEqual(calls, prior_calls)
                        self.assertEqual(journal.read_bytes(), before)

    def test_repinned_invocation_must_match_all_validated_arm_paths(self) -> None:
        mutations = ("timer", "format", "timing", "compiler", "threads", "source_root", "source",
                     "setup", "olean", "ilean", "c", "extra", "missing_argv", "cwd", "stdout", "stderr")
        for name in ("baseline", "candidate"):
            for mutation in mutations:
                with self.subTest(arm=name, mutation=mutation), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    with external_cli(root) as (invoke, _, calls):
                        self.assertEqual(invoke([]), 0)
                        journal = root / "output/results.jsonl"
                        result = json.loads(journal.read_bytes())
                        arm = Path(result["attempt_directory"]) / name
                        command = optimizer.read_json(arm / "compile.json")
                        argv = command["argv"]
                        indices = {"timer": 0, "format": 2, "timing": 4, "compiler": 5,
                                   "threads": 6, "source_root": 8, "source": 9, "setup": 11,
                                   "olean": 13, "ilean": 15, "c": 17}
                        if mutation in indices:
                            argv[indices[mutation]] = str(root / "wrong")
                        elif mutation == "extra":
                            argv.append("--trust=2")
                        elif mutation == "missing_argv":
                            del command["argv"]
                        else:
                            command[mutation] = str(root / "wrong")
                        optimizer.write_json(arm / "compile.json", command)
                        result[name]["command"] = command
                        result[name]["command_evidence"]["json"] = optimizer.file_pin(arm / "compile.json")
                        journal.write_text(json.dumps(result) + "\n")
                        before, prior_calls = journal.read_bytes(), list(calls)
                        with self.assertRaises((ValueError, OSError)):
                            invoke(["--resume"])
                        self.assertEqual(calls, prior_calls)
                        self.assertEqual(journal.read_bytes(), before)

    def test_clean_nonzero_bulk_can_fallback_but_unclean_nonzero_cannot(self) -> None:
        real_command = optimizer.run_command
        for code, flag in ((37, None), (37, "remaining_group_killed"), (124, "timed_out")):
            with self.subTest(exit_code=code, flag=flag), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with external_cli(root) as (invoke, analyzed, calls):
                    original = optimizer.Tools.run.side_effect
                    observed = []

                    def external(argv, label, environment=None):
                        result = original(argv, label, environment)
                        if "build" in argv and "--no-build" not in argv:
                            script = "print('clean nonzero child',flush=True);raise SystemExit(37)"
                            if flag == "remaining_group_killed":
                                script = ("import subprocess,sys;"
                                          "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)']);"
                                          "print('unfinished descendant',p.pid,flush=True);raise SystemExit(37)")
                            elif flag == "timed_out":
                                script = ("import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);"
                                          "print('timeout child started',flush=True);time.sleep(30)")
                            real_killpg = optimizer.os.killpg
                            cleanup_signals = []

                            def observed_killpg(group, cleanup_signal):
                                event = {"group": group, "signal": int(cleanup_signal)}
                                if flag == "timed_out" and cleanup_signal == signal.SIGKILL:
                                    event["leader_exited_before_kill"] = (
                                        optimizer._owned_child_exited_without_reaping(group))
                                try:
                                    real_killpg(group, cleanup_signal)
                                except ProcessLookupError:
                                    cleanup_signals.append({**event, "succeeded": False})
                                    raise
                                cleanup_signals.append({**event, "succeeded": True})

                            with patch.object(optimizer.os, "killpg", side_effect=observed_killpg):
                                result = real_command([sys.executable, "-c", script], root, label,
                                                      dict(os.environ), 1 if flag == "timed_out" else 5)
                            self.assertEqual(result["exit_code"], code)
                            self.assertIs(result["timed_out"], flag == "timed_out")
                            if flag == "timed_out":
                                # TERM is ignored, so KILL must reach the same live, unreaped owned leader.
                                self.assertEqual([event["signal"] for event in cleanup_signals],
                                                 [signal.SIGTERM, signal.SIGKILL])
                                self.assertTrue(all(event["succeeded"] for event in cleanup_signals))
                                self.assertIs(cleanup_signals[-1]["leader_exited_before_kill"], False)
                                killed = any(event["signal"] == signal.SIGKILL and event["succeeded"]
                                             for event in cleanup_signals)
                                self.assertIs(result["remaining_group_killed"], killed)
                            else:
                                self.assertIs(result["remaining_group_killed"], flag == "remaining_group_killed")
                            observed.append({"command": result, "cleanup_signals": cleanup_signals,
                                             "stdout": Path(result["stdout"]).read_text(),
                                             "stderr": Path(result["stderr"]).read_text()})
                            print(json.dumps({"bulk_external_replacement_python_control": observed}),
                                  file=sys.__stdout__)
                        return result

                    with patch.object(optimizer.Tools, "run", side_effect=external):
                        self.assertEqual(invoke([]), 1 if flag else 0,
                                         (root / "output/results.jsonl").read_text())
                    result = json.loads((root / "output/results.jsonl").read_text())
                    self.assertEqual(result["status"], "blocked" if flag else "verified")
                    self.assertEqual([kind for kind, _ in calls].count("prepare"), 1 if flag else 2)
                    self.assertEqual(len(analyzed), 0 if flag else 1)
                    if flag:
                        self.assertIn("completion", result["error"])
                        self.assertEqual(calls, [("prepare", ["A"])])


class CompilerPathComponentTests(unittest.TestCase):
    def compile_shared_dependency(self, root: Path, *, mutation: str):
        recovery.main_inputs(root, ("A",))
        tools = proposals.ChangedProposalEvidenceTests.tools(root)
        canonical, shadow = root / "canonical-package", root / "shadow-package"
        for package, content in ((canonical, b"canonical dependency\n"),
                                 (shadow, b"shadow dependency\n")):
            outputs.physical_parts(package, Path("Mathlib.lean"))
            (package / "Mathlib.olean").write_bytes(content)
        alias = root / ".lake/packages/shared"
        alias.parent.mkdir(parents=True, exist_ok=True)
        alias.symlink_to(canonical, target_is_directory=True)
        setup = root / ".lake/build/ir/A.setup.json"
        metadata = optimizer.read_json(setup)
        metadata["importArts"] = {"Mathlib": [[str(alias / "Mathlib.olean")], []]}
        optimizer.write_json(setup, metadata)
        original = optimizer.source_identity(canonical / "Mathlib.olean")
        arm = tools.output / "baseline"
        shadow_arm = root / "shadow-arm"
        (shadow_arm / "source").mkdir(parents=True)
        (shadow_arm / "source/A.lean").write_bytes(b"shadow source\n")
        optimizer.write_json(shadow_arm / "setup.json", metadata)
        observations = []
        script = r"""
import json, sys
from pathlib import Path
setup, alias, shadow, prefix, timing = map(Path, sys.argv[1:6])
mutation = sys.argv[6]
suffixes = json.loads(sys.argv[7])
shadow_arm = Path(sys.argv[8])
arm = setup.parent
retained = alias.with_name(alias.name + "-retained")
retained_arm = arm.with_name(arm.name + "-retained")
target = str(alias.readlink())
if mutation == "dependency":
    alias.rename(retained)
    alias.symlink_to(shadow, target_is_directory=True)
elif mutation == "arm":
    arm.rename(retained_arm)
    shadow_arm.rename(arm)
try:
    path = (arm / "source/A.lean" if mutation == "arm" else
            Path(json.loads(setup.read_text())["importArts"]["Mathlib"][0][0]))
    consumed = path.read_bytes()
finally:
    if mutation == "dependency":
        alias.unlink()
        retained.rename(alias)
    elif mutation == "arm":
        arm.rename(shadow_arm)
        retained_arm.rename(arm)
for suffix in suffixes:
    Path(str(prefix) + suffix).write_bytes(b"compiled with " + consumed)
timing.write_text('{"wall_seconds":0}\n')
print(json.dumps({"consumed": consumed.decode(), "alias_restored": str(alias.readlink()) == target}))
"""

        def external(argv, label, environment=None):
            source_identity = optimizer.source_identity(arm / "source/A.lean")
            command = optimizer.run_command(
                [sys.executable, "-c", script, argv[argv.index("--setup") + 1],
                 str(alias), str(shadow), str(arm / "artifacts/A"), str(arm / "time.json"),
                 mutation, json.dumps(optimizer.ARTIFACT_SUFFIXES), str(shadow_arm)],
                root, label, dict(os.environ), 5)
            optimizer.require_success(command)
            observed = optimizer.read_json(Path(command["stdout"]))
            expected = {"dependency": "shadow dependency\n", "arm": "shadow source\n",
                        "none": "canonical dependency\n"}
            self.assertEqual(observed["consumed"], expected[mutation])
            self.assertTrue(observed["alias_restored"])
            self.assertEqual(optimizer.source_identity(canonical / "Mathlib.olean"), original)
            self.assertEqual(optimizer.source_identity(arm / "source/A.lean"), source_identity)
            observations.append({"command": command, "stdout": observed})
            command = {**command, "argv": argv, "python_mock_command": command}
            optimizer.write_json(Path(str(label) + ".json"), command)
            return command

        try:
            with patch.object(optimizer.Tools, "run", side_effect=external):
                result = optimizer.compile_arm(tools, Path("A.lean"), setup, arm,
                                               source_bytes=recovery.ORIGINAL)
        except ValueError as error:
            print(json.dumps({"compiler_path_component_control": observations,
                              "accepted": False, "error": str(error)}), file=sys.__stdout__)
            raise
        print(json.dumps({"compiler_path_component_control": observations, "accepted": True}),
              file=sys.__stdout__)
        return result

    def test_compiler_rejects_restored_dependency_directory_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "Compilation input path identity changed"):
                self.compile_shared_dependency(Path(directory).resolve(), mutation="dependency")

    def test_compiler_rejects_restored_output_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "Compilation input path identity changed"):
                self.compile_shared_dependency(Path(directory).resolve(), mutation="arm")

    def test_stable_shared_package_symlink_allows_new_compiler_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            result = self.compile_shared_dependency(root, mutation="none")
            self.assertEqual(len(result["artifacts"]), 7)
            self.assertEqual((root / "output/baseline/artifacts/A.c").read_bytes(),
                             b"compiled with canonical dependency\n")


if __name__ == "__main__":
    unittest.main()
