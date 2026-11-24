#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Command completion controls; Python children are real, Lean/Lake are mocked."""

from __future__ import annotations

import json
import os
import signal
import sys
import subprocess
import textwrap
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_proposal_evidence as proposals
import test_import_optimizer_recovery as recovery


def clean_status() -> dict[str, object]:
    return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False,
            "stderr": "Explicit external command mock"}


class CommandCompletionTests(unittest.TestCase):
    def test_real_zero_exit_requires_descendants_to_finish(self) -> None:
        for waited in (False, True):
            with self.subTest(waited=waited), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                source = (
                    "import json,os,subprocess,sys;"
                    "p=subprocess.Popen([sys.executable,'-c',"
                    + repr("import time;time.sleep(0.05)" if waited else "import time;time.sleep(30)")
                    + "]);print(json.dumps({'complete':True,'pid':p.pid,'pgid':os.getpgrp()}),flush=True);"
                    + ("p.wait()" if waited else "")
                )
                result = optimizer.run_command([sys.executable, "-c", source], root,
                                               root / "command", dict(os.environ), 5)
                child = json.loads((root / "command.stdout").read_text())
                try:
                    self.assertTrue(child["complete"])
                    self.assertEqual(result["exit_code"], 0)
                    self.assertIs(result["timed_out"], False)
                    self.assertIs(result["remaining_group_killed"], not waited)
                    if waited:
                        optimizer.require_success(result)
                    else:
                        with self.assertRaisesRegex(ValueError, "completion"):
                            optimizer.require_success(result)
                finally:
                    if recovery.live(child["pid"]):
                        self.assertNotEqual(child["pgid"], os.getpgrp())
                        self.assertEqual(os.getpgid(child["pid"]), child["pgid"])
                        os.killpg(child["pgid"], signal.SIGKILL)
                    self.assertFalse(recovery.live(child["pid"]))

    @unittest.skipUnless(sys.platform.startswith("linux"), "Private subreaper fixture requires Linux")
    def test_remaining_orphans_are_rejected_for_zero_and_nonzero_exit(self) -> None:
        for intended_exit in (0, 37):
            with self.subTest(intended_exit=intended_exit), tempfile.TemporaryDirectory() as directory:
                worker = textwrap.dedent(r"""
                    import ctypes,json,os,signal,subprocess,sys
                    from pathlib import Path
                    from unittest.mock import patch
                    sys.path.insert(0,sys.argv[1])
                    import optimize_imports as optimizer
                    if ctypes.CDLL(None).prctl(36,1,0,0,0) != 0:
                        raise RuntimeError("Private fixture subreaper unavailable")
                    root=Path(sys.argv[2]); intended_exit=int(sys.argv[3])
                    release=root/"release"; os.mkfifo(release)
                    label=root/"command"; evidence={}
                    real_wait=subprocess.Popen.wait; real_killpg=os.killpg
                    def identity(pid: int) -> dict[str, object]:
                        raw=Path(f"/proc/{pid}/stat").read_text()
                        fields=raw[raw.rindex(")")+2:].split()
                        return {"pid":pid,"state":fields[0],"ppid":int(fields[1]),
                                "pgid":int(fields[2]),"start_ticks":int(fields[19])}
                    orphan_source=(
                        "import json,os,sys;from pathlib import Path;"
                        "raw=Path('/proc/self/stat').read_text();"
                        "fields=raw[raw.rindex(')')+2:].split();"
                        "os.write(int(sys.argv[2]),json.dumps({'pid':os.getpid(),"
                        "'pgid':os.getpgrp(),'start_ticks':int(fields[19])}).encode());"
                        "os.close(int(sys.argv[2]));"
                        "f=open(sys.argv[1],'rb',buffering=0);"
                        "assert f.read(1)==b'1';os._exit(int(sys.argv[3]))")
                    parent_source=(
                        "import json,os,subprocess,sys;from pathlib import Path;"
                        "r,w=os.pipe();"
                        "p=subprocess.Popen([sys.executable,'-c',sys.argv[1],sys.argv[2],"
                        "str(w),sys.argv[3]],pass_fds=(w,));"
                        "os.close(w);info=json.loads(os.fdopen(r,'rb').read());"
                        "raw=Path('/proc/self/stat').read_text();"
                        "info.update(parent_pid=os.getpid(),parent_pgid=os.getpgrp(),"
                        "parent_start_ticks=int(raw[raw.rindex(')')+2:].split()[19]));"
                        "print(json.dumps(info),flush=True)")
                    def observed_wait(child: subprocess.Popen[bytes], timeout: float | None = None) -> int:
                        code=real_wait(child,timeout=timeout)
                        info=json.loads((root/"command.stdout").read_text())
                        if code != 0 or info["parent_pid"] != child.pid:
                            raise RuntimeError("Actual direct parent did not finish with exit 0")
                        current=identity(info["pid"])
                        if (current["start_ticks"] != info["start_ticks"] or
                                current["pgid"] != child.pid or current["state"] == "Z" or
                                current["pgid"] == os.getpgrp()):
                            raise RuntimeError("Exact live remaining orphan identity is absent")
                        real_killpg(child.pid,0)
                        evidence.update(parent=info,parent_exit_code=code,
                                        remaining_orphan_at_parent_exit=current)
                        return code
                    def observed_cleanup(pgid: int, sig: int) -> None:
                        if not evidence or pgid != evidence["parent"]["parent_pgid"]:
                            raise RuntimeError("Cleanup did not follow actual direct-parent exit")
                        real_killpg(pgid,sig)
                        if "first_cleanup_signal" not in evidence:
                            evidence["first_cleanup_signal"]=int(sig)
                            if sig == 0:
                                with release.open("wb",buffering=0) as control:
                                    control.write(b"1")
                            elif sig != signal.SIGKILL:
                                raise RuntimeError("Unexpected initial cleanup signal")
                            pid,status=os.waitpid(evidence["parent"]["pid"],0)
                            evidence["actual_orphan_reaped"]={
                                "pid":pid,"exit_code":os.waitstatus_to_exitcode(status)}
                    with patch.object(subprocess.Popen,"wait",observed_wait), \
                            patch.object(os,"killpg",observed_cleanup):
                        command=optimizer.run_command(
                            [sys.executable,"-c",parent_source,orphan_source,str(release),
                             str(intended_exit)],root,label,dict(os.environ),5)
                    rejected=False
                    try:
                        optimizer.require_success(command)
                    except ValueError as error:
                        if "completion" not in str(error):
                            raise
                        rejected=True
                    try:
                        real_killpg(evidence["parent"]["parent_pgid"],0)
                    except ProcessLookupError:
                        group_absent=True
                    else:
                        raise RuntimeError("Exact owned process group remains")
                    evidence.update(intended_exit=intended_exit,command=command,
                                    guard_rejected=rejected,actual_group_absent=group_absent,
                                    observers_forwarded_real_wait_and_signal=True)
                    print(json.dumps(evidence),flush=True)
                """)
                result = subprocess.run(
                    [sys.executable, "-c", worker, str(Path(optimizer.__file__).parent),
                     directory, str(intended_exit)], capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                actual = json.loads(result.stdout)
                print("ORPHAN_EVIDENCE " + json.dumps(actual), flush=True)
                self.assertTrue(actual["guard_rejected"], actual)
                self.assertEqual(actual["first_cleanup_signal"], signal.SIGKILL)
                self.assertEqual(actual["actual_orphan_reaped"]["exit_code"], -signal.SIGKILL)
                self.assertIs(actual["command"]["remaining_group_killed"], True)
                self.assertIs(actual["command"]["timed_out"], False)
                self.assertEqual(actual["command"]["exit_code"], 0)
                self.assertTrue(actual["actual_group_absent"])


    def test_success_requires_explicit_clean_flags_and_integer_exit(self) -> None:
        optimizer.require_success(clean_status())
        for flag in ("timed_out", "remaining_group_killed"):
            for value in (True, None, 0, "false", "missing"):
                with self.subTest(flag=flag, value=value):
                    result = clean_status()
                    if value == "missing":
                        del result[flag]
                    else:
                        result[flag] = value
                    with self.assertRaisesRegex(ValueError, "completion"):
                        optimizer.require_success(result)
        for value in (False, None, "0"):
            with self.subTest(exit_code=value), self.assertRaisesRegex(ValueError, "completion"):
                optimizer.require_success({**clean_status(), "exit_code": value})
        with self.assertRaisesRegex(ValueError, "completion"):
            optimizer.require_success({**clean_status(), "remaining_group_members": [37]})
        with self.assertRaisesRegex(ValueError, "exited 37"):
            optimizer.require_success({**clean_status(), "exit_code": 37})

    def test_force_compile_rejects_dirty_success_before_artifact_acceptance(self) -> None:
        for name, data in (("baseline", recovery.ORIGINAL), ("candidate", recovery.CANDIDATE)):
            for flag in ("timed_out", "remaining_group_killed"):
                with self.subTest(arm=name, flag=flag), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    recovery.main_inputs(root, ("A",))
                    tools = proposals.ChangedProposalEvidenceTests.tools(root)
                    arm = tools.output / name

                    def external(argv: list[str], label: Path,
                                 environment: dict[str, str] | None = None) -> dict[str, object]:
                        optimizer.write_json(Path(argv[argv.index("-o") + 1]), {"wall_seconds": 0})
                        result = {**clean_status(), flag: True, "argv": argv,
                                  "external_lean_and_time_mock": True}
                        optimizer.write_json(Path(str(label) + ".json"), result)
                        return result

                    with patch.object(optimizer.Tools, "run", side_effect=external), \
                            patch.object(optimizer, "artifact_receipt",
                                         return_value=[{"external_artifacts_mock": True}]) as artifacts:
                        with self.assertRaisesRegex(ValueError, "completion"):
                            optimizer.compile_arm(tools, Path("A.lean"), root / ".lake/build/ir/A.setup.json",
                                                  arm, source_bytes=data)
                        artifacts.assert_not_called()
                        self.assertFalse((arm / "compile-receipt.json").exists())

    def test_main_blocks_unclean_preparation_and_fallback_before_analysis(self) -> None:
        fixture = proposals.ChangedProposalEvidenceTests()
        for fallback in (False, True):
            with self.subTest(fallback=fallback), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with fixture.external_cli(root) as (invoke, analyzed, calls):
                    original = optimizer.Tools.run.side_effect

                    def external(argv: list[str], label: Path,
                                 environment: dict[str, str] | None = None) -> dict[str, object]:
                        result = original(argv, label, environment)
                        if "build" in argv:
                            if fallback and "--no-build" not in argv:
                                result["exit_code"] = 37
                            else:
                                result["remaining_group_killed"] = True
                            optimizer.write_json(Path(str(label) + ".json"), result)
                        return result

                    with patch.object(optimizer.Tools, "run", side_effect=external):
                        self.assertEqual(invoke([]), 1)
                    result = json.loads((root / "output/results.jsonl").read_text())
                    self.assertEqual(result["status"], "blocked")
                    self.assertIn("completion", result["error"])
                    self.assertEqual(analyzed, [])
                    self.assertEqual([kind for kind, _ in calls], ["prepare"] * (2 if fallback else 1))

    def test_native_headers_allow_clean_status_one_and_reject_dirty_rows(self) -> None:
        for code in (0, 1):
            for dirty in (False, True):
                with self.subTest(code=code, dirty=dirty), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    recovery.main_inputs(root, ("A",))
                    tools = proposals.ChangedProposalEvidenceTests.tools(root)
                    tools.output.mkdir()
                    row = {"path": "A.lean", "module": "A", "source_sha256": recovery.digest(recovery.ORIGINAL)}

                    def external(argv: list[str], label: Path,
                                 environment: dict[str, str] | None = None) -> dict[str, object]:
                        label.parent.mkdir(parents=True, exist_ok=True)
                        Path(str(label) + ".stdout").write_text(
                            json.dumps(recovery.native_header(root / "A.lean")) + "\n")
                        return {**clean_status(), "exit_code": code, "remaining_group_killed": dirty}

                    with patch.object(optimizer.Tools, "run", side_effect=external):
                        if dirty:
                            with self.assertRaisesRegex(ValueError, "completion"):
                                optimizer.native_headers(tools, [row])
                            self.assertEqual((tools.output / "native-headers.jsonl").read_bytes(), b"")
                        else:
                            self.assertEqual(set(optimizer.native_headers(tools, [row])), {"A.lean"})

    def test_populated_changed_candidate_resume_requires_clean_both_arm_commands(self) -> None:
        fixture = proposals.ChangedProposalEvidenceTests()
        for name in ("baseline", "candidate"):
            for mutation in ("timed_out", "remaining_group_killed", "missing_flag", "missing_command", "bad_exit"):
                with self.subTest(arm=name, mutation=mutation), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    with fixture.external_cli(root) as (invoke, _, calls):
                        original_compile = optimizer.compile_arm.side_effect

                        def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                                         arm: Path, artifact_root: Path | None = None,
                                         source_bytes: bytes | None = None, *,
                                         header_is_module: bool = True) -> dict[str, object]:
                            result = original_compile(tools, relative, setup, arm, artifact_root, source_bytes,
                                                      header_is_module=header_is_module)
                            return result

                        with patch.object(optimizer, "compile_arm", side_effect=compile_stub):
                            self.assertEqual(invoke([]), 0)
                            journal = root / "output/results.jsonl"
                            result = json.loads(journal.read_text())
                            self.assertEqual((result["status"], result["declaration_count"]), ("verified", 1))
                            for filename in ("owned-before.json", "owned-after.json"):
                                snapshot = optimizer.read_json(Path(result["attempt_directory"]) / filename)
                                self.assertEqual(len(snapshot["declarations"]), 1)
                                self.assertEqual(len(snapshot["declarations"][0]), 10)
                            before_calls = list(calls)
                            self.assertEqual(invoke(["--resume"]), 0)
                            self.assertEqual(calls, before_calls)
                            if mutation == "missing_command":
                                del result[name]["command"]
                            elif mutation == "missing_flag":
                                del result[name]["command"]["remaining_group_killed"]
                            elif mutation == "bad_exit":
                                result[name]["command"]["exit_code"] = False
                            else:
                                result[name]["command"][mutation] = True
                            optimizer.write_json(Path(result["attempt_directory"]) / name / "compile.json",
                                                 result[name].get("command", {}))
                            journal.write_text(json.dumps(result) + "\n")
                            changed = journal.read_bytes()
                            with self.assertRaisesRegex(ValueError, "completion"):
                                invoke(["--resume"])
                            self.assertEqual(calls, before_calls)
                            self.assertEqual(journal.read_bytes(), changed)


if __name__ == "__main__":
    unittest.main()
