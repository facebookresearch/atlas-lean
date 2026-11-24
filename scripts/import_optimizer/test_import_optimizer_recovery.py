#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Recovery state tests; Lean/Lake calls are mocked and child processes are real."""

from __future__ import annotations

import contextlib
import difflib
import hashlib
import io
import json
import os
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from collections.abc import Iterator
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
from test_generate_import_inventory import header_fixture


ORIGINAL = b"module\nimport Mathlib\ndef x : Nat := 0\n"
CANDIDATE = b"module\nimport Init\ndef x : Nat := 0\n"
CHECK_OUTPUT = subprocess.check_output


@contextlib.contextmanager
def isolated_ancestor_metadata(root: Path) -> Iterator[None]:
    """Keep host activity out of metadata-only tests; fixture paths stay real."""
    original = optimizer.path_component_identity

    def identity(path: Path, *, strict: bool = False,
                 mutable: bool = False) -> optimizer.SourceIdentity:
        value = original(path, strict=strict, mutable=mutable)
        if stat.S_ISDIR(value[5]) and not path.is_relative_to(root):
            return (value[0], value[1], 0, 0, 0, value[5])
        return value

    with patch.object(optimizer, "path_component_identity", side_effect=identity):
        yield


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def time_version_stub(argv: list[str], **kwargs: object) -> bytes:
    if Path(argv[0]).name == "time" and argv[1:] == ["--version"]:
        return b"GNU time fixture"
    return CHECK_OUTPUT(argv, **kwargs)


def native_header(path: Path, data: bytes = ORIGINAL,
                  is_module: bool = True) -> dict[str, object]:
    header = header_fixture(path, (("Mathlib", ()),), is_module=is_module, data=data)
    header["relative_path"] = path.name
    return header


def main_inputs(root: Path, names: tuple[str, ...]) -> list[str]:
    rows = []
    dependency = root / "fixture-import-part"
    dependency.write_bytes(b"Explicitly mocked imported module bytes\n")
    for name in names:
        source = root / (name + ".lean")
        source.write_bytes(ORIGINAL)
        rows.append({"path": source.name, "module": name,
                     "source_sha256": digest(ORIGINAL), "analysis_status": "pending"})
        optimizer.write_json(root / ".lake/build/ir" / (name + ".setup.json"), {
            "name": name, "isModule": True, "importArts": {"Mathlib": [[str(dependency)], []], "Init": [[], []]},
        })
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        (root / name).write_text("Python recovery fixture\n")
    binary = root / "bin"
    binary.mkdir()
    for name in ("lake", "lean", "time"):
        (binary / name).write_text("Fixture identity bytes, never executed\n")
    manifest, headers = root / "manifest.jsonl", root / "headers.jsonl"
    manifest.write_text("".join(json.dumps(row) + "\n" for row in rows))
    headers.write_text("".join(json.dumps(native_header(root / (name + ".lean"))) + "\n"
                             for name in names))
    for arguments in (["init", "-q"], ["add", "--", *(name + ".lean" for name in names)]):
        subprocess.run(["git", *arguments], cwd=root, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return ["optimize_imports.py", "--root", str(root), "--output", str(root / "output"),
            "--manifest", str(manifest), "--headers", str(headers),
            "--lake", str(binary / "lake"), "--time", str(binary / "time")]


def environment_stub(argv: list[str], cwd: Path, label: Path,
                     environment: dict[str, str], timeout: int) -> dict[str, object]:
    # Use the fixture's own compiler namespace, including its explicit
    # standard library when present, instead of an ambient real toolchain.
    sysroot = cwd / "sysroot" if (cwd / "sysroot/bin/lean").is_file() else cwd
    Path(str(label) + ".stdout").write_text(json.dumps({
        "LAKE": str(argv[0]), "LEAN_SYSROOT": str(sysroot),
        "LEAN_PATH": "", "LEAN_SRC_PATH": "",
    }) + "\n")
    return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "External Lake environment mocked"}


def mock_no_change_proposals(tools: optimizer.Tools, rows: list[dict[str, object]],
                             headers: dict[str, dict[str, object]], directory: Path
                             ) -> dict[str, optimizer.Proposal]:
    label = directory / "mock-analysis" / str(time.time_ns()) / "shake"
    label.parent.mkdir(parents=True, exist_ok=True)
    stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
    stdout.write_text("".join(str(row["path"]) + ":\n" for row in rows))
    stderr.write_text("")
    argv = tools.lake_command("shake", "--force", "--explain", "--add-public")
    for row in rows:
        argv.extend(("--only", str(row["module"])))
    optimizer.write_json(Path(str(label) + ".json"), {
        "argv": [*argv, *(str(row["module"]) for row in rows)], "cwd": str(tools.root),
        "exit_code": 0, "timed_out": False, "remaining_group_killed": False,
        "elapsed_seconds": 0, "stdout": str(stdout), "stderr": str(stderr),
    })
    evidence = optimizer.analysis_evidence(tools, label, "shake", optimizer.analysis_inputs(tools, rows))
    return {str(row["path"]): optimizer.Proposal(evidence=evidence) for row in rows}


def mock_changed_proposals(tools: optimizer.Tools, rows: list[dict[str, object]],
                           headers: dict[str, dict[str, object]], directory: Path
                           ) -> dict[str, optimizer.Proposal]:
    proposals = mock_no_change_proposals(tools, rows, headers, directory)
    result = {}
    for row in rows:
        evidence = proposals[str(row["path"])].evidence
        assert evidence is not None
        stdout = Path(evidence["stdout"]["path"])
        stdout.write_text("".join(str(item["path"]) + ":\n  remove #[import Mathlib]\n  add #[import Init]\n"
                                  for item in rows))
        evidence["stdout"] = optimizer.file_pin(stdout)
        result[str(row["path"])] = optimizer.Proposal((optimizer.ImportSpec("Mathlib"),),
                                                     (optimizer.ImportSpec("Init"),), evidence)
    return result


def saved_fixture_tools(output: Path) -> optimizer.Tools:
    return optimizer.Tools(output, output, output / "lake", output / "lean", output, {}, 5,
                           time_binary=output / "time")


@contextlib.contextmanager
def mock_saved_canonical_artifacts(tools: optimizer.Tools) -> Iterator[None]:
    actual = optimizer.artifact_receipt

    def artifacts(root: Path, relative: Path, **kwargs: object) -> list[dict[str, object]]:
        if root == tools.root / ".lake/build/lib/lean":
            return [{"external_canonical_artifacts_mock": optimizer.sha256(tools.root / "canonical-input-marker")}]
        return actual(root, relative, **kwargs)

    with patch.object(optimizer, "artifact_receipt", side_effect=artifacts):
        yield


def bind_saved_fixture_proposal(result: dict[str, object], tools: optimizer.Tools) -> None:
    directory = Path(result["attempt_directory"])
    original = (directory / "original.lean").read_bytes()
    candidate = (directory / "candidate.lean").read_bytes()
    relative = Path(result["path"])
    (tools.root / relative).write_bytes(original)
    marker = tools.root / "canonical-input-marker"
    if not marker.exists():
        marker.write_text("Explicit external canonical artifact mock\n")
    if not tools.lean.exists():
        tools.lean.write_text("Compiler identity fixture, never executed\n")
    setup = tools.root / ".lake/build/ir" / relative.with_suffix(".setup.json")
    optimizer.write_json(setup, optimizer.read_json(Path(result["setup_path"])))
    native = optimizer.read_json(Path(result["native_header"]["path"]))
    if native["is_module"]:
        row = {"path": str(relative), "module": result["module"], "source_sha256": result["source_sha256"]}
        with mock_saved_canonical_artifacts(tools):
            proposal = mock_changed_proposals(tools, [row], {str(relative): native}, directory)[str(relative)]
    else:
        label = directory / "legacy"
        optimizer.write_json(Path(str(label) + ".stdout"), {"module": result["module"], "required_modules": []})
        Path(str(label) + ".stderr").write_text("")
        optimizer.write_json(Path(str(label) + ".json"), {
            "argv": [str(tools.lean), "-j2", "--run", str(tools.helpers / "legacy.lean"), result["module"]],
            "cwd": str(tools.root), "exit_code": 0, "timed_out": False,
            "remaining_group_killed": False, "stdout": str(label) + ".stdout", "stderr": str(label) + ".stderr",
        })
        proposal = optimizer.Proposal(evidence=optimizer.analysis_evidence(tools, label, "legacy"))
    result.update(old_imports=[span.spec.render() for span in optimizer.decode_header(native, original).imports],
                  removed_imports=[spec.render() for spec in proposal.remove],
                  added_imports=[spec.render() for spec in proposal.add])
    optimizer.write_json(directory / "proposal.json", {
        "path": str(relative), "module": result["module"], "source_sha256": result["source_sha256"],
        "native_header": native, "analysis": proposal.evidence,
        "removed_imports": result["removed_imports"], "added_imports": result["added_imports"],
    })
    result["proposal_receipt"] = optimizer.file_pin(directory / "proposal.json")
    patch_bytes = b"".join(difflib.diff_bytes(
        difflib.unified_diff, original.splitlines(keepends=True), candidate.splitlines(keepends=True),
        fromfile=("a/" + str(relative)).encode(), tofile=("b/" + str(relative)).encode()))
    (directory / "proposal.patch").write_bytes(patch_bytes)
    result.update(proposal_patch=str(directory / "proposal.patch"),
                  proposal_patch_sha256=optimizer.sha256(directory / "proposal.patch"))


def verify_saved_fixture(result: dict[str, object], output: Path,
                         tools: optimizer.Tools | None = None) -> None:
    tools = tools or saved_fixture_tools(output)
    with mock_saved_canonical_artifacts(tools):
        optimizer.verify_saved_candidate(result, output, tools)


def mock_compile_command(tools: optimizer.Tools, argv: list[str], label: Path) -> dict[str, object]:
    label.parent.mkdir(parents=True, exist_ok=True)
    stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
    stdout.write_text("External compiler and GNU time explicitly mocked\n")
    stderr.write_text("")
    command = {"argv": argv, "cwd": str(tools.root), "exit_code": 0,
               "timed_out": False, "remaining_group_killed": False,
               "stdout": str(stdout), "stderr": str(stderr), "external_lean_and_time_mock": True}
    optimizer.write_json(Path(str(label) + ".json"), command)
    return command


def mock_arm_inputs(tools: optimizer.Tools, setup: Path, arm: Path,
                    relative: Path, source_bytes: bytes,
                    artifact_root: Path | None = None) -> dict[str, object]:
    arm.mkdir(parents=True, exist_ok=True)
    copy = arm / "setup.json"
    copy.write_bytes(setup.read_bytes())
    source_root = arm / "source"
    source = source_root / relative
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(source_bytes)
    for executable in (tools.lean, tools.time_binary):
        if not executable.resolve().is_relative_to(tools.root.resolve()):
            raise AssertionError("Executable fixture escaped its temporary root")
        if not executable.exists():
            executable.parent.mkdir(parents=True, exist_ok=True)
            executable.write_text("External executable identity fixture, never executed\n")
    argv = optimizer.compilation_argv(tools, relative, arm, artifact_root or arm / "artifacts")
    command = mock_compile_command(tools, argv, arm / "compile")
    evidence = optimizer.analysis_evidence(tools, arm / "compile", "compile", {
        "compiler": optimizer.file_pin(tools.lean), "time_binary": optimizer.file_pin(tools.time_binary)})
    compilation = {"command": command, "command_evidence": evidence,
            "setup": optimizer.file_pin(copy), "setup_source": optimizer.file_pin(setup),
            "header_is_module": True,
            "source_root": str(source_root), "source_path": str(source), "source_sha256": digest(source_bytes),
            "setup_root": str(tools.root), "setup_sha256": optimizer.sha256(setup),
            "standard_library_root": str(library) if (library := optimizer.standard_library_root(tools)) else None,
            "input_manifest": optimizer.pin_setup_inputs(tools, optimizer.read_json(copy)),
            "artifact_root": str(artifact_root or arm / "artifacts")}
    bind_mock_snapshot_inputs(tools, compilation, relative)
    return compilation


def bind_mock_snapshot_inputs(tools: optimizer.Tools, compilation: dict[str, object],
                              relative: Path) -> None:
    artifacts = Path(compilation["artifact_root"])
    artifacts.mkdir(parents=True, exist_ok=True)
    if not any(artifacts.iterdir()):
        (artifacts / "external-artifact-fixture").write_bytes(b"Explicitly mocked arm artifact bytes\n")
    module = optimizer.read_json(Path(compilation["setup"]["path"]))["name"]
    compilation["snapshot_input_manifest"] = optimizer.pin_snapshot_inputs(tools, artifacts)
    compilation["snapshot_setup"] = optimizer.pin_snapshot_setup(
        tools, artifacts, [{"path": str(relative), "module": module}], {str(relative): compilation}, kind="single")


class IsolatedAncestorMetadataTests(unittest.TestCase):
    def test_only_external_directory_timestamps_are_isolated(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            outer = Path(directory).resolve()
            root = outer / "fixture"
            root.mkdir()
            with patch.object(optimizer.sys, "platform", "darwin"), isolated_ancestor_metadata(root):
                before_outer = optimizer.path_component_identity(outer)
                before_inner = optimizer.path_component_identity(root, strict=True)
                (outer / "host-activity").write_text("unrelated")
                (root / "fixture-activity").write_text("must be observed")
                self.assertEqual(optimizer.path_component_identity(outer), before_outer)
                self.assertNotEqual(optimizer.path_component_identity(root, strict=True), before_inner)
                before_mode = optimizer.path_component_identity(outer)
                outer.chmod(0o750)
                self.assertNotEqual(optimizer.path_component_identity(outer), before_mode)

    def test_external_files_and_symlinks_retain_real_identity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            outer = Path(directory).resolve()
            root = outer / "fixture"
            root.mkdir()
            source = outer / "helper"
            source.write_text("before")
            link = outer / "link"
            link.symlink_to(source)
            with isolated_ancestor_metadata(root):
                before_file = optimizer.path_component_identity(source)
                before_link = optimizer.path_component_identity(link)
                source.write_text("after")
                link.unlink()
                link.symlink_to(root)
                self.assertNotEqual(optimizer.path_component_identity(source), before_file)
                self.assertNotEqual(optimizer.path_component_identity(link), before_link)


class SourceRecoveryTests(unittest.TestCase):
    def test_compile_arms_use_original_module_path_in_isolated_sources(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            relative = Path("Package/Statement.lean")
            tracked = root / relative
            tracked.parent.mkdir()
            tracked.write_bytes(ORIGINAL)
            tracked.chmod(0o444)
            original_stat = tracked.stat()
            setup = root / "production.setup.json"
            optimizer.write_json(setup, {"name": "Package.Statement", "isModule": True,
                                        "imports": None, "importArts": {},
                                        "options": {"autoImplicit": False}})
            setup_hash = optimizer.sha256(setup)
            tools = optimizer.Tools(root, root / "output", root / "lake", root / "lean",
                                    root / "helpers", {}, 5, root / "mock-time")
            for executable in (tools.lean, tools.time_binary):
                executable.write_text("External executable identity fixture, never executed\n")
            observed = []

            def run_stub(tools: optimizer.Tools, argv: list[str], label: Path,
                         environment: dict[str, str] | None = None) -> dict[str, object]:
                lean_index = argv.index(str(tools.lean))
                self.assertEqual(argv[lean_index + 1:lean_index + 3], ["-j2", "-R"])
                source_root = Path(argv[lean_index + 3])
                source = Path(argv[lean_index + 4])
                self.assertEqual(source.relative_to(source_root), relative)
                self.assertNotEqual(source, tracked)
                copy = Path(argv[lean_index + 6])
                self.assertEqual(argv[lean_index + 5], "--setup")
                self.assertEqual(copy.read_bytes(), setup.read_bytes())
                self.assertNotEqual(copy, setup)
                self.assertEqual(tracked.read_bytes(), ORIGINAL)
                observed.append((source_root, source, source.read_bytes()))
                Path(argv[argv.index("-o") + 1]).write_text(json.dumps({
                    "wall_seconds": 0, "user_seconds": 0, "system_seconds": 0,
                    "max_rss_kib": 0}) + "\n")
                return mock_compile_command(tools, argv, label)

            with patch.object(optimizer.Tools, "run", new=run_stub), \
                    patch.object(optimizer, "artifact_receipt",
                                 return_value=[{"external_artifacts_mock": True}]):
                for arm, data in (("baseline", ORIGINAL), ("candidate", CANDIDATE)):
                    result = optimizer.compile_arm(tools, relative, setup,
                                                   tools.output / arm, source_bytes=data)
                    self.assertEqual(result["source_sha256"], digest(data))
                    self.assertEqual(result["setup_sha256"], setup_hash)
                    self.assertEqual(result["source_path"], str(observed[-1][1]))
            self.assertEqual([row[2] for row in observed], [ORIGINAL, CANDIDATE])
            self.assertNotEqual(observed[0][0], observed[1][0])
            self.assertEqual(tracked.read_bytes(), ORIGINAL)
            self.assertEqual(tracked.stat().st_mtime_ns, original_stat.st_mtime_ns)
            self.assertEqual(tracked.stat().st_mode, original_stat.st_mode)
            self.assertEqual(optimizer.sha256(setup), setup_hash)
            self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_compile_rejects_changed_isolated_source_or_setup(self) -> None:
        for mutation in ("source", "setup"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                main_inputs(root, ("A",))
                tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                        root / "bin/lean", root / "helpers", {}, 5,
                                        root / "bin/time")
                setup = root / ".lake/build/ir/A.setup.json"

                def run_stub(tools: optimizer.Tools, argv: list[str], label: Path,
                             environment: dict[str, str] | None = None) -> dict[str, object]:
                    target = (Path(argv[argv.index(str(tools.lean)) + 4])
                              if mutation == "source" else setup)
                    target.write_bytes(CANDIDATE)
                    return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "external_lean_mock": True}

                with patch.object(optimizer.Tools, "run", new=run_stub), \
                        patch.object(optimizer, "artifact_receipt") as artifacts:
                    with self.assertRaisesRegex(ValueError, "Isolated source or production setup changed"):
                        optimizer.compile_arm(tools, Path("A.lean"), setup,
                                              tools.output / "baseline", source_bytes=ORIGINAL)
                    artifacts.assert_not_called()
                self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
                self.assertFalse((tools.output / "transaction.json").exists())
                self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_edit_after_final_source_hash_is_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            main_inputs(root, ("A",))
            source = root / "A.lean"
            edited = ORIGINAL.replace(b":= 0", b":= 1")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                    root / "bin/lean", root / "helpers", {}, 5,
                                    time_binary=root / "bin/time")
            row = {"path": "A.lean", "module": "A", "source_sha256": digest(ORIGINAL)}
            compiled = []
            injections = []
            actual_sha256 = optimizer.sha256

            def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                             arm: Path, artifact_root: Path | None = None,
                             source_bytes: bytes | None = None, *,
                             header_is_module: bool = True) -> dict[str, object]:
                compiled.append(arm.name)
                return {"external_lean_mock": True}

            def edit_after_hash(path: Path) -> str:
                value = actual_sha256(path)
                if path == source and "baseline" in compiled and not injections:
                    self.assertEqual(value, digest(ORIGINAL))
                    source.write_bytes(edited)
                    injections.append(value)
                return value

            with patch.object(optimizer.Tools, "run", return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False}), \
                    patch.object(optimizer, "artifact_receipt",
                                 return_value=[{"external_lean_mock": True}]), \
                    patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                    patch.object(optimizer, "sha256", side_effect=edit_after_hash):
                proposal = mock_changed_proposals(tools, [row], {}, tools.output)["A.lean"]
                result = optimizer.optimize_one(tools, row, native_header(source), proposal,
                                                defer_snapshots=True)
            self.assertEqual(injections, [digest(ORIGINAL)])
            self.assertEqual(source.read_bytes(), edited)
            self.assertEqual(result["status"], "blocked")
            self.assertFalse((tools.output / "transaction.json").exists())
            self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_edit_during_baseline_compile_is_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            main_inputs(root, ("A",))
            source = root / "A.lean"
            edited_source = ORIGINAL.replace(b":= 0", b":= 1")
            entered, finished = threading.Event(), threading.Event()
            failures, compiled = [], []

            def edit_source() -> None:
                try:
                    if not entered.wait(timeout=5):
                        raise AssertionError("Baseline compilation never started")
                    source.write_bytes(edited_source)
                except BaseException as error:
                    failures.append(error)
                finally:
                    finished.set()

            def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                             arm: Path, artifact_root: Path | None = None,
                             source_bytes: bytes | None = None, *,
                             header_is_module: bool = True) -> dict[str, object]:
                compiled.append(arm.name)
                self.assertEqual(source_bytes, ORIGINAL)
                if arm.name == "baseline":
                    entered.set()
                    self.assertTrue(finished.wait(timeout=5))
                    self.assertFalse(failures)
                return {"external_lean_mock": True}

            tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                    root / "bin/lean", root / "helpers", {}, 5,
                                    time_binary=root / "bin/time")
            row = {"path": "A.lean", "module": "A", "source_sha256": digest(ORIGINAL)}
            snapshot = {"module": "A", "declaration_count": 1, "loaded_module_count": 1,
                        "declarations": [{"name": "A.x", "type": "Nat", "value": "Nat.zero"}]}
            editor = threading.Thread(target=edit_source)
            editor.start()
            try:
                with patch.object(optimizer.Tools, "run", return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False}), \
                        patch.object(optimizer, "artifact_receipt",
                                     return_value=[{"external_lean_mock": True}]), \
                        patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                        patch.object(optimizer, "snapshot_arm", return_value=snapshot):
                    proposal = mock_changed_proposals(tools, [row], {}, tools.output)["A.lean"]
                    result = optimizer.optimize_one(tools, row, native_header(source), proposal)
            finally:
                entered.set()
                editor.join(timeout=5)
            self.assertFalse(editor.is_alive())
            self.assertFalse(failures)
            self.assertEqual(source.read_bytes(), edited_source)
            self.assertEqual(result["status"], "blocked")
            self.assertEqual(compiled, ["baseline"])
            self.assertFalse((tools.output / "transaction.json").exists())
            self.assertEqual((Path(str(result["attempt_directory"])) / "original.lean").read_bytes(),
                             ORIGINAL)

    def test_partial_source_retains_backup_and_transaction(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source, backup = root / "A.lean", root / "original.lean"
            transaction = root / "transaction.json"
            source.write_bytes(CANDIDATE[:17])
            backup.write_bytes(ORIGINAL)
            optimizer.write_json(transaction, {
                "path": source.name, "backup": str(backup),
                "source_sha256": digest(ORIGINAL), "candidate_sha256": digest(CANDIDATE),
            })
            with self.assertRaises(ValueError):
                optimizer.recover_source_edit(root, transaction)
            self.assertEqual(source.read_bytes(), CANDIDATE[:17])
            self.assertEqual(backup.read_bytes(), ORIGINAL)
            self.assertTrue(transaction.is_file())

    def test_main_stops_before_next_candidate_when_legacy_recovery_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B"))
            compiled = []

            def compile_stub(tools: optimizer.Tools, relative: Path,
                             setup: Path, arm: Path,
                             artifact_root: Path | None = None,
                             source_bytes: bytes | None = None, *,
                             header_is_module: bool = True) -> dict[str, object]:
                compiled.append((relative.name, arm.name))
                if relative.name == "A.lean" and arm.name == "candidate":
                    self.assertEqual(source_bytes, CANDIDATE)
                    self.assertEqual((root / relative).read_bytes(), ORIGINAL)
                    optimizer.write_json(tools.output / "transaction.json", {
                        "path": str(relative), "backup": str(arm.parent / "original.lean"),
                        "source_sha256": digest(ORIGINAL), "candidate_sha256": digest(CANDIDATE),
                    })
                    (root / relative).write_bytes(CANDIDATE[:17])
                    raise OSError("Injected legacy transaction with unknown source bytes")
                return {"external_lean_mock": True}

            snapshot = {"module": "A", "declaration_count": 1, "loaded_module_count": 1,
                        "declarations": [{"name": "A.x", "type": "Nat", "value": "Nat.zero"}]}
            with patch.object(sys, "argv", arguments), \
                    patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output",
                                 side_effect=time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=environment_stub), \
                    patch.object(optimizer.Tools, "run",
                                 return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "Build mocked"}), \
                    patch.object(optimizer, "artifact_receipt",
                                 return_value=[{"external_lean_mock": True}]), \
                    patch.object(optimizer, "analyze_batch",
                                 side_effect=mock_changed_proposals), \
                    patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                    patch.object(optimizer, "snapshot_arm", return_value=snapshot), \
                    contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(ValueError):
                    optimizer.main()
            self.assertEqual(compiled, [("A.lean", "baseline"), ("A.lean", "candidate")])
            self.assertEqual((root / "A.lean").read_bytes(), CANDIDATE[:17])
            self.assertEqual((root / "B.lean").read_bytes(), ORIGINAL)
            transaction = optimizer.read_json(root / "output/transaction.json")
            self.assertEqual(transaction["path"], "A.lean")
            self.assertEqual(Path(str(transaction["backup"])).read_bytes(), ORIGINAL)
            journal = root / "output/results.jsonl"
            rows = [json.loads(line) for line in journal.read_text().splitlines()]
            self.assertEqual([(row["path"], row["status"]) for row in rows],
                             [("A.lean", "blocked")])


class JournalRecoveryTests(unittest.TestCase):
    def test_atlas_only_changes_reject_resume_of_legacy_no_change_and_blocked_rows(self) -> None:
        for status in ("no_change", "blocked"):
            for mutation in ("revision", "added", "removed"):
                with self.subTest(status=status, mutation=mutation), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    arguments = main_inputs(root, ("A",))
                    source = b"-- shake: keep\nimport Mathlib\ndef x : Nat := 0\n"
                    (root / "A.lean").write_bytes(source)
                    row = json.loads((root / "manifest.jsonl").read_text())
                    row["source_sha256"] = digest(source)
                    (root / "manifest.jsonl").write_text(json.dumps(row) + "\n")
                    header = native_header(root / "A.lean", source, is_module=False)
                    (root / "headers.jsonl").write_text(json.dumps(header) + "\n")
                    setup_path = root / ".lake/build/ir/A.setup.json"
                    setup = optimizer.read_json(setup_path)
                    setup["isModule"] = False
                    optimizer.write_json(setup_path, setup)
                    lock = root / "atlas.lock.json"
                    if mutation != "added":
                        lock.write_text(json.dumps({"revision": "a" * 40}) + "\n")
                    gate = {"exit_code": 0 if status == "no_change" else 1,
                            "timed_out": False, "remaining_group_killed": False,
                            "stderr": "External Lake mocked"}
                    with patch.object(optimizer.signal, "signal"), \
                            patch.object(optimizer.subprocess, "check_output", side_effect=time_version_stub), \
                            patch.object(optimizer, "run_command", side_effect=environment_stub), \
                            patch.object(optimizer.Tools, "run", return_value=gate) as build, \
                            patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                            patch.object(optimizer, "analyze_batch", side_effect=AssertionError("Legacy source used Shake")), \
                            patch.object(optimizer, "compile_arm", side_effect=AssertionError("Unexpected Lean compilation")), \
                            contextlib.redirect_stdout(io.StringIO()):
                        expected_exit = 0 if status == "no_change" else 1
                        with patch.object(sys, "argv", arguments):
                            self.assertEqual(optimizer.main(), expected_exit)
                        identity_path = root / "output/run.json"
                        identity = identity_path.read_bytes()
                        pins = json.loads(identity)["project_pins"]
                        self.assertEqual("atlas.lock.json" in pins, mutation != "added")
                        journal_path = root / "output/results.jsonl"
                        journal = journal_path.read_bytes()
                        self.assertEqual(json.loads(journal)["status"], status)
                        calls = build.call_count
                        with patch.object(sys, "argv", arguments + ["--resume"]):
                            self.assertEqual(optimizer.main(), expected_exit)
                        self.assertEqual(build.call_count, calls)
                        if mutation == "removed":
                            lock.unlink()
                        else:
                            lock.write_text(json.dumps({"revision": "b" * 40}) + "\n")
                        with patch.object(sys, "argv", arguments + ["--resume"]), \
                                self.assertRaisesRegex(ValueError, "Resume inputs, compiler, or backend bytes changed"):
                            optimizer.main()
                        self.assertEqual(identity_path.read_bytes(), identity)
                        self.assertEqual(journal_path.read_bytes(), journal)
                        self.assertEqual(build.call_count, calls)
                    self.assertEqual((root / "A.lean").read_bytes(), source)

    def test_unselected_source_changes_reject_analysis_and_resume(self) -> None:
        for phase in ("analysis", "resume"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = main_inputs(root, ("A", "B")) + ["A.lean"]
                dependency = root / "B.lean"
                changed = ORIGINAL + b"-- concurrent unselected source edit\n"

                def analyze_stub(*args: object) -> dict[str, optimizer.Proposal]:
                    proposals = mock_no_change_proposals(*args)
                    if phase == "analysis":
                        dependency.write_bytes(changed)
                    return proposals

                with patch.object(optimizer.signal, "signal"), \
                        patch.object(optimizer.subprocess, "check_output",
                                     side_effect=time_version_stub), \
                        patch.object(optimizer, "run_command", side_effect=environment_stub), \
                        patch.object(optimizer.Tools, "run",
                                     return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "External Lake mocked"}), \
                        patch.object(optimizer, "artifact_receipt",
                                     return_value=[{"external_artifacts_mock": True}]), \
                        patch.object(optimizer, "analyze_batch", side_effect=analyze_stub) as analyze, \
                        patch.object(optimizer, "compile_arm",
                                     side_effect=AssertionError("Unexpected Lean compilation")), \
                        contextlib.redirect_stdout(io.StringIO()):
                    journal = root / "output/results.jsonl"
                    if phase == "resume":
                        with patch.object(sys, "argv", arguments):
                            self.assertEqual(optimizer.main(), 0)
                        self.assertEqual(json.loads(journal.read_bytes())["status"], "no_change")
                        with patch.object(sys, "argv", arguments + ["--resume"]):
                            self.assertEqual(optimizer.main(), 0)
                        before = journal.read_bytes()
                        identity = (root / "output/run.json").read_bytes()
                        dependency.write_bytes(changed)
                    argv = arguments + (["--resume"] if phase == "resume" else [])
                    with patch.object(sys, "argv", argv):
                        with self.assertRaisesRegex(ValueError, "Inventory source hash changed"):
                            optimizer.main()
                    self.assertEqual(analyze.call_count, 1)
                    self.assertEqual(journal.read_bytes(), before if phase == "resume" else b"")
                    if phase == "resume":
                        self.assertEqual((root / "output/run.json").read_bytes(), identity)
                self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
                self.assertEqual(dependency.read_bytes(), changed)

    def test_lake_only_change_rejects_resume(self) -> None:
        for mutation in ("bytes", "resolved_path", "selected_toolchain"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = main_inputs(root, ("A",))
                lake = root / "bin/lake"
                original_lake = lake.read_bytes()
                selected_lake = lake
                if mutation == "selected_toolchain":
                    sysroot = root / "toolchain"
                    (sysroot / "bin").mkdir(parents=True)
                    selected_lake = sysroot / "bin/lake"
                    selected_lake.write_bytes(original_lake)
                    (sysroot / "bin/lean").write_bytes((root / "bin/lean").read_bytes())

                def toolchain_environment(argv: list[str], cwd: Path, label: Path,
                                          environment: dict[str, str], timeout: int) -> dict[str, object]:
                    result = environment_stub(argv, cwd, label, environment, timeout)
                    if mutation == "selected_toolchain":
                        Path(str(label) + ".stdout").write_text(json.dumps({
                            "LAKE": str(selected_lake), "LEAN_SYSROOT": str(sysroot),
                        }) + "\n")
                    return result

                with patch.object(optimizer.signal, "signal"), \
                        patch.object(optimizer.subprocess, "check_output", side_effect=time_version_stub), \
                        patch.object(optimizer, "run_command", side_effect=toolchain_environment), \
                        patch.object(optimizer.Tools, "run", return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "External Lake mocked"}), \
                        patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                        patch.object(optimizer, "analyze_batch", side_effect=mock_no_change_proposals) as analyze, \
                        patch.object(optimizer, "compile_arm", side_effect=AssertionError("Unexpected Lean compilation")), \
                        contextlib.redirect_stdout(io.StringIO()):
                    with patch.object(sys, "argv", arguments):
                        self.assertEqual(optimizer.main(), 0)
                    identity_path = root / "output/run.json"
                    identity_before = identity_path.read_bytes()
                    journal_path = root / "output/results.jsonl"
                    journal_before = journal_path.read_bytes()
                    self.assertEqual(json.loads(journal_before)["status"], "no_change")
                    with patch.object(sys, "argv", arguments + ["--resume"]):
                        self.assertEqual(optimizer.main(), 0)
                    self.assertEqual(identity_path.read_bytes(), identity_before)
                    if mutation in ("bytes", "selected_toolchain"):
                        selected_lake.write_bytes(original_lake + b"Changed Lake fixture\n")
                    else:
                        replacement = lake.with_name("lake-replacement")
                        replacement.write_bytes(original_lake)
                        lake.unlink()
                        lake.symlink_to(replacement)
                    with patch.object(sys, "argv", arguments + ["--resume"]):
                        with self.assertRaisesRegex(ValueError, "Resume inputs, compiler, or backend bytes changed"):
                            optimizer.main()
                    self.assertEqual(identity_path.read_bytes(), identity_before)
                    self.assertEqual(journal_path.read_bytes(), journal_before)
                    self.assertEqual(json.loads(identity_before)["lake_binary"],
                                     str(selected_lake.resolve()) if mutation == "selected_toolchain"
                                     else str(lake))
                    self.assertEqual(analyze.call_count, 1)
                self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)

    def test_main_fixture_uses_its_own_time_executable(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A",))
            (root / "bin/time").chmod(0o644)
            with patch.object(sys, "argv", arguments), \
                    patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.shutil, "which", return_value="/missing-system-gtime"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=time_version_stub) as version_probe, \
                    patch.object(optimizer, "run_command", side_effect=environment_stub), \
                    patch.object(optimizer.Tools, "run",
                                 return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "External Lake mocked"}), \
                    patch.object(optimizer, "artifact_receipt",
                                 return_value=[{"external_artifacts_mock": True}]), \
                    patch.object(optimizer, "analyze_batch",
                                 side_effect=mock_no_change_proposals), \
                    patch.object(optimizer, "compile_arm",
                                 side_effect=AssertionError("Unexpected Lean compilation")), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(optimizer.main(), 0)
            version_probe.assert_any_call([str(root / "bin/time"), "--version"],
                                          stderr=subprocess.STDOUT)
            self.assertEqual(sum(call.args[0] == [str(root / "bin/time"), "--version"]
                                 for call in version_probe.call_args_list), 1)
            self.assertEqual(optimizer.read_json(root / "output/run.json")["time_binary"],
                             str(root / "bin/time"))
            self.assertEqual(json.loads((root / "output/results.jsonl").read_text())["status"],
                             "no_change")
            self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_manifest_validator_only_change_rejects_resume(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A",))
            scripts = root / "scripts"
            scripts.mkdir()
            original_script = Path(optimizer.__file__)
            script = scripts / original_script.name
            script.write_bytes(original_script.read_bytes())
            validator = scripts / "generate_import_inventory.py"
            validator.write_bytes(original_script.with_name(validator.name).read_bytes())
            validator_before = optimizer.sha256(validator)
            with patch.object(optimizer, "__file__", str(script)), \
                    patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=environment_stub), \
                    patch.object(optimizer.Tools, "run", return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "External Lake mocked"}), \
                    patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                    patch.object(optimizer, "analyze_batch", side_effect=mock_no_change_proposals) as analyze, \
                    patch.object(optimizer, "compile_arm", side_effect=AssertionError("Unexpected Lean compilation")), \
                    contextlib.redirect_stdout(io.StringIO()):
                with patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                identity_path = root / "output/run.json"
                identity_before = identity_path.read_bytes()
                journal = (root / "output/results.jsonl").read_bytes()
                self.assertEqual(json.loads(journal)["status"], "no_change")
                with patch.object(sys, "argv", arguments + ["--resume"]):
                    self.assertEqual(optimizer.main(), 0)
                self.assertEqual(identity_path.read_bytes(), identity_before)
                self.assertEqual(analyze.call_count, 1)
                policy = b'"helper_readonly",'
                self.assertEqual(validator.read_bytes().count(policy), 1)
                validator.write_bytes(validator.read_bytes().replace(
                    policy, b'"fixture_readonly", "helper_readonly",', 1))
                self.assertNotEqual(optimizer.sha256(validator), validator_before)
                with patch.object(sys, "argv", arguments + ["--resume"]):
                    with self.assertRaisesRegex(ValueError, "Resume inputs, compiler, or backend bytes changed"):
                        optimizer.main()
                self.assertEqual(json.loads(identity_before)["manifest_validator_sha256"], validator_before)
                self.assertEqual(identity_path.read_bytes(), identity_before)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
                self.assertEqual(analyze.call_count, 1)
            self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
            self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_missing_run_identity_rejects_resume_before_commands(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A",)) + ["--resume"]
            output = root / "output"
            output.mkdir()
            (output / "results.jsonl").write_text(json.dumps({
                "path": "A.lean", "status": "no_change", "source_sha256": digest(ORIGINAL),
            }) + "\n")
            with patch.object(sys, "argv", arguments), \
                    patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer, "run_command",
                                 side_effect=AssertionError("Resume issued commands")):
                with self.assertRaises(ValueError):
                    optimizer.main()
            self.assertFalse((output / "run.json").exists())

    def test_torn_final_record_preserves_prefix_but_interior_corruption_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            journal = Path(directory).resolve() / "results.jsonl"
            row = {"path": "A.lean", "status": "no_change", "source_sha256": digest(ORIGINAL)}
            prefix = (json.dumps(row) + "\n").encode()
            journal.write_bytes(prefix + b'{"path":"B.lean","status":"ver')
            completed = optimizer.read_journal(journal, {"A.lean": digest(ORIGINAL)})
            self.assertEqual(completed, {"A.lean": row})
            self.assertEqual(journal.read_bytes(), prefix)
            journal.write_bytes(prefix + b'{"path":broken}\n' + prefix)
            with self.assertRaises(ValueError):
                optimizer.read_journal(journal, {"A.lean": digest(ORIGINAL)})


def live(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    try:
        return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0] != "Z"
    except FileNotFoundError:
        return True


class ProcessRecoveryTests(unittest.TestCase):
    def test_darwin_zombie_only_permission_error_preserves_term_cleanup(self) -> None:
        real_killpg = os.killpg
        observed: list[int] = []

        def darwin_killpg(pgid: int, sig: int) -> None:
            if sig == signal.SIGKILL:
                # The child and ps snapshot are real; only Darwin's zombie-only
                # EPERM is injected when running this regression on Linux.
                self.assertTrue(optimizer._owned_group_only_has_zombies(pgid))
                observed.append(pgid)
                raise PermissionError(1, "Operation not permitted")
            real_killpg(pgid, sig)

        with patch.object(optimizer.sys, "platform", "darwin"), \
                patch.object(optimizer.os, "killpg", side_effect=darwin_killpg):
            self.test_timeout_preserves_real_term_handler_cleanup()
        self.assertEqual(len(observed), 1)
        self.assertFalse(live(observed[0]))

    def test_term_handler_cleanup_with_portable_ps_observation(self) -> None:
        with patch.object(optimizer.os, "waitid", None, create=True):
            self.test_timeout_preserves_real_term_handler_cleanup()

    def test_timeout_preserves_real_term_handler_cleanup(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cleanup = root / "term-cleanup.txt"
            source = (
                "import signal,sys,time\nfrom pathlib import Path\n"
                "def finish(*_):\n"
                "    time.sleep(0.15)\n"
                "    Path(sys.argv[1]).write_text('TERM cleanup finished')\n"
                "    raise SystemExit(0)\n"
                "signal.signal(signal.SIGTERM,finish)\n"
                "print('ready',flush=True)\ntime.sleep(90)\n"
            )
            result = optimizer.run_command([sys.executable, "-c", source, str(cleanup)], root,
                                           root / "command", dict(os.environ), 1)
            self.assertEqual(result["exit_code"], 124)
            self.assertTrue(result["timed_out"])
            self.assertEqual(cleanup.read_text(), "TERM cleanup finished")
            with self.assertRaisesRegex(ValueError, "completion"):
                optimizer.require_success(result)

    def test_live_child_is_detected_without_procfs(self) -> None:
        child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(90)"],
                                 start_new_session=True)
        proc_stat = Path(f"/proc/{child.pid}/stat")
        original_read = Path.read_text

        def without_proc(path: Path, *args: object, **kwargs: object) -> str:
            if path == proc_stat:
                raise FileNotFoundError(str(path))
            return original_read(path, *args, **kwargs)

        try:
            self.assertIsNone(child.poll())
            os.kill(child.pid, 0)
            with patch.object(Path, "read_text", without_proc):
                self.assertTrue(live(child.pid))
        finally:
            child.kill()
            child.wait(timeout=5)
        with patch.object(Path, "read_text", without_proc):
            self.assertFalse(live(child.pid))

    def test_normal_exit_and_timeout_leave_no_live_descendant(self) -> None:
        for wait in (False, True):
            with self.subTest(timeout=wait), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                sleeper = ("import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);"
                           "time.sleep(90)")
                source = (
                    "import json,os,subprocess,sys,time;"
                    f"p=subprocess.Popen([sys.executable,'-c',{sleeper!r}]);"
                    "print(json.dumps({'pid':p.pid,'pgid':os.getpgrp()}),flush=True);"
                    + ("time.sleep(90)" if wait else "")
                )
                result = optimizer.run_command([sys.executable, "-c", source], root,
                                               root / "command", dict(os.environ), 1 if wait else 5)
                children = json.loads((root / "command.stdout").read_text())
                pid, pgid = children["pid"], children["pgid"]
                try:
                    deadline = time.monotonic() + 1
                    while live(pid) and time.monotonic() < deadline:
                        time.sleep(0.02)
                    self.assertEqual(result["exit_code"], 124 if wait else 0)
                    self.assertEqual(result["timed_out"], wait)
                    self.assertFalse(live(pid))
                finally:
                    if live(pid):
                        self.assertNotEqual(pgid, os.getpgrp())
                        self.assertEqual(os.getpgid(pid), pgid)
                        os.killpg(pgid, signal.SIGKILL)
                        deadline = time.monotonic() + 1
                        while live(pid) and time.monotonic() < deadline:
                            time.sleep(0.02)
                    self.assertFalse(live(pid), "Owned test child survived cleanup")


class OwnedProcessGroupCleanupTests(unittest.TestCase):
    """Ordering tests use a fake process; the existing real-child tests check liveness."""

    @contextlib.contextmanager
    def process(self, mode: str, *, denied: bool = False, parent_group: bool = False,
                reused: bool = False, exited: bool = True) -> Iterator[tuple[Path, list[tuple[object, ...]]]]:
        events: list[tuple[object, ...]] = []
        group = 23145 if parent_group else 423145

        class Child:
            pid = group
            returncode: int | None = None
            waits = 0

            def wait(self, timeout: int | None = None) -> int:
                events.append(("wait", timeout))
                self.waits += 1
                if self.waits == 1 and mode == "timeout":
                    raise subprocess.TimeoutExpired(["test-only"], timeout)
                if self.waits == 1 and mode == "interrupt":
                    raise KeyboardInterrupt
                self.returncode = 0 if mode == "normal" else -signal.SIGKILL
                events.append(("reap",))
                return self.returncode

            def poll(self) -> int | None:
                raise AssertionError("poll may reap the owned leader before group termination")

        child = Child()

        def signal_group(pgid: int, sig: int) -> None:
            events.append(("signal", pgid, sig))
            if denied or (mode != "normal" and sig == signal.SIGKILL and ("reap",) in events):
                raise PermissionError(1, "Operation not permitted")

        def group_of(pid: int) -> int:
            events.append(("getpgid", pid))
            if reused:
                return group
            raise ProcessLookupError

        def observe(pid: int, _timeout: float = 1.0) -> bool:
            self.assertNotIn(("reap",), events)
            self.assertEqual(pid, group)
            events.append(("observe", pid))
            return exited

        with tempfile.TemporaryDirectory() as directory, \
                patch.object(optimizer.subprocess, "Popen", return_value=child) as spawn, \
                patch.object(optimizer.os, "getpgrp", return_value=23145), \
                patch.object(optimizer.os, "getpgid", side_effect=group_of), \
                patch.object(optimizer, "_owned_child_exited_without_reaping", side_effect=observe), \
                patch.object(optimizer.os, "killpg", side_effect=signal_group):
            root = Path(directory)
            yield root, events
            self.assertTrue(spawn.call_args.kwargs["start_new_session"])

    def test_timeout_kills_once_before_reap(self) -> None:
        with self.process("timeout") as (root, events):
            result = optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            signals = [event for event in events if event[0] == "signal"]
            self.assertEqual(signals, [("signal", 423145, signal.SIGTERM),
                                       ("signal", 423145, signal.SIGKILL)])
            self.assertLess(events.index(("observe", 423145)), events.index(signals[1]))
            self.assertLess(events.index(signals[1]), events.index(("reap",)))
            self.assertEqual([event for event in events if event[0] == "wait"], [("wait", 1), ("wait", None)])
            self.assertEqual(result["exit_code"], 124)
            self.assertTrue(result["timed_out"])
            self.assertTrue(result["remaining_group_killed"])

    def test_interrupt_kills_once_before_reap_and_reraises(self) -> None:
        with self.process("interrupt") as (root, events):
            with self.assertRaises(KeyboardInterrupt):
                optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            signals = [event for event in events if event[0] == "signal"]
            self.assertEqual(signals, [("signal", 423145, signal.SIGKILL)])
            self.assertLess(events.index(signals[0]), events.index(("reap",)))

    def test_normal_exit_still_cleans_owned_group(self) -> None:
        with self.process("normal") as (root, events):
            result = optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            self.assertEqual([event for event in events if event[0] == "signal"],
                             [("signal", 423145, signal.SIGKILL)])
            self.assertEqual(result["exit_code"], 0)
            self.assertFalse(result["timed_out"])
            self.assertTrue(result["remaining_group_killed"])

    def test_permission_error_never_reports_completion(self) -> None:
        with self.process("timeout", denied=True) as (root, events), \
                patch.object(optimizer, "_owned_group_only_has_zombies", return_value=False):
            with self.assertRaises(PermissionError):
                optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            self.assertEqual([event[2] for event in events if event[0] == "signal"],
                             [signal.SIGTERM, signal.SIGKILL])
            self.assertNotIn(("reap",), events)
            self.assertFalse((root / "command.json").exists())

    def test_darwin_permission_error_with_live_group_never_reports_completion(self) -> None:
        with self.process("timeout", denied=True) as (root, events), \
                patch.object(optimizer.sys, "platform", "darwin"), \
                patch.object(optimizer.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, "423145 423145 Z\n423146 423145 S\n", "")):
            with self.assertRaises(PermissionError):
                optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            self.assertNotIn(("reap",), events)
            self.assertFalse((root / "command.json").exists())

    def test_parent_group_is_never_signalled(self) -> None:
        with self.process("timeout", parent_group=True) as (root, events):
            with self.assertRaisesRegex(RuntimeError, "parent process group"):
                optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            self.assertFalse(any(event[0] == "signal" for event in events))

    def test_reused_leader_pid_is_never_signalled(self) -> None:
        with self.process("normal", reused=True) as (root, events):
            with self.assertRaisesRegex(RuntimeError, "PID was reused"):
                optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            self.assertFalse(any(event[0] == "signal" for event in events))

    def test_term_grace_is_bounded_without_reaping(self) -> None:
        clock = [0.0]

        def advance(seconds: float) -> None:
            clock[0] += seconds

        with self.process("timeout", exited=False) as (root, events), \
                patch.object(optimizer.time, "monotonic", side_effect=lambda: clock[0]), \
                patch.object(optimizer.time, "sleep", side_effect=advance):
            result = optimizer.run_command(["test-only"], root, root / "command", dict(os.environ), 1)
            self.assertAlmostEqual(result["elapsed_seconds"], 10.02)
            self.assertEqual([event[2] for event in events if event[0] == "signal"],
                             [signal.SIGTERM, signal.SIGKILL])
            self.assertLess(events.index(("signal", 423145, signal.SIGKILL)), events.index(("reap",)))


class OwnedChildExitObservationTests(unittest.TestCase):
    def test_group_observation_requires_owned_zombie_leader_and_no_live_member(self) -> None:
        with patch.object(optimizer.subprocess, "run") as run:
            for output, expected in [
                    ("423145 423145 Z\n423146 423145 Z+\n7 7 S\n", True),
                    ("423145 423145 Z\n423146 423145 S\n", False),
                    ("423145 7 Z\n423146 423145 Z\n", False),
                    ("423146 423145 Z\n", False),
                    ("423145 423145 S\n", False),
                    ("423145 423145 Z\ninvalid observation\n", False),
                    ("", False)]:
                with self.subTest(output=output):
                    run.return_value = subprocess.CompletedProcess([], 0, output, "")
                    self.assertEqual(optimizer._owned_group_only_has_zombies(423145), expected)
            self.assertEqual(run.call_args.args[0], ["ps", "-A", "-o", "pid=,pgid=,stat="])
            self.assertEqual(run.call_args.kwargs["timeout"], 1.0)
            run.return_value = subprocess.CompletedProcess([], 1, "423145 423145 Z\n", "")
            self.assertFalse(optimizer._owned_group_only_has_zombies(423145))
            run.return_value = subprocess.CompletedProcess([], 0, "423145 423145 Z\n", "denied")
            self.assertFalse(optimizer._owned_group_only_has_zombies(423145))
            run.side_effect = subprocess.TimeoutExpired(["ps"], 1.0)
            with self.assertRaises(subprocess.TimeoutExpired):
                optimizer._owned_group_only_has_zombies(423145)

    def test_waitid_uses_nonreaping_exit_flags(self) -> None:
        state = type("ExitState", (), {"si_pid": 423145})()
        with patch.object(optimizer.os, "waitid", return_value=state, create=True) as waitid, \
                patch.object(optimizer.os, "P_PID", 7, create=True), \
                patch.object(optimizer.os, "WEXITED", 1, create=True), \
                patch.object(optimizer.os, "WNOHANG", 2, create=True), \
                patch.object(optimizer.os, "WNOWAIT", 4, create=True), \
                patch.object(optimizer.subprocess, "run", side_effect=AssertionError("unexpected ps")):
            self.assertTrue(optimizer._owned_child_exited_without_reaping(423145))
            waitid.assert_called_once_with(7, 423145, 7)
            waitid.return_value = None
            self.assertFalse(optimizer._owned_child_exited_without_reaping(423145))

    def test_portable_ps_distinguishes_live_and_exit_states(self) -> None:
        with patch.object(optimizer.os, "waitid", None, create=True), \
                patch.object(optimizer.subprocess, "run") as run:
            for state, expected in [("S", False), ("R+", False), ("T", False), ("Z+", True), ("X", True)]:
                run.return_value = subprocess.CompletedProcess([], 0, state + "\n", "")
                self.assertEqual(optimizer._owned_child_exited_without_reaping(423145), expected)
            self.assertEqual(run.call_args.args[0], ["ps", "-p", "423145", "-o", "stat="])
            self.assertEqual(run.call_args.kwargs["timeout"], 1.0)
            run.return_value = subprocess.CompletedProcess([], 1, "", "")
            self.assertTrue(optimizer._owned_child_exited_without_reaping(423145))
            run.return_value = subprocess.CompletedProcess([], 1, "", "permission denied")
            with self.assertRaises(RuntimeError):
                optimizer._owned_child_exited_without_reaping(423145)

    def test_unsupported_waitid_falls_back_but_permission_does_not(self) -> None:
        with patch.object(optimizer.os, "waitid", create=True) as waitid, \
                patch.object(optimizer.os, "P_PID", 7, create=True), \
                patch.object(optimizer.os, "WEXITED", 1, create=True), \
                patch.object(optimizer.os, "WNOHANG", 2, create=True), \
                patch.object(optimizer.os, "WNOWAIT", 4, create=True), \
                patch.object(optimizer.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "Z\n", "")) as run:
            import errno
            waitid.side_effect = OSError(errno.ENOSYS, "unsupported")
            self.assertTrue(optimizer._owned_child_exited_without_reaping(423145))
            run.reset_mock()
            waitid.side_effect = PermissionError(errno.EPERM, "not permitted")
            with self.assertRaises(PermissionError):
                optimizer._owned_child_exited_without_reaping(423145)
            run.assert_not_called()


class BatchJournalRecoveryTests(unittest.TestCase):
    def test_retry_buildable_module_refreshes_partial_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B"))
            records = [json.loads(line) for line in (root / "manifest.jsonl").read_text().splitlines()]
            headers = []
            sources = {}
            for row in records:
                name = row["module"]
                source = ORIGINAL.replace(b"def x", f"def {name}_x".encode())
                sources[name] = source
                (root / row["path"]).write_bytes(source)
                row["source_sha256"] = digest(source)
                header = native_header(root / row["path"])
                header.update(source_sha256=digest(source), source_utf8_bytes=len(source))
                headers.append(header)
            (root / "manifest.jsonl").write_text("".join(json.dumps(row) + "\n" for row in records))
            (root / "headers.jsonl").write_text("".join(json.dumps(row) + "\n" for row in headers))
            buildable = {"A"}
            analyzed = []
            compiled = []

            def lake_stub(argv: list[str], label: Path,
                          environment: dict[str, str] | None = None) -> dict[str, object]:
                label.parent.mkdir(parents=True, exist_ok=True)
                stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                code = 0
                output = ""
                if "build" in argv:
                    requested = {word.removeprefix("+") for word in argv if word.startswith("+")}
                    code = 0 if requested.issubset(buildable) else 1
                elif "shake" in argv:
                    requested = tuple(argv[index + 1] for index, word in enumerate(argv) if word == "--only")
                    analyzed.append(requested)
                    output = "".join(f"{name}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                                     for name in requested)
                else:
                    raise AssertionError(f"Unexpected Lake command: {argv}")
                stdout.write_text(output)
                stderr.write_text("Baseline fixture unavailable\n" if code else "")
                result = {"argv": argv, "cwd": str(root), "exit_code": code,
                          "timed_out": False, "remaining_group_killed": False,
                          "elapsed_seconds": 0, "stdout": str(stdout), "stderr": str(stderr)}
                optimizer.write_json(Path(str(label) + ".json"), result)
                return result

            def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                             arm: Path, artifact_root: Path | None = None,
                             source_bytes: bytes | None = None, *,
                             header_is_module: bool = True) -> dict[str, object]:
                compiled.append((relative.stem, arm.name))
                original = sources[relative.stem]
                self.assertEqual(source_bytes, original if arm.name == "baseline" else
                                 original.replace(b"import Mathlib", b"import Init"))
                return {"artifact_root": str(artifact_root), "artifacts": [{"external_artifacts_mock": True}],
                        **mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root)}

            def snapshot_stub(tools: optimizer.Tools, rows: list[dict[str, object]],
                              artifacts: Path, arm: Path, compilations: dict[str, dict[str, object]]
                              ) -> dict[str, dict[str, object]]:
                snapshots = {}
                for row in rows:
                    module = str(row["module"])
                    snapshot = SavedSnapshotRecoveryTests.snapshot(module, artifacts / f"{module}.olean")
                    snapshot["declarations"] = [{**SavedSnapshotRecoveryTests.declaration(), "name": module + "_x"}]
                    snapshots[module] = snapshot
                return snapshots

            with patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=environment_stub), \
                    patch.object(optimizer.Tools, "run", side_effect=lake_stub), \
                    patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                    patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                    patch.object(optimizer, "snapshot_batch", side_effect=snapshot_stub), \
                    contextlib.redirect_stdout(io.StringIO()):
                with patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 1)
                completed = optimizer.read_journal(root / "output/results.jsonl",
                    {row["path"]: row["source_sha256"] for row in records})
                self.assertEqual(completed["A.lean"]["status"], "verified")
                self.assertEqual(completed["B.lean"]["status"], "blocked")
                verified_a = dict(completed["A.lean"])
                self.assertEqual(analyzed, [("A",)])
                tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                    root, {}, 5, root / "bin/time", root / ".lake/lakefile-lean-j2.toml")
                optimizer.analyze_batch(tools, records[:1], {header["relative_path"]: header for header in headers},
                                        root / "output/batches/0")
                self.assertEqual(analyzed, [("A",)], "Covered analysis should remain reusable")
                buildable.add("B")
                with patch.object(sys, "argv", arguments + ["--resume", "--retry-blocked"]):
                    status = optimizer.main()
                completed = optimizer.read_journal(root / "output/results.jsonl",
                    {row["path"]: row["source_sha256"] for row in records})
                self.assertEqual(completed["B.lean"]["status"], "verified", completed["B.lean"].get("error"))
                self.assertEqual(status, 0)
                self.assertEqual(completed["A.lean"], verified_a)
                self.assertEqual(analyzed, [("A",), ("B",)])
                cached = optimizer.read_json(root / "output/batches/0/analysis.json")
                self.assertEqual(cached["inputs"]["sources"], {"B.lean": digest(sources["B"])})
            self.assertEqual(compiled, [("A", "baseline"), ("A", "candidate"),
                                        ("B", "baseline"), ("B", "candidate")])
            for name, source in sources.items():
                self.assertEqual((root / f"{name}.lean").read_bytes(), source)
            self.assertEqual(list(root.rglob("*.olean*")), [])

    def test_legacy_failed_source_preserves_legal_prefix_and_can_resume(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B", "C"))
            compiled = []

            def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                             arm: Path, artifact_root: Path | None = None,
                             source_bytes: bytes | None = None, *,
                             header_is_module: bool = True) -> dict[str, object]:
                compiled.append((relative.name, arm.name))
                if relative.name == "B.lean" and arm.name == "candidate":
                    self.assertEqual(source_bytes, CANDIDATE)
                    self.assertEqual((root / relative).read_bytes(), ORIGINAL)
                    optimizer.write_json(tools.output / "transaction.json", {
                        "path": str(relative), "backup": str(arm.parent / "original.lean"),
                        "source_sha256": digest(ORIGINAL), "candidate_sha256": digest(CANDIDATE),
                    })
                    (root / relative).write_bytes(CANDIDATE[:17])
                    raise OSError("Injected legacy transaction during B compilation")
                return {"external_lean_mock": True}

            with patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=environment_stub), \
                    patch.object(optimizer.Tools, "run", return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "External Lake mocked"}), \
                    patch.object(optimizer, "artifact_receipt", return_value=[{"external_lean_mock": True}]), \
                    patch.object(optimizer, "analyze_batch", side_effect=mock_changed_proposals) as analyze, \
                    patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                    patch.object(optimizer, "snapshot_batch", side_effect=AssertionError("Snapshot used unrecovered sources")), \
                    contextlib.redirect_stdout(io.StringIO()):
                with patch.object(sys, "argv", arguments), self.assertRaises(ValueError):
                    optimizer.main()
                self.assertEqual(compiled, [("A.lean", "baseline"), ("A.lean", "candidate"),
                                            ("B.lean", "baseline"), ("B.lean", "candidate")])
                self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
                self.assertEqual((root / "B.lean").read_bytes(), CANDIDATE[:17])
                transaction_path = root / "output/transaction.json"
                transaction = optimizer.read_json(transaction_path)
                self.assertEqual(transaction["path"], "B.lean")
                self.assertEqual(Path(str(transaction["backup"])).read_bytes(), ORIGINAL)
                sources = {name + ".lean": digest(ORIGINAL) for name in ("A", "B", "C")}
                journal = root / "output/results.jsonl"
                completed = optimizer.read_journal(journal, sources)
                self.assertEqual(completed["A.lean"]["status"], "blocked")
                self.assertNotIn("B.lean", completed)
                self.assertNotIn("C.lean", completed)
                self.assertEqual((root / "C.lean").read_bytes(), ORIGINAL)
                self.assertTrue(transaction_path.is_file())
                (root / "B.lean").write_bytes(Path(str(transaction["backup"])).read_bytes())
                analyze.side_effect = mock_no_change_proposals
                with patch.object(sys, "argv", arguments + ["--resume"]):
                    self.assertEqual(optimizer.main(), 1)
                self.assertFalse(transaction_path.exists())
                completed = optimizer.read_journal(journal, sources)
                self.assertEqual(completed["B.lean"]["status"], "no_change")
                self.assertEqual(completed["C.lean"]["status"], "no_change")
                with patch.object(sys, "argv", arguments + ["--resume", "--retry-blocked"]):
                    self.assertEqual(optimizer.main(), 0)
                completed = optimizer.read_journal(journal, sources)
                self.assertEqual({row["status"] for row in completed.values()}, {"no_change"})
            self.assertEqual(len(compiled), 4)
            self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
            self.assertEqual((root / "B.lean").read_bytes(), ORIGINAL)


class SavedSnapshotRecoveryTests(unittest.TestCase):
    @staticmethod
    def declaration() -> dict[str, object]:
        return {"name": "A.x", "level_params": [], "kind": "definition", "type": "Nat",
                "value": "Nat.zero", "is_unsafe": False, "is_partial": False,
                "is_exported": True, "is_private_name": False, "axioms": []}

    @classmethod
    def snapshot(cls, module: str, artifact: Path, count: int = 1) -> dict[str, object]:
        return {"module": module, "declaration_count": count,
                "declarations": [cls.declaration()] if count else [],
                "resolved_olean": str(artifact), "uses_module_system": True,
                "loaded_module_count": 1, "loaded_modules": [module]}

    @classmethod
    def evidence(cls, output: Path, count: int = 1) -> tuple[dict[str, object], Path]:
        directory = output / "attempt"
        directory.mkdir()
        (directory / "original.lean").write_bytes(ORIGINAL)
        (directory / "candidate.lean").write_bytes(CANDIDATE)
        result = {"module": "A", "path": "A.lean", "attempt_directory": str(directory),
                  "source_sha256": digest(ORIGINAL), "candidate_sha256": digest(CANDIDATE),
                  "declaration_count": count}
        setup = output / "production.setup.json"
        dependency = output / "fixture-import-part"
        dependency.write_bytes(b"Explicitly mocked imported module bytes\n")
        optimizer.write_json(setup, {"name": "A", "isModule": True,
                                    "importArts": {"Mathlib": [[str(dependency)], []]}})
        tools = optimizer.Tools(output, output, output / "lake", output / "lean", output, {}, 5,
                                time_binary=output / "time")
        result.update(setup_path=str(setup), setup_root=str(output), setup_sha256=optimizer.sha256(setup))
        native = directory / "native-header.json"
        optimizer.write_json(native, native_header(output / "A.lean"))
        result["native_header"] = optimizer.file_pin(native)
        for arm, filename, pin in (("baseline", "owned-before.json", "owned_before_sha256"),
                                   ("candidate", "owned-after.json", "owned_after_sha256")):
            artifact_root = directory / arm / "artifacts"
            snapshot = cls.snapshot("A", artifact_root / "A.olean", count)
            optimizer.write_json(directory / filename, snapshot)
            result[pin] = optimizer.sha256(directory / filename)
            result[arm] = {"artifact_root": str(artifact_root),
                           "artifacts": [{"external_artifacts_mock": True}],
                           **mock_arm_inputs(tools, setup, directory / arm, Path("A.lean"),
                                             ORIGINAL if arm == "baseline" else CANDIDATE)}
        bind_saved_fixture_proposal(result, tools)
        return result, directory

    @staticmethod
    def mutate_snapshot(directory: Path, filename: str,
                        update: dict[str, object]) -> None:
        snapshot = optimizer.read_json(directory / filename)
        snapshot.update(update)
        optimizer.write_json(directory / filename, snapshot)

    def test_valid_zero_and_one_owner_metadata_are_accepted(self) -> None:
        for count in (0, 1):
            with self.subTest(count=count), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, _ = self.evidence(output, count)
                with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                    verify_saved_fixture(result, output)
                self.assertEqual(list(output.rglob("*.olean*")), [])

    def test_identically_changed_saved_snapshots_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory).resolve()
            result, attempt = self.evidence(output)
            changed = self.declaration()
            changed["type"] = "Int"
            for filename in ("owned-before.json", "owned-after.json"):
                self.mutate_snapshot(attempt, filename, {"declarations": [changed]})
            with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                with self.assertRaises(ValueError):
                    verify_saved_fixture(result, output)

    def test_erased_owners_with_matching_hashes_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory).resolve()
            result, attempt = self.evidence(output)
            for filename, pin in (("owned-before.json", "owned_before_sha256"),
                                   ("owned-after.json", "owned_after_sha256")):
                self.mutate_snapshot(attempt, filename, {"declarations": []})
                result[pin] = optimizer.sha256(attempt / filename)
            with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                with self.assertRaises(ValueError):
                    verify_saved_fixture(result, output)

    def test_missing_fields_and_duplicate_owners_are_rejected(self) -> None:
        for defect in ("missing_field", "duplicate_owner"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, attempt = self.evidence(output)
                declaration = self.declaration()
                if defect == "missing_field":
                    del declaration["type"]
                    declarations = [declaration]
                else:
                    declarations = [declaration, dict(declaration)]
                    result["declaration_count"] = 2
                for filename, pin in (("owned-before.json", "owned_before_sha256"),
                                       ("owned-after.json", "owned_after_sha256")):
                    self.mutate_snapshot(attempt, filename, {"declarations": declarations,
                                                           "declaration_count": len(declarations)})
                    result[pin] = optimizer.sha256(attempt / filename)
                with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                    with self.assertRaises(ValueError):
                        verify_saved_fixture(result, output)

    def test_single_and_deferred_results_pin_snapshots_at_creation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            output.mkdir()
            (root / "A.lean").write_bytes(ORIGINAL)
            dependency = root / "fixture-import-part"
            dependency.write_bytes(b"Explicitly mocked imported module bytes\n")
            optimizer.write_json(root / ".lake/build/ir/A.setup.json", {
                "name": "A", "isModule": True,
                "importArts": {"Mathlib": [[str(dependency)], []], "Init": [[], []]}})
            tools = optimizer.Tools(root, output, root / "lake", root / "lean", root, {}, 5,
                                    time_binary=root / "time")
            row = {"path": "A.lean", "module": "A", "source_sha256": digest(ORIGINAL)}
            header = native_header(root / "A.lean")
            parts = [{"external_artifacts_mock": True}]

            def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                             arm: Path, artifact_root: Path | None = None,
                             source_bytes: bytes | None = None, *,
                             header_is_module: bool = True) -> dict[str, object]:
                return {"artifact_root": str(artifact_root or arm / "artifacts"), "artifacts": parts,
                        **mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root)}

            def single_snapshot(tools: optimizer.Tools, module: str,
                                relative: Path, arm: Path, compilation: dict[str, object]) -> dict[str, object]:
                return self.snapshot(module, arm / "artifacts" / relative.with_suffix(".olean"))

            def batch_snapshot(tools: optimizer.Tools, rows: list[dict[str, object]],
                               artifacts: Path, arm: Path, compilations: dict[str, dict[str, object]]
                               ) -> dict[str, dict[str, object]]:
                for compilation in compilations.values():
                    compilation["snapshot_input_manifest"] = optimizer.pin_snapshot_inputs(tools, artifacts)
                    compilation["snapshot_setup"] = optimizer.pin_snapshot_setup(tools, artifacts, rows, compilations)
                snapshot = self.snapshot("A", artifacts / "A.olean")
                snapshot.update(batch_modules=["A"], batch_module_count=1, loaded_modules_scope="whole_batch")
                return {"A": snapshot}

            with patch.object(optimizer.Tools, "run", return_value={"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "stderr": "External Lake mocked"}), \
                    patch.object(optimizer, "artifact_receipt", return_value=parts), \
                    patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                    patch.object(optimizer, "snapshot_arm", side_effect=single_snapshot), \
                    patch.object(optimizer, "snapshot_batch", side_effect=batch_snapshot):
                tools.lean.write_text("Compiler identity fixture, never executed\n")
                proposal = mock_changed_proposals(tools, [row], {"A.lean": header}, output)["A.lean"]
                single = optimizer.optimize_one(tools, row, header, proposal)
                shared = optimizer.optimize_batch(tools, [row], {"A.lean": header},
                    {"A.lean": proposal}, {"A.lean": {"exit_code": 0, "timed_out": False, "remaining_group_killed": False}}, output / "batch")["A.lean"]
            for result in (single, shared):
                self.assertEqual(result["status"], "verified")
                attempt = Path(str(result["attempt_directory"]))
                self.assertEqual(result["owned_before_sha256"], optimizer.sha256(attempt / "owned-before.json"))
                self.assertEqual(result["owned_after_sha256"], optimizer.sha256(attempt / "owned-after.json"))
            self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)
            self.assertEqual(list(output.rglob("*.olean*")), [])


if __name__ == "__main__":
    unittest.main()
