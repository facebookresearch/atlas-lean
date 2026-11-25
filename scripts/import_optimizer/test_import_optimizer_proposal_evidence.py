#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Changed-candidate provenance controls; all Lean/Lake execution is mocked."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tarfile
import tempfile
import unittest
from collections.abc import Callable, Iterator
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery
import test_import_optimizer_snapshot_inputs as shared


class ChangedProposalEvidenceTests(unittest.TestCase):
    @contextlib.contextmanager
    def external_cli(self, root: Path, names: tuple[str, ...] = ("A",)
                     ) -> Iterator[tuple[Callable[[list[str]], int], list[Path], list[tuple[str, object]]]]:
        arguments = recovery.main_inputs(root, names)
        calls: list[tuple[str, object]] = []
        analyzed: list[Path] = []
        marker = root / "canonical-input-marker"
        marker.write_text("Explicitly mocked canonical compilation identity\n")
        for name in names:
            if name != "A":
                (root / ("canonical-input-marker-" + name)).write_text("Explicit sibling compilation identity\n")
        with tarfile.open(shared.ARCHIVE) as archive:
            native_prefix = archive.extractfile("input/original-compiler-prefix.json")
            assert native_prefix is not None
            native_module = json.load(native_prefix)["module"]

        def artifacts(artifact_root: Path, relative: Path, **kwargs: object) -> list[dict[str, object]]:
            if artifact_root == root / ".lake/build/lib/lean":
                target = marker if relative.stem == "A" else root / ("canonical-input-marker-" + relative.stem)
                return [{"external_canonical_artifacts_mock": optimizer.sha256(target)}]
            return shared.EXTERNAL_ARTIFACTS

        def external(argv: list[str], label: Path,
                     environment: dict[str, str] | None = None) -> dict[str, object]:
            label.parent.mkdir(parents=True, exist_ok=True)
            stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
            if "shake" in argv:
                modules = [argv[i + 1] for i, word in enumerate(argv) if word == "--only"]
                calls.append(("shake", modules))
                analyzed.append(label)
                stdout.write_text("".join(f"{name}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                                          for name in modules))
            elif "build" in argv:
                calls.append(("prepare", [word[1:] for word in argv if word.startswith("+")]))
                stdout.write_text("Canonical build explicitly mocked\n")
            elif "--deps" in argv:
                modules = [line.removeprefix("import all ") for line in Path(argv[-1]).read_text().splitlines()]
                calls.append(("deps", modules))
                assert environment is not None
                stdout.write_text("".join(str(Path(environment["LEAN_PATH"]) / (name + ".olean")) + "\n"
                                          for name in modules))
            elif "--run" in argv:
                modules = argv[argv.index("--run") + 3:]
                assert environment is not None
                snapshot_setup = optimizer.read_json(Path(argv[argv.index("--run") + 2]))
                self.assertEqual(environment["LEAN_PATH"], "")
                calls.append(("snapshot", modules))
                rows = []
                for name in modules:
                    row = recovery.SavedSnapshotRecoveryTests.snapshot(name,
                        Path(snapshot_setup["importArts"][name][0][0]))
                    row["declarations"][0]["name"] = name + ".x"
                    row.update(loaded_modules=[*modules, native_module], loaded_module_count=len(modules) + 1)
                    if Path(argv[argv.index("--run") + 1]).name == "declarations_batch.lean":
                        row.update(batch_modules=modules, batch_module_count=len(modules),
                                   loaded_modules_scope="whole_batch")
                    rows.append(row)
                stdout.write_text("".join(json.dumps(row) + "\n" for row in rows))
            else:
                raise AssertionError(f"Unexpected external call: {argv}")
            stderr.write_text("")
            result = {"argv": argv, "cwd": str(root), "exit_code": 0, "timed_out": False,
                      "remaining_group_killed": False, "stdout": str(stdout), "stderr": str(stderr)}
            optimizer.write_json(Path(str(label) + ".json"), result)
            return result

        def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                         arm: Path, artifact_root: Path | None = None,
                         source_bytes: bytes | None = None, *,
                         header_is_module: bool = True) -> dict[str, object]:
            assert source_bytes is not None
            artifact_root = artifact_root or arm / "artifacts"
            calls.append(("compile", (relative.stem, arm.name)))
            outputs.physical_parts(artifact_root, relative)
            shared.native_sibling(artifact_root)
            return {"artifact_root": str(artifact_root), "artifacts": shared.EXTERNAL_ARTIFACTS,
                    **recovery.mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root)}

        def invoke(extra: list[str]) -> int:
            with patch.object(sys, "argv", [*arguments, *extra]):
                return optimizer.main()

        with patch.object(optimizer.signal, "signal"), \
                patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                patch.object(optimizer, "run_command", side_effect=recovery.environment_stub), \
                patch.object(optimizer.Tools, "run", side_effect=external), \
                patch.object(optimizer, "artifact_receipt", side_effect=artifacts), \
                patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                contextlib.redirect_stdout(io.StringIO()):
            yield invoke, analyzed, calls

    @staticmethod
    def tools(root: Path) -> optimizer.Tools:
        config = root / ".lake/lakefile-lean-j2.toml"
        return optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                               Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 5,
                               root / "bin/time", config if config.exists() else None)

    def test_resume_rejects_deleted_immutable_analysis_after_verified_candidate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.external_cli(root) as (invoke, analyzed, calls):
                self.assertEqual(invoke([]), 0)
                journal = root / "output/results.jsonl"
                original = journal.read_bytes()
                result = json.loads(original)
                self.assertEqual((result["status"], result["declaration_count"]), ("verified", 1))
                for name in ("owned-before.json", "owned-after.json"):
                    snapshot = optimizer.read_json(Path(result["attempt_directory"]) / name)
                    self.assertEqual(len(snapshot["declarations"]), 1)
                    self.assertEqual(len(snapshot["declarations"][0]), 10)
                self.assertEqual(invoke(["--resume"]), 0)
                self.assertEqual(len(analyzed), 1)
                (root / "output/batches/0/analysis.json").unlink()
                for suffix in ("json", "stdout", "stderr"):
                    Path(str(analyzed[0]) + "." + suffix).unlink()
                prior_calls = list(calls)
                with self.assertRaises((ValueError, OSError)):
                    invoke(["--resume"])
                self.assertEqual(calls, prior_calls)
                self.assertEqual(journal.read_bytes(), original)

    def test_resume_rejects_each_mutated_analysis_stream(self) -> None:
        for suffix in ("json", "stdout", "stderr"):
            with self.subTest(suffix=suffix), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with self.external_cli(root) as (invoke, analyzed, calls):
                    self.assertEqual(invoke([]), 0)
                    journal = (root / "output/results.jsonl").read_bytes()
                    target = Path(str(analyzed[0]) + "." + suffix)
                    target.write_bytes(target.read_bytes() + b"Changed official analysis evidence\n")
                    before = list(calls)
                    with self.assertRaises((ValueError, OSError)):
                        invoke(["--resume"])
                    self.assertEqual(calls, before)
                    self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_mutable_analysis_cache_is_not_required_for_completed_provenance(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.external_cli(root, ("A", "B")) as (invoke, analyzed, calls):
                self.assertEqual(invoke([]), 0)
                before = (root / "output/results.jsonl").read_bytes()
                rows = [json.loads(line) for line in before.splitlines()]
                self.assertEqual([row["status"] for row in rows], ["verified", "verified"])
                self.assertTrue(all(isinstance(row.get("proposal_receipt"), dict) for row in rows))
                (root / "output/batches/0/analysis.json").unlink()
                prior_calls = list(calls)
                self.assertEqual(invoke(["--resume"]), 0)
                self.assertEqual(calls, prior_calls)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), before)
                self.assertEqual(len(analyzed), 1)

    def test_resume_rejects_changed_canonical_analysis_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.external_cli(root) as (invoke, _, calls):
                self.assertEqual(invoke([]), 0)
                journal = (root / "output/results.jsonl").read_bytes()
                (root / "canonical-input-marker").write_text("Changed canonical compiled input\n")
                before = list(calls)
                with self.assertRaises((ValueError, OSError)):
                    invoke(["--resume"])
                self.assertEqual(calls, before)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_reparse_rejects_changed_recorded_imports_and_missing_receipt(self) -> None:
        for mutation in ("recorded_imports", "old_imports", "missing_receipt", "native_header", "native_target"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with self.external_cli(root) as (invoke, _, calls):
                    self.assertEqual(invoke([]), 0)
                    journal = root / "output/results.jsonl"
                    result = json.loads(journal.read_bytes())
                    if mutation == "recorded_imports":
                        result["added_imports"] = ["import Wrong.Provider"]
                        journal.write_text(json.dumps(result) + "\n")
                    elif mutation == "old_imports":
                        result["old_imports"] = ["public import Mathlib"]
                        journal.write_text(json.dumps(result) + "\n")
                    elif mutation == "missing_receipt":
                        result.pop("proposal_receipt", None)
                        journal.write_text(json.dumps(result) + "\n")
                    else:
                        proposal_pin = result.get("proposal_receipt")
                        self.assertIsInstance(proposal_pin, dict)
                        receipt = Path(proposal_pin["path"])
                        value = optimizer.read_json(receipt)
                        if mutation == "native_target":
                            value["native_header"]["relative_path"] = "Different.lean"
                        else:
                            value["native_header"]["imports"][0]["modifiers"] = ["public"]
                        optimizer.write_json(receipt, value)
                        result["proposal_receipt"] = optimizer.file_pin(receipt)
                        journal.write_text(json.dumps(result) + "\n")
                    before = journal.read_bytes()
                    prior_calls = list(calls)
                    with self.assertRaises((ValueError, OSError)):
                        invoke(["--resume"])
                    self.assertEqual(calls, prior_calls)
                    self.assertEqual(journal.read_bytes(), before)

    def test_saved_candidate_rejects_every_changed_shared_analysis_input(self) -> None:
        for mutation in ("source", "setup", "artifact", "dependency", "missing_input_manifest"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with self.external_cli(root, ("A", "B")) as (invoke, _, calls):
                    dependency = root / "sibling-dependency-input"
                    dependency.write_text("Original sibling dependency\n")
                    setup = root / ".lake/build/ir/B.setup.json"
                    metadata = optimizer.read_json(setup)
                    metadata["importArts"]["Sibling"] = [[str(dependency)], []]
                    optimizer.write_json(setup, metadata)
                    self.assertEqual(invoke([]), 0)
                    rows = [json.loads(line) for line in (root / "output/results.jsonl").read_text().splitlines()]
                    result = rows[0]
                    receipt = optimizer.read_json(Path(result["proposal_receipt"]["path"]))
                    self.assertEqual(set(receipt["analysis"]["inputs"]["sources"]), {"A.lean", "B.lean"})
                    optimizer.verify_saved_candidate(result, root / "output", self.tools(root))
                    before = list(calls)
                    if mutation == "source":
                        (root / "B.lean").write_bytes(recovery.ORIGINAL + b"-- edited sibling\n")
                    elif mutation == "setup":
                        metadata["options"] = {"maxRecDepth": 2048}
                        optimizer.write_json(setup, metadata)
                    elif mutation == "artifact":
                        (root / "canonical-input-marker-B").write_text("Changed sibling artifact\n")
                    elif mutation == "dependency":
                        dependency.write_text("Changed sibling dependency\n")
                    else:
                        Path(receipt["analysis"]["inputs"]["compiled_inputs"]["B.lean"]["input_manifest"]["path"]).unlink()
                    with self.assertRaises((ValueError, OSError)):
                        optimizer.verify_saved_candidate(result, root / "output", self.tools(root))
                    self.assertEqual(calls, before)

    def test_saved_candidate_regenerates_repinned_candidate_and_patch(self) -> None:
        for mutation in ("candidate", "patch", "patch_target"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with self.external_cli(root) as (invoke, _, calls):
                    self.assertEqual(invoke([]), 0)
                    result = json.loads((root / "output/results.jsonl").read_text())
                    attempt = Path(result["attempt_directory"])
                    before = list(calls)
                    if mutation == "candidate":
                        candidate = attempt / "candidate.lean"
                        candidate.write_bytes(candidate.read_bytes() + b"-- source outside the import proposal\n")
                        result["candidate_sha256"] = optimizer.sha256(candidate)
                    else:
                        saved = attempt / "proposal.patch"
                        data = saved.read_bytes()
                        saved.write_bytes(data.replace(b"a/A.lean", b"a/Other.lean") if mutation == "patch_target"
                                          else data + b"Changed patch\n")
                        result["proposal_patch_sha256"] = optimizer.sha256(saved)
                    with self.assertRaisesRegex(ValueError, "analysis does not establish"):
                        optimizer.verify_saved_candidate(result, root / "output", self.tools(root))
                    self.assertEqual(calls, before)

    def test_saved_candidate_rejects_repinned_wrong_command_and_incomplete_completion(self) -> None:
        for mutation in ("launcher", "selectors", "positional", "exit", "timeout", "leaked_child", "target_output"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with self.external_cli(root) as (invoke, _, calls):
                    self.assertEqual(invoke([]), 0)
                    result = json.loads((root / "output/results.jsonl").read_text())
                    pin = Path(result["proposal_receipt"]["path"])
                    proposal = optimizer.read_json(pin)
                    command_path = Path(proposal["analysis"]["json"]["path"])
                    command = optimizer.read_json(command_path)
                    if mutation == "launcher":
                        command["argv"][0] = str(root / "different-lake")
                    elif mutation == "selectors":
                        command["argv"][command["argv"].index("--only") + 1] = "Different"
                    elif mutation == "positional":
                        command["argv"][-1] = "Different"
                    elif mutation == "exit":
                        command["exit_code"] = 37
                    elif mutation == "timeout":
                        command["timed_out"] = True
                    elif mutation == "leaked_child":
                        command["remaining_group_members"] = [37]
                    else:
                        stdout = Path(proposal["analysis"]["stdout"]["path"])
                        stdout.write_text("Other.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n")
                        proposal["analysis"]["stdout"] = optimizer.file_pin(stdout)
                    optimizer.write_json(command_path, command)
                    proposal["analysis"]["json"] = optimizer.file_pin(command_path)
                    optimizer.write_json(pin, proposal)
                    result["proposal_receipt"] = optimizer.file_pin(pin)
                    before = list(calls)
                    with self.assertRaises(ValueError):
                        optimizer.verify_saved_candidate(result, root / "output", self.tools(root))
                    self.assertEqual(calls, before)

    def test_single_changed_path_retains_proposal_and_requires_validation_context(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.external_cli(root) as (_, analyzed, calls):
                tools = self.tools(root)
                row = json.loads((root / "manifest.jsonl").read_text())
                native = json.loads((root / "headers.jsonl").read_text())
                result = optimizer.optimize_one(tools, row, native)
                self.assertEqual((result["status"], result["declaration_count"]), ("verified", 1))
                self.assertEqual([name for name, _ in calls].count("compile"), 2)
                self.assertEqual([name for name, _ in calls].count("snapshot"), 2)
                self.assertEqual(len(analyzed), 1)
                optimizer.verify_saved_candidate(result, tools.output, tools)
                before = list(calls)
                with self.assertRaisesRegex(ValueError, "complete validation tools"):
                    optimizer.verify_saved_candidate(result, tools.output)
                Path(str(analyzed[0]) + ".stdout").unlink()
                with self.assertRaises(OSError):
                    optimizer.verify_saved_candidate(result, tools.output, tools)
                self.assertEqual(calls, before)

    def test_shared_module_names_cannot_replace_canonical_source_identities(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.external_cli(root, ("A", "B")) as (invoke, _, calls):
                self.assertEqual(invoke([]), 0)
                result = json.loads((root / "output/results.jsonl").read_text().splitlines()[0])
                tools = self.tools(root)
                setup = root / ".lake/build/ir/B.setup.json"
                metadata = optimizer.read_json(setup)
                metadata["name"] = "A"
                optimizer.write_json(setup, metadata)
                claimed = [dict(row, module="A") for row in
                           (json.loads(line) for line in (root / "manifest.jsonl").read_text().splitlines())]
                pin = Path(result["proposal_receipt"]["path"])
                proposal = optimizer.read_json(pin)
                proposal["analysis"]["inputs"] = optimizer.analysis_inputs(tools, claimed)
                self.assertEqual(set(proposal["analysis"]["inputs"]["sources"]), {"A.lean", "B.lean"})
                command_path = Path(proposal["analysis"]["json"]["path"])
                command = optimizer.read_json(command_path)
                command["argv"] = tools.lake_command("shake", "--force", "--explain", "--add-public", "--only", "A", "A")
                optimizer.write_json(command_path, command)
                stdout = Path(proposal["analysis"]["stdout"]["path"])
                stdout.write_text("A.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n")
                for suffix in ("json", "stdout"):
                    proposal["analysis"][suffix] = optimizer.file_pin(Path(proposal["analysis"][suffix]["path"]))
                optimizer.write_json(pin, proposal)
                result["proposal_receipt"] = optimizer.file_pin(pin)
                before = list(calls)
                with self.assertRaisesRegex(ValueError, "module differs from its source path"):
                    optimizer.verify_saved_candidate(result, root / "output", tools)
                self.assertEqual(calls, before)

    def test_changed_proposal_without_official_evidence_stops_before_compilation(self) -> None:
        for deferred in (False, True):
            with self.subTest(deferred=deferred), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with self.external_cli(root) as (_, analyzed, calls):
                    row = json.loads((root / "manifest.jsonl").read_text())
                    native = json.loads((root / "headers.jsonl").read_text())
                    result = optimizer.optimize_one(self.tools(root), row, native,
                        optimizer.Proposal((optimizer.ImportSpec("Mathlib"),), (optimizer.ImportSpec("Init"),)),
                        defer_snapshots=deferred)
                    self.assertEqual(result["status"], "blocked")
                    self.assertIn("analysis", result["error"])
                    self.assertEqual(analyzed, [])
                    self.assertEqual([name for name, _ in calls], ["prepare"])

    def test_official_shake_exit_one_keeps_complete_changed_evidence_valid(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with self.external_cli(root) as (invoke, _, calls):
                self.assertEqual(invoke([]), 0)
                result = json.loads((root / "output/results.jsonl").read_text())
                pin = Path(result["proposal_receipt"]["path"])
                proposal = optimizer.read_json(pin)
                command_path = Path(proposal["analysis"]["json"]["path"])
                command = optimizer.read_json(command_path)
                command["exit_code"] = 1
                optimizer.write_json(command_path, command)
                proposal["analysis"]["json"] = optimizer.file_pin(command_path)
                optimizer.write_json(pin, proposal)
                result["proposal_receipt"] = optimizer.file_pin(pin)
                before = list(calls)
                optimizer.verify_saved_candidate(result, root / "output", self.tools(root))
                self.assertEqual(calls, before)


if __name__ == "__main__":
    unittest.main()
