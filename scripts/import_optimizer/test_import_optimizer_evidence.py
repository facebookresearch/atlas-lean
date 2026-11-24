#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Resume evidence controls; external Lean/Lake calls are explicitly mocked."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_recovery as recovery
from test_import_optimizer_recovery import (
    CANDIDATE, ORIGINAL, digest, environment_stub,
    main_inputs, native_header,
)


def file_pin(path: Path) -> dict[str, object]:
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": optimizer.sha256(path)}


class AnalysisResumeTests(unittest.TestCase):
    @staticmethod
    def change_source(root: Path, source: bytes, is_module: bool) -> None:
        (root / "A.lean").write_bytes(source)
        row = json.loads((root / "manifest.jsonl").read_text())
        row["source_sha256"] = digest(source)
        (root / "manifest.jsonl").write_text(json.dumps(row) + "\n")
        header = native_header(root / "A.lean", source, is_module=is_module)
        (root / "headers.jsonl").write_text(json.dumps(header) + "\n")
        setup = root / ".lake/build/ir/A.setup.json"
        metadata = optimizer.read_json(setup)
        metadata["isModule"] = is_module
        optimizer.write_json(setup, metadata)

    @contextlib.contextmanager
    def external_cli(self, root: Path, buildable: set[str], analyzed: list[Path]):
        def external(argv: list[str], label: Path,
                     environment: dict[str, str] | None = None) -> dict[str, object]:
            label.parent.mkdir(parents=True, exist_ok=True)
            stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
            code, output = 0, ""
            if "build" in argv:
                requested = {word[1:] for word in argv if word.startswith("+")}
                code = 0 if requested <= buildable else 1
            elif "shake" in argv:
                modules = [argv[index + 1] for index, word in enumerate(argv) if word == "--only"]
                output = "".join(f"{module}.lean:\n" for module in modules)
                analyzed.append(stdout)
            elif "--run" in argv and argv[-2].endswith("legacy.lean"):
                output = json.dumps({"module": argv[-1], "required_modules": ["Mathlib"]})
                analyzed.append(stdout)
            else:
                raise AssertionError(f"Unexpected external call: {argv}")
            stdout.write_text(output)
            stderr.write_text("Mock baseline unavailable\n" if code else "")
            result = {"argv": argv, "cwd": str(root), "exit_code": code,
                      "timed_out": False, "remaining_group_killed": False,
                      "elapsed_seconds": 0, "stdout": str(stdout), "stderr": str(stderr)}
            optimizer.write_json(Path(str(label) + ".json"), result)
            return result

        with patch.object(optimizer.signal, "signal"), \
                patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                patch.object(optimizer, "run_command", side_effect=environment_stub), \
                patch.object(optimizer.Tools, "run", side_effect=external), \
                patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                patch.object(optimizer, "compile_arm", side_effect=AssertionError("No-change must not compile")), \
                patch.object(optimizer, "snapshot_batch", side_effect=AssertionError("No-change must not snapshot")), \
                contextlib.redirect_stdout(io.StringIO()):
            yield

    def invoke(self, arguments: list[str]) -> int:
        with patch.object(sys, "argv", arguments):
            return optimizer.main()

    def test_modern_no_change_retains_proposal_receipt_and_reuses_resume(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A",))
            analyzed: list[Path] = []
            with self.external_cli(root, {"A"}, analyzed):
                self.assertEqual(self.invoke(arguments), 0)
                journal = (root / "output/results.jsonl").read_bytes()
                result = json.loads(journal)
                self.assertEqual(result["status"], "no_change")
                self.assertIsInstance(result.get("proposal_receipt"), dict)
                self.assertEqual(self.invoke([*arguments, "--resume"]), 0)
            self.assertEqual(len(analyzed), 1)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_aliased_tempdir_keeps_analysis_receipts_and_resume_valid(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            physical = Path(directory).resolve()
            alias = physical / "temporary-alias"
            alias.symlink_to(physical, target_is_directory=True)
            self.assertTrue(alias.is_symlink())
            self.assertTrue(alias.samefile(physical))
            self.assertNotEqual(alias, alias.resolve())
            with patch.object(tempfile, "tempdir", str(alias)):
                self.test_modern_no_change_retains_proposal_receipt_and_reuses_resume()

    def test_no_change_resume_rejects_changed_analysis_before_journal_write(self) -> None:
        for mutation in ("stdout", "stderr", "command", "delete", "proposal", "missing_proposal"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = main_inputs(root, ("A",))
                analyzed: list[Path] = []
                with self.external_cli(root, {"A"}, analyzed):
                    self.assertEqual(self.invoke(arguments), 0)
                    journal = (root / "output/results.jsonl").read_bytes()
                    stdout = analyzed[0]
                    target = stdout if mutation in ("stdout", "delete") else stdout.with_suffix(
                        ".stderr" if mutation == "stderr" else ".json")
                    if mutation in ("proposal", "missing_proposal"):
                        target = Path(json.loads(journal)["proposal_receipt"]["path"])
                    if mutation in ("delete", "missing_proposal"):
                        target.unlink()
                    else:
                        target.write_bytes(target.read_bytes() + b"changed evidence\n")
                    with self.assertRaises((ValueError, OSError)):
                        self.invoke([*arguments, "--resume"])
                    self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
                self.assertEqual(len(analyzed), 1)

    def test_no_change_resume_rejects_false_saved_header_with_refreshed_receipt(self) -> None:
        for mutation in ("module", "modifiers"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = main_inputs(root, ("A",))
                analyzed: list[Path] = []
                with self.external_cli(root, {"A"}, analyzed):
                    self.assertEqual(self.invoke(arguments), 0)
                    journal = root / "output/results.jsonl"
                    result = json.loads(journal.read_text())
                    receipt = Path(result["proposal_receipt"]["path"])
                    proposal = optimizer.read_json(receipt)
                    item = proposal["native_header"]["imports"][0]
                    if mutation == "module":
                        item["module"] = "Init"
                        result["old_imports"] = ["import Init"]
                    else:
                        item.update(modifiers=["public"], is_exported=True)
                        result["old_imports"] = ["public import Mathlib"]
                    optimizer.write_json(receipt, proposal)
                    result["proposal_receipt"] = file_pin(receipt)
                    journal.write_text(json.dumps(result) + "\n")
                    before = journal.read_bytes()
                    with self.assertRaisesRegex(ValueError, "Native module identity|Native import differs"):
                        self.invoke([*arguments, "--resume"])
                    self.assertEqual(journal.read_bytes(), before)
                self.assertEqual(len(analyzed), 1)

    def test_retry_blocked_preserves_prior_no_change_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A", "B"))
            buildable, analyzed = {"A"}, []
            with self.external_cli(root, buildable, analyzed):
                self.assertEqual(self.invoke(arguments), 1)
                original_output = analyzed[0].read_bytes()
                original_path = analyzed[0]
                before = optimizer.read_journal(root / "output/results.jsonl",
                    {"A.lean": digest(ORIGINAL), "B.lean": digest(ORIGINAL)})["A.lean"]
                buildable.add("B")
                self.assertEqual(self.invoke([*arguments, "--resume", "--retry-blocked"]), 0)
                self.assertEqual(original_path.read_bytes(), original_output)
                self.assertNotEqual(analyzed[0], analyzed[1])
                after = optimizer.read_journal(root / "output/results.jsonl",
                    {"A.lean": digest(ORIGINAL), "B.lean": digest(ORIGINAL)})
                self.assertEqual(after["A.lean"], before)
                self.assertEqual(after["B.lean"]["status"], "no_change")
                self.assertEqual(self.invoke([*arguments, "--resume"]), 0)
            self.assertEqual(len(analyzed), 2)

    def test_legacy_no_change_resume_checks_backend_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A",))
            source = ORIGINAL.removeprefix(b"module\n")
            self.change_source(root, source, False)
            analyzed: list[Path] = []
            with self.external_cli(root, {"A"}, analyzed):
                self.assertEqual(self.invoke(arguments), 0)
                journal = (root / "output/results.jsonl").read_bytes()
                self.assertEqual(self.invoke([*arguments, "--resume"]), 0)
                self.assertEqual(len(analyzed), 1)
                analyzed[0].write_text(json.dumps({"module": "B", "required_modules": []}))
                with self.assertRaises((ValueError, OSError)):
                    self.invoke([*arguments, "--resume"])
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
            self.assertEqual((root / "A.lean").read_bytes(), source)

    def test_source_keep_no_change_has_evidence_and_needs_no_backend(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = main_inputs(root, ("A",))
            source = b"-- shake: keep\n" + ORIGINAL.removeprefix(b"module\n")
            self.change_source(root, source, False)
            analyzed: list[Path] = []
            with self.external_cli(root, {"A"}, analyzed):
                self.assertEqual(self.invoke(arguments), 0)
                journal = (root / "output/results.jsonl").read_bytes()
                receipt = json.loads(journal)["proposal_receipt"]
                proposal = optimizer.read_json(Path(receipt["path"]))
                self.assertEqual(proposal["analysis"], {"kind": "source_keep"})
                self.assertEqual(self.invoke([*arguments, "--resume"]), 0)
            self.assertEqual(analyzed, [])
            self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)

    def test_injected_no_change_without_official_evidence_is_blocked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            main_inputs(root, ("A",))
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {}, 5, root / "bin/time")
            row = {"path": "A.lean", "module": "A", "source_sha256": digest(ORIGINAL)}
            with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                    patch.object(optimizer, "compile_arm") as compile_:
                result = optimizer.optimize_one(tools, row, native_header(root / "A.lean"),
                                                optimizer.Proposal(), {"exit_code": 0, "timed_out": False, "remaining_group_killed": False})
            self.assertEqual(result["status"], "blocked")
            self.assertIn("analysis", result["error"])
            compile_.assert_not_called()


class CompilationInputResumeTests(unittest.TestCase):
    def saved_evidence(self, output: Path) -> tuple[dict[str, object], dict[str, Path]]:
        result, attempt = recovery.SavedSnapshotRecoveryTests.evidence(output)
        inputs = {}
        for name in ("olean", "server", "private", "ir", "ir_sig", "dynlib", "plugin"):
            inputs[name] = output / ("import-" + name)
            inputs[name].write_text("Pinned external artifact fixture " + name)
        setup = output / "production.setup.json"
        optimizer.write_json(setup, {"name": "A", "isModule": True, "imports": None,
            "importArts": {"Mathlib": [[str(inputs[name]) for name in ("olean", "server", "private")],
                                       [str(inputs[name]) for name in ("ir_sig", "ir")]]},
            "dynlibs": [str(inputs["dynlib"])], "plugins": [{"path": str(inputs["plugin"]), "initFn": "init"}]})
        manifest = optimizer.pin_setup_inputs(recovery.saved_fixture_tools(output), optimizer.read_json(setup))
        result.update(setup_path=str(setup), setup_root=str(output), setup_sha256=optimizer.sha256(setup))
        for arm in ("baseline", "candidate"):
            copy = attempt / arm / "setup.json"
            copy.parent.mkdir(parents=True, exist_ok=True)
            copy.write_bytes(setup.read_bytes())
            result[arm].update(setup=file_pin(copy), setup_source=file_pin(setup),
                               setup_root=str(output), setup_sha256=result["setup_sha256"],
                               standard_library_root=None, input_manifest=manifest)
            recovery.bind_mock_snapshot_inputs(recovery.saved_fixture_tools(output), result[arm], Path("A.lean"))
            inputs[arm + "_setup"] = copy
        inputs["production_setup"] = setup
        recovery.bind_saved_fixture_proposal(result, recovery.saved_fixture_tools(output))
        return result, inputs

    def test_saved_candidate_rejects_setup_and_import_mutations(self) -> None:
        for name in ("baseline_setup", "candidate_setup", "production_setup", "olean", "server",
                     "private", "ir", "ir_sig", "dynlib", "plugin"):
            with self.subTest(input=name), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, inputs = self.saved_evidence(output)
                with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                    recovery.verify_saved_fixture(result, output)
                    inputs[name].write_bytes(inputs[name].read_bytes() + b"changed")
                    with self.assertRaises((ValueError, OSError)):
                        recovery.verify_saved_fixture(result, output)

    def test_saved_candidate_rejects_missing_or_mismatched_input_receipts(self) -> None:
        for field in ("setup", "setup_sha256", "setup_source", "setup_root", "standard_library_root", "input_manifest"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, _ = self.saved_evidence(output)
                del result["candidate"][field]
                with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                    with self.assertRaises((ValueError, OSError)):
                        recovery.verify_saved_fixture(result, output)

    def test_saved_manifest_must_cover_every_declared_setup_input(self) -> None:
        for mutation in ("omit", "duplicate", "reorder", "wrong_path", "empty"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                output = Path(directory).resolve()
                result, _ = self.saved_evidence(output)
                original = Path(result["baseline"]["input_manifest"]["path"])
                manifest = output / "baseline-structural-manifest.json"
                manifest.write_bytes(original.read_bytes())
                result["baseline"]["input_manifest"] = file_pin(manifest)
                recovery.bind_mock_snapshot_inputs(recovery.saved_fixture_tools(output),
                                                   result["baseline"], Path("A.lean"))
                with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                        patch.object(optimizer, "verify_input_manifest", wraps=optimizer.verify_input_manifest) as checked:
                    recovery.verify_saved_fixture(result, output)
                    self.assertEqual(checked.call_count, 6)
                    for arm in ("baseline", "candidate"):
                        self.assertEqual([call.args[0] for call in checked.call_args_list].count(
                            result[arm]["input_manifest"]), 2)
                files = optimizer.read_json(manifest)["files"]
                if mutation == "omit":
                    files.pop()
                elif mutation == "duplicate":
                    files.append(files[-1])
                elif mutation == "reorder":
                    files.reverse()
                elif mutation == "wrong_path":
                    files[0] = file_pin(output / "production.setup.json")
                else:
                    files.clear()
                optimizer.write_json(manifest, {"files": files})
                result["baseline"]["input_manifest"] = file_pin(manifest)
                with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                        patch.object(optimizer, "verify_input_manifest", wraps=optimizer.verify_input_manifest) as checked:
                    with self.assertRaisesRegex(ValueError, "manifest"):
                        recovery.verify_saved_fixture(result, output)
                    self.assertEqual(checked.call_count, 1)

    def test_shared_input_hash_cache_rehashes_metadata_changes_without_overwrite(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            imported = root / "imported-artifact"
            imported.write_bytes(b"External artifact fixture\n")
            tools = optimizer.Tools(root, root / "output", root / "lake", root / "lean", root, {}, 5,
                                    time_binary=root / "time")
            metadata = {"importArts": {"Mathlib": [[str(imported)], []]},
                        "plugins": [str(imported), {"path": str(imported), "initFn": "init"}],
                        "dynlibs": [str(imported)]}
            actual_hash, calls = optimizer.sha256, []

            def counted(path: Path) -> str:
                if path == imported:
                    calls.append(optimizer.source_identity(path))
                return actual_hash(path)

            with patch.object(optimizer, "sha256", side_effect=counted):
                first = optimizer.pin_setup_inputs(tools, metadata)
                manifest = Path(first["path"])
                original, identity = manifest.read_bytes(), optimizer.source_identity(manifest)
                self.assertEqual(optimizer.pin_setup_inputs(tools, metadata), first)
                self.assertEqual(len(calls), 1)
                imported.chmod(0o444)
                self.assertEqual(optimizer.pin_setup_inputs(tools, metadata), first)
                self.assertEqual(len(calls), 2)
                imported.chmod(0o644)
                imported.write_bytes(b"Changed dependency fixture\n")
                with self.assertRaisesRegex(ValueError, "evidence file changed"):
                    optimizer.pin_setup_inputs(tools, metadata)
                self.assertEqual(manifest.read_bytes(), original)
                self.assertEqual(optimizer.source_identity(manifest), identity)

    def test_input_edit_restore_during_compile_and_edit_during_hash_are_rejected(self) -> None:
        for phase in ("compile", "hash"):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                main_inputs(root, ("A",))
                imported = root / "imported-artifact"
                original = b"External artifact fixture\n"
                imported.write_bytes(original)
                setup = root / ".lake/build/ir/A.setup.json"
                optimizer.write_json(setup, {"name": "A", "isModule": True,
                    "importArts": {"Mathlib": [[str(imported)], []]}})
                tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean", root, {}, 5,
                                        time_binary=root / "bin/time")
                actual_hash = optimizer.sha256

                def mutate_hash(path: Path) -> str:
                    digest = actual_hash(path)
                    if path == imported:
                        imported.write_bytes(b"Concurrent artifact edit\n")
                    return digest

                def external(argv: list[str], label: Path,
                             environment: dict[str, str] | None = None) -> dict[str, object]:
                    imported.write_bytes(b"Transient artifact edit\n")
                    imported.write_bytes(original)
                    return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False, "external_lean_mock": True}

                with patch.object(optimizer.Tools, "run", side_effect=external), \
                        patch.object(optimizer, "artifact_receipt") as artifacts, \
                        patch.object(optimizer, "sha256", side_effect=mutate_hash if phase == "hash" else actual_hash):
                    with self.assertRaisesRegex(ValueError, "changed"):
                        optimizer.compile_arm(tools, Path("A.lean"), setup, tools.output / "baseline",
                                              source_bytes=ORIGINAL)
                    artifacts.assert_not_called()
                self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)

    def test_official_setup_arrays_and_library_plugin_forms_are_preserved(self) -> None:
        root = Path("/project")
        metadata = {"importArts": {"M": [["a", "s", "p"], ["sig", "ir"]]},
                    "plugins": ["plugin", {"path": "other", "initFn": "init"}], "dynlibs": ["dynamic"]}
        self.assertEqual(optimizer.setup_input_paths(metadata, root),
                         tuple(sorted(str(root / name) for name in ("a", "s", "p", "sig", "ir", "plugin", "other", "dynamic"))))
        for change in ({"importArts": {"M": {"olean": "a"}}},
                       {"importArts": {"M": [["a"], "ir"]}},
                       {"importArts": {"M": [[True], []]}},
                       {"dynlibs": "a"}, {"plugins": [{"initFn": "init"}]}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                optimizer.setup_input_paths({**metadata, **change}, root)

    def test_toolchain_fallback_artifacts_are_pinned_and_revalidated(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            result, _ = self.saved_evidence(root)
            library = root / "toolchain/lib/lean"
            (library / "Init").mkdir(parents=True)
            paths = [library / "Init/Core.olean", library / "Init/Core.ir",
                     library / "libleanshared.so"]
            for path in paths:
                path.write_bytes(b"External toolchain artifact fixture\n")
            metadata = optimizer.read_json(Path(result["setup_path"]))
            tools = optimizer.Tools(root, root, root / "lake", root / "lean", root,
                                    {"LEAN_SYSROOT": str(root / "toolchain")}, 5,
                                    time_binary=root / "time")
            manifest = optimizer.pin_setup_inputs(tools, metadata)
            for arm in ("baseline", "candidate"):
                result[arm].update(standard_library_root=str(library), input_manifest=manifest)
                recovery.bind_mock_snapshot_inputs(tools, result[arm], Path("A.lean"))
            recovery.bind_saved_fixture_proposal(result, tools)
            for path in paths:
                self.assertIn(str(path), [record["path"] for record in
                                         optimizer.read_json(Path(manifest["path"]))["files"]])
            with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                recovery.verify_saved_fixture(result, root, tools)
                paths[0].write_bytes(b"Changed standard-library import\n")
                with self.assertRaisesRegex(ValueError, "evidence file changed"):
                    recovery.verify_saved_fixture(result, root, tools)

    def test_main_candidate_resume_validates_inputs_without_new_children(self) -> None:
        for mutation in ("baseline_setup", "production_setup", "import"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = main_inputs(root, ("A",))
                imported = root / "imported-artifact"
                imported.write_bytes(b"External artifact fixture\n")
                setup = root / ".lake/build/ir/A.setup.json"
                optimizer.write_json(setup, {"name": "A", "isModule": True,
                                            "importArts": {"Mathlib": [[str(imported)], []]}})
                compiles, analyses = [], []

                def external(argv: list[str], label: Path,
                             environment: dict[str, str] | None = None) -> dict[str, object]:
                    label.parent.mkdir(parents=True, exist_ok=True)
                    stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                    if "shake" in argv:
                        stdout.write_text("A.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n")
                        analyses.append(label)
                    elif "build" in argv:
                        stdout.write_text("Mock prepared target\n")
                    else:
                        raise AssertionError(f"Unexpected external call: {argv}")
                    stderr.write_text("")
                    command = {"argv": argv, "cwd": str(root), "exit_code": 0,
                               "timed_out": False, "remaining_group_killed": False,
                               "stdout": str(stdout), "stderr": str(stderr)}
                    optimizer.write_json(Path(str(label) + ".json"), command)
                    return command

                def compile_stub(tools: optimizer.Tools, relative: Path, setup: Path,
                                 arm: Path, artifact_root: Path | None = None,
                                 source_bytes: bytes | None = None, *,
                                 header_is_module: bool = True) -> dict[str, object]:
                    compiles.append(arm)
                    return {"artifact_root": str(artifact_root), "artifacts": [{"external_artifacts_mock": True}],
                            **recovery.mock_arm_inputs(tools, setup, arm, relative, source_bytes, artifact_root)}

                def snapshot_stub(tools: optimizer.Tools, rows: list[dict[str, object]],
                                  artifacts: Path, arm: Path, compilations: dict[str, dict[str, object]]
                                  ) -> dict[str, dict[str, object]]:
                    return {"A": recovery.SavedSnapshotRecoveryTests.snapshot("A", artifacts / "A.olean")}

                with patch.object(optimizer.signal, "signal"), \
                        patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                        patch.object(optimizer, "run_command", side_effect=environment_stub), \
                        patch.object(optimizer.Tools, "run", side_effect=external), \
                        patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                        patch.object(optimizer, "compile_arm", side_effect=compile_stub), \
                        patch.object(optimizer, "snapshot_batch", side_effect=snapshot_stub), \
                        contextlib.redirect_stdout(io.StringIO()):
                    with patch.object(sys, "argv", arguments):
                        self.assertEqual(optimizer.main(), 0)
                    journal = (root / "output/results.jsonl").read_bytes()
                    result = json.loads(journal)
                    self.assertEqual((result["status"], result["declaration_count"]), ("verified", 1))
                    with patch.object(sys, "argv", [*arguments, "--resume"]):
                        self.assertEqual(optimizer.main(), 0)
                    target = (Path(result["baseline"]["setup"]["path"]) if mutation == "baseline_setup" else
                              setup if mutation == "production_setup" else imported)
                    target.write_bytes(target.read_bytes() + b"changed\n")
                    with patch.object(sys, "argv", [*arguments, "--resume"]):
                        with self.assertRaises((ValueError, OSError)):
                            optimizer.main()
                    self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)
                    self.assertEqual((len(compiles), len(analyses)), (2, 1))
                    self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)

    def test_compile_checks_inputs_and_uses_frozen_setup_copy(self) -> None:
        for mutation in (False, True):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                main_inputs(root, ("A",))
                imported = root / "imported-artifact"
                imported.write_bytes(b"External artifact fixture\n")
                setup = root / ".lake/build/ir/A.setup.json"
                optimizer.write_json(setup, {"name": "A", "isModule": True,
                    "importArts": {"Mathlib": [[str(imported)], []]}})
                tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                        root, {}, 5, root / "bin/time")
                observed = []

                def external(argv: list[str], label: Path,
                             environment: dict[str, str] | None = None) -> dict[str, object]:
                    copy = Path(argv[argv.index("--setup") + 1])
                    observed.append(copy)
                    self.assertEqual(copy.read_bytes(), setup.read_bytes())
                    if mutation:
                        imported.write_bytes(b"Changed while Lean was running\n")
                    Path(argv[argv.index("-o") + 1]).write_text(json.dumps({"wall_seconds": 0}) + "\n")
                    return recovery.mock_compile_command(tools, argv, label)

                with patch.object(optimizer.Tools, "run", side_effect=external), \
                        patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                    if mutation:
                        with self.assertRaises((ValueError, OSError)):
                            optimizer.compile_arm(tools, Path("A.lean"), setup, tools.output / "baseline",
                                                  source_bytes=ORIGINAL)
                    else:
                        baseline = optimizer.compile_arm(tools, Path("A.lean"), setup,
                                                         tools.output / "baseline", source_bytes=ORIGINAL)
                        candidate = optimizer.compile_arm(tools, Path("A.lean"), setup,
                                                          tools.output / "candidate", source_bytes=CANDIDATE)
                        self.assertIsInstance(baseline.get("input_manifest"), dict)
                        self.assertEqual(baseline["input_manifest"], candidate["input_manifest"])
                        self.assertTrue(all(path != setup for path in observed))
                self.assertEqual((root / "A.lean").read_bytes(), ORIGINAL)


if __name__ == "__main__":
    unittest.main()
