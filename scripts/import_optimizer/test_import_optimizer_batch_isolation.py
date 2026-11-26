#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Dependent-module controls with physical outputs and mocked native commands."""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery
from test_generate_import_inventory import header_fixture


class BatchArtifactIsolationTests(unittest.TestCase):
    def run_dependent_batch(self, fault: str) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = recovery.main_inputs(root, ("B", "A"))
            canonical = root / ".lake/build/lib/lean"
            sources = {
                "B": b"module\nimport Mathlib\npublic def B_x : Nat := 0\n",
                "A": b"module\nimport Mathlib\nimport B\npublic def A_x : Nat := B_x\n",
            }
            rows, headers = [], []
            for module, source in sources.items():
                path = root / (module + ".lean")
                path.write_bytes(source)
                rows.append({"path": path.name, "module": module,
                             "source_sha256": recovery.digest(source), "analysis_status": "pending",
                             "direct_local_dependencies": ["B"] if module == "A" else []})
                imports = (("Mathlib", ()), ("B", ())) if module == "A" else (("Mathlib", ()),)
                header = header_fixture(path, imports)
                header["relative_path"] = path.name
                headers.append(header)
                outputs.physical_parts(canonical, Path(path.name))
                optimizer.write_json(canonical / (module + ".olean"), {
                    "module": module, "dependencies": ["B"] if module == "A" else [], "axioms": [],
                })
            (root / "manifest.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
            (root / "headers.jsonl").write_text("".join(json.dumps(row) + "\n" for row in headers))
            setup = root / ".lake/build/ir/A.setup.json"
            metadata = optimizer.read_json(setup)
            metadata["importArts"]["B"] = [[str(canonical / ("B" + suffix)) for suffix in
                                            (".olean", ".olean.server", ".olean.private")],
                                           [str(canonical / ("B" + suffix)) for suffix in (".ir.sig", ".ir")]]
            optimizer.write_json(setup, metadata)
            canonical_bytes = {path: path.read_bytes() for path in canonical.iterdir()}
            commands, compiled, resolved_a = [], [], []

            def external(argv: list[str], cwd: Path, label: Path,
                         environment: dict[str, str], timeout: int) -> dict[str, object]:
                self.assertEqual(cwd, root)
                label.parent.mkdir(parents=True, exist_ok=True)
                stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                code, text, error = 0, "", ""
                commands.append({"argv": argv, "label": str(label),
                                 "lean_path": environment.get("LEAN_PATH")})
                if "env" in argv:
                    text = json.dumps({"LAKE": str(root / "bin/lake"),
                                       "LEAN_PATH": str(canonical), "LEAN_SYSROOT": str(root)}) + "\n"
                elif "build" in argv:
                    self.assertEqual({word for word in argv if word.startswith("+")}, {"+A", "+B"})
                elif "shake" in argv:
                    text = "".join(f"{module}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                                   for module in ("B", "A"))
                elif argv[0] == str(root / "bin/time"):
                    self.assertEqual(environment["LEAN_PATH"], str(canonical))
                    source = Path(argv[argv.index("-R") + 2])
                    module, arm = source.stem, label.parent.name
                    self.assertEqual(source.read_bytes(), sources[module] if arm == "baseline" else
                                     sources[module].replace(b"import Mathlib", b"import Init"))
                    compile_setup = optimizer.read_json(Path(argv[argv.index("--setup") + 1]))
                    if module == "A":
                        self.assertEqual(compile_setup["importArts"]["B"], metadata["importArts"]["B"])
                    artifacts = Path(argv[argv.index("-i") + 1]).parent
                    compiled.append((module, arm, str(artifacts)))
                    outputs.physical_parts(artifacts, Path(module + ".lean"))
                    optimizer.write_json(artifacts / (module + ".olean"), {
                        "module": module, "dependencies": ["B"] if module == "A" else [],
                        "axioms": ["Fixture.unaccepted"] if
                        module == "B" and arm == "candidate" and fault == "owned" else [],
                    })
                    if module == "B" and fault == "compile_" + arm:
                        (artifacts / "B.olean").write_bytes(b"Partial output from failed sibling compiler\n")
                        code, error = 1, "Sibling compiler failed after writing its output\n"
                    Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
                elif "--deps" in argv or "--run" in argv:
                    modules = (Path(argv[-1]).read_text().splitlines() if "--deps" in argv else
                               argv[argv.index("--run") + 3:])
                    if "--deps" in argv:
                        modules = [line.removeprefix("import all ") for line in modules]
                    loaded: dict[str, tuple[Path, dict[str, object]]] = {}
                    snapshot_setup = (optimizer.read_json(Path(argv[argv.index("--run") + 2]))
                                      if "--run" in argv else None)

                    def resolve(module: str) -> None:
                        if module in loaded:
                            return
                        choices = ([Path(snapshot_setup["importArts"][module][0][0])]
                                   if snapshot_setup else [Path(search_root) / (module + ".olean")
                                   for search_root in environment["LEAN_PATH"].split(os.pathsep)])
                        for path in choices:
                            if path.is_file():
                                record = optimizer.read_json(path)
                                self.assertEqual(record["module"], module)
                                loaded[module] = (path, record)
                                for dependency in record["dependencies"] if snapshot_setup else []:
                                    resolve(dependency)
                                return
                        raise ValueError("Missing fixture module " + module)

                    try:
                        for module in modules:
                            resolve(module)
                    except ValueError as failure:
                        code, error = 1, str(failure)
                    if not code and "A" in modules and snapshot_setup:
                        resolved_a.append({"label": str(label), "B": str(loaded["B"][0])})
                    if not code and "--deps" in argv:
                        text = "".join(str(path) + "\n" for path, _ in loaded.values())
                    elif not code:
                        if fault == "snapshot" and "B" in modules and label.parent.parent.name == "candidate":
                            code, error = 1, "Sibling snapshot helper failed\n"
                        else:
                            for module in modules:
                                snapshot = recovery.SavedSnapshotRecoveryTests.snapshot(module, loaded[module][0])
                                declaration = recovery.SavedSnapshotRecoveryTests.declaration()
                                declaration.update(name=module + "_x", value="B_x" if module == "A" else "Nat.zero",
                                                   axioms=sorted({axiom for _, record in loaded.values()
                                                                  for axiom in record["axioms"]}))
                                snapshot.update(declarations=[declaration], loaded_modules=list(loaded),
                                                loaded_module_count=len(loaded), loaded_modules_scope="whole_batch",
                                                batch_modules=modules, batch_module_count=len(modules))
                                text += json.dumps(snapshot) + "\n"
                else:
                    raise AssertionError(f"Unexpected native command: {argv}")
                stdout.write_text(text)
                stderr.write_text(error)
                command = {"argv": argv, "cwd": str(cwd), "exit_code": code,
                           "timed_out": False, "remaining_group_killed": False, "elapsed_seconds": 0,
                           "stdout": str(stdout), "stderr": str(stderr), "external_native_mock": True}
                optimizer.write_json(Path(str(label) + ".json"), command)
                return command

            output = io.StringIO()
            with patch.object(optimizer.signal, "signal"), \
                    patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
                    patch.object(optimizer, "run_command", side_effect=external), \
                    patch.object(sys, "argv", arguments), contextlib.redirect_stdout(output):
                self.assertEqual(optimizer.main(), 1)
            (root / "main.stdout").write_text(output.getvalue())
            optimizer.write_json(root / "observations.json", {
                "fault": fault, "commands": commands, "compiled": compiled, "resolved_a": resolved_a,
            })
            results = optimizer.read_journal(root / "output/results.jsonl",
                                            {row["path"]: row["source_sha256"] for row in rows})
            a, b = results["A.lean"], results["B.lean"]
            self.assertEqual(a["status"], "verified", a.get("error"))
            self.assertEqual(b["status"], "blocked")
            self.assertEqual(len([command for command in commands if "build" in command["argv"]]), 1)
            self.assertEqual(len([command for command in commands if "shake" in command["argv"]]), 1)
            expected_compiles = [("B", "baseline")]
            if fault != "compile_baseline":
                expected_compiles.append(("B", "candidate"))
            expected_compiles.extend((("A", "baseline"), ("A", "candidate")))
            self.assertEqual([(module, arm) for module, arm, _ in compiled], expected_compiles)
            self.assertEqual(len(resolved_a), 2)
            self.assertTrue(all(record["B"] == str(canonical / "B.olean") for record in resolved_a))
            for arm in ("baseline", "candidate"):
                self.assertEqual(len(a[arm]["artifacts"]), 7)
                self.assertEqual({path.name for path in Path(a[arm]["artifact_root"]).iterdir()},
                                 {"A" + suffix for suffix in outputs.SUFFIXES})
                snapshot = optimizer.read_json(Path(a["attempt_directory"]) / ("owned-" +
                                               ("before" if arm == "baseline" else "after") + ".json"))
                self.assertEqual(snapshot["batch_modules"], ["A"])
                self.assertEqual(snapshot["loaded_modules"], ["A", "B"])
                self.assertEqual(len(snapshot["declarations"][0]), 10)
                self.assertEqual(snapshot["declarations"][0]["axioms"], [])
            if fault.startswith("compile_"):
                sibling_root = Path(next(path for module, arm, path in compiled
                                         if module == "B" and fault == "compile_" + arm))
                self.assertEqual((sibling_root / "B.olean").read_bytes(),
                                 b"Partial output from failed sibling compiler\n")
            elif fault == "owned":
                self.assertIn("changed owned declarations", b["error"])
            elif fault == "snapshot":
                self.assertIn("exit", b["error"])
            self.assertEqual({path: path.read_bytes() for path in canonical.iterdir()}, canonical_bytes)
            for module, source in sources.items():
                self.assertEqual((root / (module + ".lean")).read_bytes(), source)

    def test_failed_sibling_outputs_do_not_enter_dependent_snapshot(self) -> None:
        for arm in ("baseline", "candidate"):
            with self.subTest(arm=arm):
                self.run_dependent_batch("compile_" + arm)

    def test_unaccepted_sibling_axioms_do_not_enter_dependent_snapshot(self) -> None:
        self.run_dependent_batch("owned")

    def test_sibling_snapshot_failure_does_not_block_dependent_candidate(self) -> None:
        self.run_dependent_batch("snapshot")


if __name__ == "__main__":
    unittest.main()
