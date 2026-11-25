#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Private-only import dependencies must use pinned artifacts in both snapshot modes."""

from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery


def parts(root: Path, module: str) -> list[list[str]]:
    stem = root / Path(*module.split("."))
    result = [[str(stem) + suffix for suffix in
               (".olean", ".olean.server", ".olean.private")],
              [str(stem) + suffix for suffix in (".ir.sig", ".ir")]]
    for group in result:
        for name in group:
            path = Path(name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((module + path.suffix + " explicitly mocked artifacts\n").encode())
    return result


class PrivateDependencyTests(unittest.TestCase):
    def capture(self, root: Path, batch: bool, defect: str | None = None,
                private_only_namespace: bool = False,
                top_level_external: bool = False
                ) -> tuple[optimizer.Tools, dict[str, object], dict[str, object], list[str]]:
        recovery.main_inputs(root, ("A",))
        selected = (root / "external/lib/lean" if top_level_external else root / "selected")
        shadow = root / "ambient-shadow"
        public_module = ("Foo" if top_level_external else
                         "Bar.Public" if private_only_namespace else "Foo.Public")
        private_module = ("Bar.Private" if top_level_external else
                          "MathlibExt.Private" if private_only_namespace else "Foo.Private")
        private_root = root / ".lake/build/lib/lean" if private_only_namespace else selected
        public = parts(selected, public_module)
        private = parts(private_root, private_module)
        shadow_parts = parts(shadow, private_module)
        Path(shadow_parts[0][2]).write_bytes(b"Different ambient private proof bytes\n")
        setup = root / ".lake/build/ir/A.setup.json"
        optimizer.write_json(setup, {"name": "A", "isModule": True,
                                    "importArts": {public_module: public}})
        expected_roots = ((str(private_root.resolve()), str(selected))
                          if private_only_namespace else (str(selected),))
        lean_path = (str(selected) + os.pathsep + str(shadow)
                     if top_level_external else str(shadow))
        tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                Path(optimizer.__file__).parent / "import_optimizer",
                                {"LEAN_PATH": lean_path}, 5, time_binary=root / "bin/time")
        arm = tools.output / "arm"
        calls: list[str] = []

        def external(argv: list[str], label: Path,
                     environment: dict[str, str] | None = None) -> dict[str, object]:
            if argv[0] == str(tools.time_binary):
                calls.append("compile")
                compile_path = optimizer.Tools.run.__wrapped__ if hasattr(
                    optimizer.Tools.run, "__wrapped__") else None
                self.assertIsNotNone(environment)
                self.assertNotIn(str(shadow), environment["LEAN_PATH"].split(":"))
                self.assertIn(str(selected), environment["LEAN_PATH"].split(":"))
                if defect == "during_compile_transient_private_only":
                    path = Path(private[0][2])
                    before, raw = path.stat(), path.read_bytes()
                    path.write_bytes(raw + b"Transient private proof during compilation\n")
                    path.write_bytes(raw)
                    os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                if defect == "pre_arm_pins":
                    pins = [pin for _, files in tools.input_manifests.values() for pin in files]
                    for group in private:
                        for name in group:
                            self.assertIn(optimizer.file_pin(Path(name)), pins)
                outputs.physical_parts(arm / "artifacts", Path("A.lean"))
                Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
                return recovery.mock_compile_command(tools, argv, label)
            label.parent.mkdir(parents=True, exist_ok=True)
            stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
            stderr.write_text("")
            code = 0
            self.assertIsNotNone(environment)
            if "--deps" in argv:
                calls.append("deps")
                stdout.write_text(str(arm / "artifacts/A.olean") + "\n")
            else:
                self.assertEqual(environment["LEAN_PATH"], "")
                helper = Path(argv[argv.index("--run") + 1]).name
                value = optimizer.read_json(Path(argv[argv.index("--run") + 2]))
                if helper == "private_imports.lean":
                    calls.append("private_closure")
                    roots = optimizer.read_json(Path(argv[argv.index("--run") + 3]))
                    namespace = "Bar" if (private_only_namespace or top_level_external) else "Foo"
                    candidates = roots.get(namespace)
                    self.assertIsNotNone(candidates)
                    # Bar only exists (as a public selection) under selected;
                    # MathlibExt only under the canonical project root.
                    self.assertEqual(candidates[0], str(selected))
                    if private_only_namespace:
                        self.assertIn(str(selected), candidates)
                        self.assertEqual(roots.get("MathlibExt"),
                            [str(private_root.resolve())])
                    self.assertNotIn(str(shadow), candidates or [])
                    rows = [{"module": module, "artifacts": artifacts}
                            for module, artifacts in value["importArts"].items()]
                    rows.append({"module": private_module, "artifacts":
                                 shadow_parts if defect == "ambient_shadow" else private})
                    stdout.write_text(json.dumps(rows) + "\n")
                    if calls.count("private_closure") == 2 and defect == "verification_change":
                        path = Path(private[0][2])
                        before, raw = path.stat(), path.read_bytes()
                        path.write_bytes(raw + b"Transient private proof\n")
                        path.write_bytes(raw)
                        os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                elif private_module not in value["importArts"]:
                    calls.append("unpinned_snapshot")
                    stdout.write_text("")
                    stderr.write_text(json.dumps({"kind": "missing_private_import_artifacts",
                                                 "module": private_module}) + "\n")
                    code = 3
                    if defect in ("before_discovery_change", "before_discovery_transient",
                                  "before_discovery_transient_private_only"):
                        path = Path(private[0][2])
                        before, raw = path.stat(), path.read_bytes()
                        path.write_bytes(raw + b"Different private proof, same mocked import graph\n")
                        if defect != "before_discovery_change":
                            path.write_bytes(raw)
                            os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                else:
                    calls.append("snapshot")
                    self.assertEqual(value["importArts"][private_module], private)
                    target = Path(value["importArts"]["A"][0][0])
                    snapshot = recovery.SavedSnapshotRecoveryTests.snapshot("A", target)
                    snapshot["declarations"][0]["value"] = optimizer.sha256(Path(private[0][2]))
                    snapshot.update(loaded_modules=list(value["importArts"]),
                                    loaded_module_count=len(value["importArts"]))
                    if batch:
                        snapshot.update(batch_modules=["A"], batch_module_count=1,
                                        loaded_modules_scope="whole_batch")
                    stdout.write_text(json.dumps(snapshot) + "\n")
            command = {"argv": argv, "cwd": str(root), "exit_code": code, "timed_out": False,
                       "remaining_group_killed": False, "elapsed_seconds": 0,
                       "stdout": str(stdout), "stderr": str(stderr)}
            optimizer.write_json(Path(str(label) + ".json"), command)
            return command

        with patch.object(optimizer.Tools, "run", side_effect=external):
            compilation = optimizer.compile_arm(tools, Path("A.lean"), setup, arm)
            if batch:
                snapshot = optimizer.snapshot_batch(tools, [{"path": "A.lean", "module": "A"}],
                    arm / "artifacts", arm, {"A.lean": compilation})["A"]
            else:
                snapshot = optimizer.snapshot_arm(tools, "A", Path("A.lean"), arm, compilation)
        return tools, snapshot, compilation, calls

    def test_snapshot_collector_rechecks_callers_original_setup_receipt(self) -> None:
        for batch, after_collection in ((False, False), (True, False), (False, True), (True, True)):
            with self.subTest(batch=batch, after_collection=after_collection), \
                    tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                original_collect = optimizer.snapshot_dependency_identities
                original_read = optimizer.read_json
                injected = root / "injected-context.json"
                changed = False
                parsed_injected = []

                def collect(setup, *arguments, **keywords):
                    nonlocal changed
                    collected = original_collect(setup, *arguments, **keywords) if after_collection else None
                    value = original_read(setup)
                    context = next(iter(value["snapshot_compilations"].values()))
                    metadata = original_read(Path(context["setup"]["path"]))
                    optimizer.write_json(injected, {**metadata, "injected_after_pin": True})
                    context["setup"] = optimizer.file_pin(injected)
                    optimizer.write_json(setup, value)
                    changed = True
                    return collected if after_collection else original_collect(setup, *arguments, **keywords)

                def read(path):
                    if path == injected:
                        parsed_injected.append(path)
                    return original_read(path)

                with patch.object(optimizer, "snapshot_dependency_identities", new=collect), \
                        patch.object(optimizer, "read_json", new=read):
                    with self.assertRaises(ValueError):
                        self.capture(root, batch)
                self.assertTrue(changed, "The change after the caller's receipt was not exercised")
                self.assertEqual(parsed_injected, [], "The collector followed a changed setup")

    def test_private_snapshot_guards_original_root_read_before_discovery(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            injected_parts = parts(root / "unlisted-original-root", "Injected.Extra")
            original_complete = optimizer.complete_private_snapshot_setup
            original_read = optimizer.read_json
            active_setup = None
            changed = False
            original_bytes = None

            def complete(tools, artifact_root, setup_pin, evidence):
                nonlocal active_setup
                active_setup = Path(setup_pin["path"])
                try:
                    return original_complete(tools, artifact_root, setup_pin, evidence)
                finally:
                    active_setup = None

            def read(path):
                nonlocal changed, original_bytes
                if path != active_setup or changed:
                    return original_read(path)
                value = original_read(path)
                original_bytes = path.read_bytes()
                value["importArts"]["Injected.Extra"] = injected_parts
                optimizer.write_json(path, value)
                changed = True
                try:
                    return original_read(path)
                finally:
                    path.write_bytes(original_bytes)

            with patch.object(optimizer, "complete_private_snapshot_setup", new=complete), \
                    patch.object(optimizer, "read_json", new=read):
                with self.assertRaises(ValueError):
                    self.capture(root, False)
            self.assertTrue(changed, "The original root read was not exercised")
            setup_pins = list((root / "output/inputs").glob("snapshot-setup-*.json"))
            self.assertTrue(any(path.read_bytes() == original_bytes for path in setup_pins))
            self.assertFalse((root / "output/arm/snapshot-evidence/private-imports/discovery.json").exists(),
                             "Private discovery ran with roots derived from transient original setup")

    def test_nonlinux_private_snapshot_writes_receipts_after_metadata_custody(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with recovery.isolated_ancestor_metadata(root), \
                        patch.object(optimizer.sys, "platform", "darwin"):
                    tools, snapshot, compilation, calls = self.capture(root, batch)
                self.assertEqual(calls, ["compile", "deps", "unpinned_snapshot",
                                         "private_closure", "private_closure", "snapshot"])
                self.assertTrue(list((tools.output / "inputs").glob("private-roots-*.json")))
                self.assertIn("snapshot_setup", compilation)
                self.assertEqual(snapshot["declaration_count"], 1)

    def test_private_dependency_is_pinned_in_single_and_batch_snapshots(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, snapshot, compilation, calls = self.capture(root, batch)
                self.assertEqual(calls, ["compile", "deps", "unpinned_snapshot",
                                         "private_closure", "private_closure", "snapshot"])
                setup = Path(compilation["snapshot_setup"]["path"])
                value = optimizer.read_json(setup)
                self.assertEqual(snapshot["declaration_count"], 1)
                self.assertEqual(snapshot["declarations"][0]["value"],
                                 optimizer.sha256(root / "selected/Foo/Private.olean.private"))
                receipt = value["snapshot_private_dependencies"]
                pins = optimizer.read_json(Path(receipt["input_manifest"]["path"]))["files"]
                for suffix in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"):
                    self.assertIn(str(root / "selected/Foo/Private") + suffix,
                                  [pin["path"] for pin in pins])
                optimizer.verify_snapshot_dependencies(tools, Path(compilation["artifact_root"]),
                    setup, optimizer.snapshot_dependency_identities(setup, setup_pin=optimizer.file_pin(setup)))

    def test_top_level_public_module_keeps_explicit_external_root(self) -> None:
        # A legitimate top-level module at an explicitly captured
        # LEAN_PATH root establishes that root for compilation,
        # fallback pinning, and discovery even though its relative
        # artifact path has only one component.
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, snapshot, compilation, calls = self.capture(
                    root, batch, top_level_external=True)
                self.assertEqual(calls, ["compile", "deps", "unpinned_snapshot",
                                         "private_closure", "private_closure", "snapshot"])
                self.assertEqual(snapshot["declarations"][0]["value"],
                                 optimizer.sha256(
                                     root / "external/lib/lean/Bar/Private.olean.private"))
                setup = Path(compilation["snapshot_setup"]["path"])
                value = optimizer.read_json(setup)
                receipt = value["snapshot_private_dependencies"]
                pins = optimizer.read_json(Path(receipt["input_manifest"]["path"]))["files"]
                for suffix in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"):
                    self.assertIn(str(root / "external/lib/lean/Bar/Private") + suffix,
                                  [pin["path"] for pin in pins])
                optimizer.verify_snapshot_dependencies(
                    tools, Path(compilation["artifact_root"]), setup,
                    optimizer.snapshot_dependency_identities(setup, setup_pin=optimizer.file_pin(setup)))

    def test_unlisted_top_level_root_is_not_a_discovery_or_pin_root(self) -> None:
        # A top-level public artifact under a directory that the
        # captured LEAN_PATH does not name cannot establish that
        # directory as a trusted root. Compilation searches only the
        # canonical project root here, so discovery and selected
        # namespace pinning must not let the duplicate private module
        # under the unlisted directory shadow the canonical copy.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            selected = root / "selected"
            canonical_private = parts(canonical, "Foo.Private")
            unlisted_private = parts(selected, "Foo.Private")
            public = parts(selected, "Foo")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                    root / "bin/lean", root, {}, 5)
            metadata = {"importArts": {"Foo": public}}
            self.assertEqual(
                optimizer.compilation_environment(tools, metadata)["LEAN_PATH"],
                str(canonical.resolve()))
            inputs = optimizer.compilation_input_paths(metadata, root, None, tools)
            fallback = optimizer.private_fallback_artifact_paths(tools, metadata)
            for group in unlisted_private:
                for name in group:
                    self.assertNotIn(name, inputs)
                    self.assertNotIn(name, fallback)
            for group in canonical_private:
                for name in group:
                    self.assertIn(name, fallback)
            value = {"importArts": {"Foo": public},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            self.assertEqual(roots["Foo"], [str(canonical.resolve())])
            value["importArts"]["A"] = parts(canonical, "A")
            rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                    {"module": "Foo.Private", "artifacts": canonical_private}]
            self.assertEqual(
                optimizer.private_import_map(value, rows, roots)["Foo.Private"],
                canonical_private)
            wrong_rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                          {"module": "Foo.Private", "artifacts": unlisted_private}]
            with self.assertRaisesRegex(ValueError, "selected artifact root"):
                optimizer.private_import_map(value, wrong_rows, roots)

    def test_nonlinux_private_completion_accepts_own_receipts(self) -> None:
        # On non-Linux platforms there is no inotify guard; directory
        # path-component identities must nevertheless not freeze
        # mutable evidence/output directories so tightly that the
        # later `snapshot-private` receipts reject their own writes.
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                with recovery.isolated_ancestor_metadata(root), \
                        patch.object(optimizer.sys, "platform", "darwin"):
                    _, snapshot, _, calls = self.capture(root, batch)
                self.assertEqual(snapshot["declaration_count"], 1)
                self.assertEqual(calls, ["compile", "deps", "unpinned_snapshot",
                                         "private_closure", "private_closure", "snapshot"])

    def test_private_dependency_cannot_use_an_ambient_shadow(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                with self.assertRaisesRegex(ValueError, "selected artifact root"):
                    self.capture(Path(directory).resolve(), batch, "ambient_shadow")

    def test_private_dependencies_are_pinned_before_compilation(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                self.capture(Path(directory).resolve(), batch, "pre_arm_pins")

    def test_private_only_change_before_discovery_is_rejected(self) -> None:
        for batch in (False, True):
            for defect in ("before_discovery_change", "before_discovery_transient"):
                with self.subTest(batch=batch, defect=defect), tempfile.TemporaryDirectory() as directory:
                    with self.assertRaisesRegex(ValueError, "identity changed|input changed|changed during"):
                        self.capture(Path(directory).resolve(), batch, defect)

    def test_single_loaded_receipt_requires_the_requested_target(self) -> None:
        value = {"snapshot_private_dependencies": {},
                 "snapshot_compilations": {"A.lean": {"module": "A"}},
                 "importArts": {"A": [], "Foo.Private": []}}
        for loaded in ([], ["Foo.Private"]):
            with self.subTest(loaded=loaded):
                with self.assertRaisesRegex(ValueError, "requested module"):
                    optimizer.verify_private_loaded_modules(
                        {"loaded_modules": loaded, "loaded_module_count": len(loaded)}, value)
        optimizer.verify_private_loaded_modules(
            {"loaded_modules": ["A"], "loaded_module_count": 1}, value)

    def test_private_proof_change_during_verification_is_rejected(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                with self.assertRaisesRegex(ValueError, "identity changed|input changed|changed during"):
                    self.capture(Path(directory).resolve(), batch, "verification_change")

    def test_repinned_root_receipt_cannot_replace_the_original_package(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, _, compilation, _ = self.capture(root, True)
            setup = Path(compilation["snapshot_setup"]["path"])
            value = optimizer.read_json(setup)
            receipt = value["snapshot_private_dependencies"]
            roots = Path(receipt["roots"]["path"])
            optimizer.write_json(roots, {"Foo": [str(root / "ambient-shadow")]})
            receipt["roots"] = optimizer.file_pin(roots)
            optimizer.write_json(setup, value)
            with self.assertRaisesRegex(ValueError, "selected artifact roots"):
                optimizer.verify_snapshot_dependencies(tools, Path(compilation["artifact_root"]),
                    setup, optimizer.snapshot_dependency_identities(setup, setup_pin=optimizer.file_pin(setup)))

    def test_selected_roots_preserve_ordered_search_path(self) -> None:
        # Two public modules in one namespace may be selected from
        # different search-path roots. Both roots stay as ordered
        # candidates, and a missing private module resolves to the
        # first candidate that actually carries its .olean.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(root / "one") + ":" + str(root / "two")}, 5)
            first_private = parts(root / "one", "Foo.Private")
            parts(root / "two", "Foo.Private")
            value = {"importArts": {"Foo.One": parts(root / "one", "Foo.One"),
                                     "Foo.Two": parts(root / "two", "Foo.Two")},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            prio = [c for c in roots["Foo"] if c in (str(root / "one"), str(root / "two"))]
            self.assertEqual(prio, [str(root / "one"), str(root / "two")])
            value["importArts"]["A"] = parts(root / "one", "A")
            rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                    {"module": "Foo.Private", "artifacts": first_private}]
            self.assertEqual(optimizer.private_import_map(value, rows, roots)["Foo.Private"],
                             first_private)

    def test_private_map_rejects_shadowed_later_root(self) -> None:
        # If the first candidate root carries the module, a closure row
        # naming the same module under a later root must be rejected:
        # that is not the copy compilation resolved.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(root / "one") + ":" + str(root / "two")}, 5)
            parts(root / "one", "Foo.Private")
            later = parts(root / "two", "Foo.Private")
            value = {"importArts": {"Foo.One": parts(root / "one", "Foo.One"),
                                     "Foo.Two": parts(root / "two", "Foo.Two")},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            value["importArts"]["A"] = parts(root / "one", "A")
            rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                    {"module": "Foo.Private", "artifacts": later}]
            with self.assertRaisesRegex(ValueError, "selected artifact root"):
                optimizer.private_import_map(value, rows, roots)

    def test_requested_arm_roots_are_excluded_from_package_selection(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            library = root / "lib/lean"
            library.mkdir(parents=True)
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {}, 5)
            value = {"importArts": {"Foo.One": parts(root / "first-arm", "Foo.One"),
                                     "Foo.Two": parts(root / "second-arm", "Foo.Two"),
                                     "Bar.Public": parts(root / "canonical", "Bar.Public")},
                     "snapshot_compilations": {"Foo/One.lean": {"module": "Foo.One"},
                                                "Foo/Two.lean": {"module": "Foo.Two"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            self.assertEqual(roots["Bar"], [str(root / "canonical")])
            self.assertNotIn("Foo", roots)

    def test_private_only_namespace_end_to_end(self) -> None:
        # The private dependency's namespace (MathlibExt) is absent from
        # the initial public importArts; it resolves only through the
        # canonical project artifact root, and its artifacts must already
        # be pinned in the compilation manifest.
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, snapshot, compilation, calls = self.capture(
                    root, batch, private_only_namespace=True)
                self.assertEqual(calls, ["compile", "deps", "unpinned_snapshot",
                                         "private_closure", "private_closure", "snapshot"])
                canonical = root / ".lake/build/lib/lean/MathlibExt/Private"
                self.assertEqual(snapshot["declarations"][0]["value"],
                                 optimizer.sha256(Path(str(canonical) + ".olean.private")))
                setup = Path(compilation["snapshot_setup"]["path"])
                receipt = optimizer.read_json(setup)["snapshot_private_dependencies"]
                pins = optimizer.read_json(Path(receipt["input_manifest"]["path"]))["files"]
                for suffix in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"):
                    self.assertIn(str(canonical) + suffix, [pin["path"] for pin in pins])
                optimizer.verify_snapshot_dependencies(tools, Path(compilation["artifact_root"]),
                    setup, optimizer.snapshot_dependency_identities(setup, setup_pin=optimizer.file_pin(setup)))

    def test_escaped_top_level_olean_namespace_is_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {}, 5)
            stem = root / "selected" / "A.olean" / "B"
            stem.parent.mkdir(parents=True)
            artifact = str(stem) + ".olean"
            Path(artifact).write_bytes(b"escaped namespace artifact\n")
            value = {"importArts": {"«A.olean».B": [[artifact], []]},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            self.assertEqual(roots["A.olean"], [str(root / "selected")])

    def test_private_only_transient_change_before_discovery_is_rejected(self) -> None:
        # A rewrite+restore of the private-only artifact after compilation
        # but before private-closure discovery must also be rejected.
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                with self.assertRaisesRegex(ValueError, "identity changed|input changed|changed during"):
                    self.capture(Path(directory).resolve(), batch,
                                 "before_discovery_transient_private_only",
                                 private_only_namespace=True)

    def test_private_only_transient_change_during_compilation_is_rejected(self) -> None:
        # A rewrite+restore of the private-only artifact (bytes and mtime
        # restored, ctime changed) while the forced compile runs must be
        # rejected: fallback artifacts are identity-guarded around the
        # compile even though they are not per-target resume inputs.
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                with self.assertRaisesRegex(ValueError, "identity changed|input changed|changed during"):
                    self.capture(Path(directory).resolve(), batch,
                                 "during_compile_transient_private_only",
                                 private_only_namespace=True)

    def test_private_resolution_uses_first_root_containing_module(self) -> None:
        # Review scenario: the compiler search path is R1:R2, Foo.Public
        # is explicitly selected only from R2, and Foo.Private exists in
        # both roots. Compilation resolved R1's copy, so discovery must
        # too; the explicit public selection must not promote R2.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            private = parts(canonical, "Foo.Private")
            shadow_private = parts(root / "later", "Foo.Private")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(canonical) + ":" + str(root / "later")}, 5)
            value = {"importArts": {"Foo.Public": parts(root / "later", "Foo.Public")},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            prio = [c for c in roots["Foo"]
                    if c in (str(canonical.resolve()), str(root / "later"))]
            self.assertEqual(prio, [str(canonical.resolve()), str(root / "later")])
            value["importArts"]["A"] = parts(canonical, "A")
            rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                    {"module": "Foo.Private", "artifacts": private}]
            self.assertEqual(optimizer.private_import_map(value, rows, roots)["Foo.Private"],
                             private)
            shadow_rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                           {"module": "Foo.Private", "artifacts": shadow_private}]
            with self.assertRaisesRegex(ValueError, "selected artifact root"):
                optimizer.private_import_map(value, shadow_rows, roots)

    def test_unselected_stale_package_root_is_not_a_candidate(self) -> None:
        # A package checkout under .lake/packages that the captured
        # LEAN_PATH does not select must never contribute private-module
        # resolution or fallback pins: the compiler would not search it.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            stale = root / ".lake/packages/stale/.lake/build/lib/lean"
            parts(stale, "Foo.Private")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(canonical)}, 5)
            # The stale root is absent from the fallback inventory...
            fallback = optimizer.canonical_namespace_artifact_paths(root, None, tools)
            self.assertFalse(any(str(stale.resolve()) in path for path in fallback))
            self.assertNotIn(stale.resolve(), optimizer.canonical_artifact_roots(tools))
            # ...and absent from private resolution candidates.
            value = {"importArts": {"Foo.Public": parts(canonical, "Foo.Public")},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            for candidates in roots.values():
                self.assertNotIn(str(stale.resolve()), candidates)

    def test_stale_default_package_root_in_lean_path_needs_manifest(self) -> None:
        # Path shape alone must not authorize a package root: a stale
        # `.lake/packages/<name>/...` entry explicitly present in the
        # captured LEAN_PATH is trusted only when the pinned manifest
        # names that package. Only the project build root is accepted
        # solely by its shape.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            stale = root / ".lake/packages/stale/.lake/build/lib/lean"
            parts(stale, "Foo.Private")
            public = parts(canonical, "Bar.Public")
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages", "packages": []})
            lean_path = os.pathsep.join((str(canonical), str(stale)))
            tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                    root / "bin/lean", root, {"LEAN_PATH": lean_path}, 5)
            self.assertEqual(optimizer.canonical_artifact_roots(tools),
                             [canonical.resolve()])
            metadata = {"importArts": {"Bar.Public": public}}
            self.assertNotIn(str(stale),
                             optimizer.compilation_environment(tools, metadata)["LEAN_PATH"].split(os.pathsep))
            inventory = optimizer.private_fallback_artifact_paths(tools, metadata)
            self.assertFalse(any(str(stale.resolve()) in name for name in inventory))
            roots = optimizer.private_dependency_roots(tools, {
                "importArts": {"Bar.Public": public},
                "snapshot_compilations": {"A.lean": {"module": "A"}}})
            for candidates in roots.values():
                self.assertNotIn(str(stale), candidates)
            # The same root becomes trusted once the pinned manifest
            # actually names the package (default git layout).
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "git", "name": "stale", "scope": "",
                              "inherited": False,
                              "url": "https://example.invalid/stale.git",
                              "rev": "0" * 40, "inputRev": "main",
                              "manifestFile": "lake-manifest.json",
                              "configFile": "lakefile.toml"}]})
            selected_tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                             root / "bin/lean", root,
                                             {"LEAN_PATH": lean_path}, 5)
            self.assertIn(stale.resolve(), optimizer.canonical_artifact_roots(selected_tools))

    def test_manifest_authorizes_private_only_external_package_roots(self) -> None:
        # Lake-selected packages need not live under the project's
        # default `.lake/packages` directory: a path dependency can be
        # outside the project, and git dependencies can use a custom
        # `packagesDir` (and a package subdirectory). When such a
        # package is reached only through a private import, no public
        # `importArts` root selects it, so canonical-root derivation
        # must authorize it from the pinned Lake manifest instead of
        # its lexical location relative to the project.
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            root = base / "project"
            (root / "bin").mkdir(parents=True)
            canonical = root / ".lake/build/lib/lean"
            path_package = base / "vendor/ext-pkg"
            path_root = path_package / ".lake/build/lib/lean"
            git_package = root / "custom-packages/git-pkg/subpkg"
            git_root = git_package / ".lake/build/lib/lean"
            path_private = parts(path_root, "Foo.Private")
            git_private = parts(git_root, "Baz.Private")
            public = parts(canonical, "Bar.Public")
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0",
                "packagesDir": "custom-packages",
                "packages": [
                    {"type": "path", "name": "extPkg", "scope": "",
                     "inherited": False, "dir": "../vendor/ext-pkg",
                     "manifestFile": "lake-manifest.json",
                     "configFile": "lakefile.toml"},
                    {"type": "git", "name": "«git-pkg»", "scope": "",
                     "inherited": False, "url": "https://example.invalid/git-pkg.git",
                     "rev": "0" * 40, "inputRev": "main", "subDir": "subpkg",
                     "manifestFile": "lake-manifest.json",
                     "configFile": "lakefile.toml"},
                ],
            })
            lean_path = os.pathsep.join((str(canonical), str(path_root), str(git_root)))
            tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                    root / "bin/lean", root, {"LEAN_PATH": lean_path}, 5)
            self.assertIn(path_root.resolve(), optimizer.canonical_artifact_roots(tools))
            self.assertIn(git_root.resolve(), optimizer.canonical_artifact_roots(tools))
            metadata = {"importArts": {"Bar.Public": public}}
            self.assertEqual(
                optimizer.compilation_environment(tools, metadata)["LEAN_PATH"].split(os.pathsep),
                [str(canonical.resolve()), str(path_root), str(git_root)])
            inventory = optimizer.private_fallback_artifact_paths(tools, metadata)
            for private in (path_private, git_private):
                for group in private:
                    for name in group:
                        self.assertIn(name, inventory)
            self.assertIn(str(root / "lake-manifest.json"), inventory)
            self.assertIn(str(root / "lake-manifest.json"),
                          optimizer.compilation_input_paths(metadata, root, None, tools))
            value = {"importArts": {"Bar.Public": public},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            self.assertEqual(roots["Foo"], [str(path_root)])
            self.assertEqual(roots["Baz"], [str(git_root)])
            value["importArts"]["A"] = parts(canonical, "A")
            rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                    {"module": "Foo.Private", "artifacts": path_private},
                    {"module": "Baz.Private", "artifacts": git_private}]
            mapped = optimizer.private_import_map(value, rows, roots)
            self.assertEqual(mapped["Foo.Private"], path_private)
            self.assertEqual(mapped["Baz.Private"], git_private)

    def test_manifest_rewrite_cannot_authorize_an_ambient_root(self) -> None:
        # Manifest-derived canonical roots must come from the manifest
        # bytes pinned when Tools was constructed (i.e. when Lake's
        # environment was captured). Rewriting lake-manifest.json
        # afterwards must fail closed rather than reclassifying an
        # ambient LEAN_PATH entry as a trusted package root.
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            root = base / "project"
            (root / "bin").mkdir(parents=True)
            canonical = root / ".lake/build/lib/lean"
            ambient = base / "ambient/.lake/build/lib/lean"
            parts(ambient, "Foo.Private")
            public = parts(canonical, "Bar.Public")
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages", "packages": []})
            lean_path = os.pathsep.join((str(canonical), str(ambient)))
            tools = optimizer.Tools(root, root / "output", root / "bin/lake",
                                    root / "bin/lean", root, {"LEAN_PATH": lean_path}, 5)
            self.assertNotIn(ambient.resolve(), optimizer.canonical_artifact_roots(tools))
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "path", "name": "ambientPkg", "scope": "",
                              "inherited": False, "dir": "../ambient",
                              "manifestFile": "lake-manifest.json",
                              "configFile": "lakefile.toml"}]})
            metadata = {"importArts": {"Bar.Public": public}}
            self.assertNotIn(ambient.resolve(), optimizer.canonical_artifact_roots(tools))
            self.assertNotIn(str(ambient),
                             optimizer.compilation_environment(tools, metadata)["LEAN_PATH"].split(os.pathsep))
            inventory = optimizer.private_fallback_artifact_paths(tools, metadata)
            self.assertFalse(any(str(ambient.resolve()) in name for name in inventory))
            roots = optimizer.private_dependency_roots(tools, {
                "importArts": {"Bar.Public": public},
                "snapshot_compilations": {"A.lean": {"module": "A"}}})
            for candidates in roots.values():
                self.assertNotIn(str(ambient), candidates)
            # Path composition binds the pinned manifest itself as a
            # guarded trust input (still with no ambient artifacts),
            # and issuing a receipt after the rewrite is refused
            # instead of hashing the rewritten manifest as though it
            # had authorized the pinned roots.
            inputs = optimizer.compilation_input_paths(metadata, root, None, tools)
            self.assertIn(str(root / "lake-manifest.json"), inputs)
            self.assertIn(str(root / "lake-manifest.json"), inventory)
            self.assertFalse(any(str(ambient.resolve()) in name for name in inputs))
            with self.assertRaisesRegex(
                    ValueError, "Lake manifest changed after environment capture"):
                optimizer.pin_private_fallback_inputs(tools, metadata)

    def test_manifest_pinned_before_lake_env_cannot_be_replaced_afterwards(self) -> None:
        # Production captures LEAN_PATH by running `lake env` before
        # Tools exists. The manifest bytes must therefore be pinned
        # before that command and passed into Tools verbatim: a
        # rewrite in the capture window is rejected by the
        # pre-Tools verification, and even a Tools value built from
        # the pre-capture bytes never authorizes the rewritten
        # manifest's ambient package.
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            root = base / "project"
            (root / "bin").mkdir(parents=True)
            canonical = root / ".lake/build/lib/lean"
            ambient = base / "ambient/.lake/build/lib/lean"
            parts(ambient, "Foo.Private")
            parts(canonical, "Bar.Public")
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages", "packages": []})
            pinned = optimizer.capture_lake_manifest_bytes(root)
            self.assertIsNotNone(pinned)
            optimizer.verify_lake_manifest_bytes(root, pinned)
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "path", "name": "ambientPkg", "scope": "",
                              "inherited": False, "dir": "../ambient",
                              "manifestFile": "lake-manifest.json",
                              "configFile": "lakefile.toml"}]})
            with self.assertRaisesRegex(
                    ValueError, "Lake manifest changed after environment capture"):
                optimizer.verify_lake_manifest_bytes(root, pinned)
            lean_path = os.pathsep.join((str(canonical), str(ambient)))
            tools = optimizer.Tools(
                root, root / "output", root / "bin/lake", root / "bin/lean", root,
                {"LEAN_PATH": lean_path}, 5,
                lake_manifest_bytes={root / "lake-manifest.json": pinned})
            self.assertNotIn(ambient.resolve(), optimizer.canonical_artifact_roots(tools))

    def test_captured_environment_is_validated_against_pinned_graph(self) -> None:
        # A rename/restore during `lake env` can leave the manifest
        # bytes (and inode) restored while the captured LEAN_PATH came
        # from alternate bytes. Before/after byte checks cannot see
        # that, so production independently validates the captured
        # environment against the pinned graph: every package root in
        # LEAN_PATH must be authorized by the pinned manifest (the
        # project root excepted), and every manifest-authorized
        # existing package root must appear in LEAN_PATH.
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory).resolve()
            root = base / "project"
            (root / "bin").mkdir(parents=True)
            canonical = root / ".lake/build/lib/lean"
            ambient_package = base / "ambient"
            ambient = ambient_package / ".lake/build/lib/lean"
            parts(ambient, "Foo.Private")
            parts(canonical, "Bar.Public")
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages", "packages": []})
            pinned = optimizer.capture_lake_manifest_bytes(root)
            lean_path = os.pathsep.join((str(canonical), str(ambient)))
            tools = optimizer.Tools(
                root, root / "output", root / "bin/lake", root / "bin/lean", root,
                {"LEAN_PATH": lean_path}, 5,
                lake_manifest_bytes={root / "lake-manifest.json": pinned})
            with self.assertRaisesRegex(
                    ValueError, "outside the pinned Lake package graph"):
                optimizer.validate_captured_environment(tools)
            honest = optimizer.Tools(
                root, root / "output", root / "bin/lake", root / "bin/lean", root,
                {"LEAN_PATH": str(canonical)}, 5,
                lake_manifest_bytes={root / "lake-manifest.json": pinned})
            optimizer.validate_captured_environment(honest)
            # The converse also fails: a manifest-authorized existing
            # package root missing from the captured LEAN_PATH means
            # Lake did not read this graph.
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "path", "name": "ambientPkg", "scope": "",
                              "inherited": False, "dir": "../ambient",
                              "manifestFile": "lake-manifest.json",
                              "configFile": "lakefile.toml"}]})
            selected = optimizer.Tools(
                root, root / "output", root / "bin/lake", root / "bin/lean", root,
                {"LEAN_PATH": str(canonical)}, 5)
            with self.assertRaisesRegex(
                    ValueError, "missing from the captured LEAN_PATH"):
                optimizer.validate_captured_environment(selected)
            complete = optimizer.Tools(
                root, root / "output", root / "bin/lake", root / "bin/lean", root,
                {"LEAN_PATH": lean_path}, 5)
            optimizer.validate_captured_environment(complete)

    def test_compilation_environment_excludes_ambient_first_root(self) -> None:
        # With LEAN_PATH=ambient:selected and Foo.Private in both, the
        # forced compile must not resolve the ambient copy: its search
        # path drops every unpinned root, so compilation and discovery
        # agree on the trusted canonical/selected copy.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            ambient, selected = root / "ambient", root / "selected"
            parts(ambient, "Foo.Private")
            privately_selected = parts(selected, "Foo.Private")
            public = parts(selected, "Foo.Public")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(ambient) + ":" + str(selected)}, 5)
            metadata = {"importArts": {"Foo.Public": public}}
            environment = optimizer.compilation_environment(tools, metadata)
            entries = environment["LEAN_PATH"].split(":")
            self.assertNotIn(str(ambient), entries)
            self.assertIn(str(selected), entries)
            value = {"importArts": {"Foo.Public": public},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            value["importArts"]["A"] = parts(selected, "A")
            rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                    {"module": "Foo.Private", "artifacts": privately_selected}]
            self.assertEqual(optimizer.private_import_map(value, rows, roots)["Foo.Private"],
                             privately_selected)

    def test_selected_external_root_private_namespace_is_pinned(self) -> None:
        # A noncanonical Lake-selected root is searched wholesale by the
        # forced compile, so its private-only namespaces (absent from
        # importArts) must be pinned before compilation in the fallback
        # receipt, and discovery must resolve them from that root.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            external = root / "external"
            private = parts(external, "Foo.Private")
            public = parts(external, "Bar.Public")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(external)}, 5)
            metadata = {"importArts": {"Bar.Public": public}}
            inventory = optimizer.private_fallback_artifact_paths(tools, metadata)
            for group in private:
                for name in group:
                    self.assertIn(name, inventory)
            value = {"importArts": {"Bar.Public": public},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            value["importArts"]["A"] = parts(external, "A")
            rows = [{"module": "A", "artifacts": value["importArts"]["A"]},
                    {"module": "Foo.Private", "artifacts": private}]
            self.assertEqual(optimizer.private_import_map(value, rows, roots)["Foo.Private"],
                             private)

    def test_flat_selected_artifact_does_not_inventory_project_root(self) -> None:
        # A flat fixture artifact's containing directory is neither a
        # wholesale artifact root nor part of the forced compile's
        # LEAN_PATH: inventories must not recurse through the project
        # root (including the optimizer's mutable output tree), and
        # compilation must not search an uninventoried root.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            flat = root / "fixture-import-part"
            flat.write_bytes(b"explicitly mocked flat artifact\n")
            parts(root / "output", "Foo.Private")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {}, 5)
            metadata = {"importArts": {"Mathlib": [[str(flat)], []]}}
            self.assertEqual(optimizer.selected_artifact_roots(metadata, root, strict=True), [])
            self.assertEqual(optimizer.selected_root_artifact_paths(metadata, root, tools), ())
            self.assertFalse(any(str(root / "output") in path for path in
                                 optimizer.private_fallback_artifact_paths(tools, metadata)))
            self.assertEqual(optimizer.compilation_environment(
                tools, metadata)["LEAN_PATH"], "")

    def test_grouped_private_snapshot_rejects_divergent_context_roots(self) -> None:
        # Two arms compiled against different noncanonical roots must
        # not share one merged private closure: each arm's own closure
        # resolves the duplicated Foo.Private from its own root, so the
        # grouped completion fails and the batch caller retries
        # singletons instead of certifying B against A's dependency.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            recovery.main_inputs(root, ("A", "B"))
            first, second = root / "first", root / "second"
            parts(first, "Foo.Private")
            parts(second, "Foo.Private")
            for name, module, public in (
                    ("A", "Alpha.Public", parts(first, "Alpha.Public")),
                    ("B", "Beta.Public", parts(second, "Beta.Public"))):
                optimizer.write_json(root / ".lake/build/ir" / (name + ".setup.json"),
                                     {"name": name, "isModule": True,
                                      "importArts": {module: public}})
            tools = optimizer.Tools(
                root, root / "output", root / "bin/lake", root / "bin/lean",
                Path(optimizer.__file__).parent / "import_optimizer", {}, 5,
                time_binary=root / "bin/time")
            calls: list[str] = []

            def external(argv: list[str], label: Path,
                         environment: dict[str, str] | None = None) -> dict[str, object]:
                self.assertIsNotNone(environment)
                if argv[0] == str(tools.time_binary):
                    calls.append("compile")
                    source = Path(argv[argv.index("-R") + 2])
                    artifact_root = Path(argv[argv.index("-i") + 1]).parent
                    outputs.physical_parts(artifact_root, Path(source.name))
                    Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
                    return recovery.mock_compile_command(tools, argv, label)
                label.parent.mkdir(parents=True, exist_ok=True)
                stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
                stdout.write_text("")
                stderr.write_text("")
                code = 0
                if "--deps" in argv:
                    calls.append("deps")
                    module = Path(argv[-1]).read_text().removeprefix("import all ").strip()
                    stdout.write_text(str(Path(environment["LEAN_PATH"]) / (module + ".olean")) + "\n")
                else:
                    helper = Path(argv[argv.index("--run") + 1]).name
                    value = optimizer.read_json(Path(argv[argv.index("--run") + 2]))
                    if helper == "private_imports.lean":
                        calls.append("private_closure")
                        roots = optimizer.read_json(Path(argv[argv.index("--run") + 3]))
                        stem = next(Path(candidate) / "Foo/Private" for candidate in roots["Foo"]
                                    if Path(str(Path(candidate) / "Foo/Private") + ".olean").is_file())
                        private = [[str(stem) + suffix for suffix in
                                    (".olean", ".olean.server", ".olean.private")],
                                   [str(stem) + suffix for suffix in (".ir.sig", ".ir")]]
                        rows = [{"module": module, "artifacts": artifacts}
                                for module, artifacts in value["importArts"].items()]
                        rows.append({"module": "Foo.Private", "artifacts": private})
                        stdout.write_text(json.dumps(rows) + "\n")
                    elif "Foo.Private" not in value["importArts"]:
                        calls.append("unpinned_snapshot")
                        stderr.write_text(json.dumps(
                            {"kind": "missing_private_import_artifacts",
                             "module": "Foo.Private"}) + "\n")
                        code = 3
                    else:
                        raise AssertionError("grouped snapshot must fail before the final snapshot")
                command = {"argv": argv, "cwd": str(root), "exit_code": code, "timed_out": False,
                           "remaining_group_killed": False, "elapsed_seconds": 0,
                           "stdout": str(stdout), "stderr": str(stderr)}
                optimizer.write_json(Path(str(label) + ".json"), command)
                return command

            compilations: dict[str, dict[str, object]] = {}
            with patch.object(optimizer.Tools, "run", side_effect=external):
                for name in ("A", "B"):
                    compilations[name + ".lean"] = optimizer.compile_arm(
                        tools, Path(name + ".lean"), root / ".lake/build/ir" / (name + ".setup.json"),
                        tools.output / name)
                with self.assertRaisesRegex(
                        ValueError, "Grouped private snapshot contexts resolve different"):
                    optimizer.snapshot_batch(
                        tools, [{"path": "A.lean", "module": "A",
                                 "source_sha256": recovery.digest(recovery.ORIGINAL)},
                                {"path": "B.lean", "module": "B",
                                 "source_sha256": recovery.digest(recovery.ORIGINAL)}],
                        {name: Path(compilations[name]["artifact_root"]) for name in compilations},
                        tools.output / "group", compilations)
            self.assertEqual(calls.count("private_closure"), 3)

    def test_tools_accepts_saved_fixture_output_equal_to_project_root(self) -> None:
        # Tools construction intentionally allows output == project
        # root (canonical root nested *below* output) for
        # saved-fixture / verification callers that only use
        # explicit file pins. The guarded trust call sites
        # (compile/fallback/discovery) reject that overlap instead;
        # see test_trusted_root_nested_inside_output_is_rejected_before_trust.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve() / "project"
            (root / "bin").mkdir(parents=True)
            canonical = root / ".lake/build/lib/lean"
            canonical.mkdir(parents=True)
            tools = optimizer.Tools(root, root, root / "bin/lake",
                                    root / "bin/lean", root, {}, 5)
            self.assertEqual(tools.output, root)
            self.assertIn(canonical, optimizer.canonical_artifact_roots(tools))
            library = root / "toolchain/lib/lean"
            toolchain_artifact = library / "Init/Core.olean"
            toolchain_artifact.parent.mkdir(parents=True)
            toolchain_artifact.write_bytes(b"saved-fixture toolchain artifact\n")
            saved_tools = optimizer.Tools(
                root, root, root / "bin/lake", root / "bin/lean", root,
                {"LEAN_SYSROOT": str(root / "toolchain")}, 5)
            manifest = optimizer.pin_setup_inputs(saved_tools, {"importArts": {}})
            pins = optimizer.read_json(Path(manifest["path"]))["files"]
            self.assertIn(str(toolchain_artifact), [pin["path"] for pin in pins])
            with self.assertRaisesRegex(
                    ValueError, "Trusted artifact root must not be nested"):
                optimizer.private_fallback_artifact_paths(
                    saved_tools, {"importArts": {}})
            with self.assertRaisesRegex(
                    ValueError, "Trusted artifact root must not be nested"):
                optimizer.compilation_environment(saved_tools, {"importArts": {}})
            with self.assertRaisesRegex(
                    ValueError, "Trusted artifact root must not be nested"):
                optimizer.private_dependency_roots(saved_tools, {
                    "importArts": {},
                    "snapshot_compilations": {"A.lean": {"module": "A"}}})
            with self.assertRaisesRegex(
                    ValueError, "Trusted artifact root must not be nested"):
                optimizer.reject_output_nested_in_roots(
                    tools, optimizer.canonical_artifact_roots(tools))

    def test_grouped_failure_derivation_skips_private_control_exit(self) -> None:
        # Exit 3 with a validated-shaped missing-private receipt is a
        # control signal, not the grouped failure. Failure derivation
        # must ignore it and report the later completed
        # `snapshot-private` command when that attempt failed.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            evidence = root / "snapshot-evidence"
            evidence.mkdir(parents=True)

            def record(label: str, code: int, stderr_payload: str) -> dict[str, object]:
                stdout = evidence / (label + ".stdout")
                stderr = evidence / (label + ".stderr")
                stdout.write_text("")
                stderr.write_text(stderr_payload)
                command_path = evidence / (label + ".json")
                optimizer.write_json(command_path, {
                    "argv": [str(root / "bin/lean"), "-j2", "--run",
                             "declarations_batch.lean", "setup.json", "A", "B"],
                    "cwd": str(root), "exit_code": code, "timed_out": False,
                    "remaining_group_killed": False, "stdout": str(stdout),
                    "stderr": str(stderr)})
                return {"json": optimizer.file_pin(command_path),
                        "stdout": optimizer.file_pin(stdout),
                        "stderr": optimizer.file_pin(stderr),
                        "kind": "snapshot"}

            tools = optimizer.Tools(root, root, root / "bin/lake", root / "bin/lean",
                                    root, {}, 5)
            control = record(
                "snapshot", 3,
                json.dumps({"kind": "missing_private_import_artifacts",
                            "module": "Foo.Private"}) + "\n")
            self.assertIsNone(optimizer.derive_snapshot_failure_error(
                tools, {"baseline": {"snapshot": control}}))
            completed = record("snapshot-private", 7, "final failure\n")
            self.assertEqual(
                optimizer.derive_snapshot_failure_error(
                    tools, {"baseline": {"snapshot": completed}}),
                "Command exited 7; see " + str(evidence / "snapshot-private.stderr"))

    def test_compile_and_discovery_share_unlisted_root_ordering(self) -> None:
        # With no LEAN_PATH, trusted roots absent from the search path
        # must be ordered identically for the forced compile and for
        # private discovery: selected, canonical project fallback, then
        # the (lexically earlier) standard library. A sorted() tail in
        # either consumer would put the sysroot ahead of the project
        # root and resolve a private module present in both differently.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            library = root / "aaa-sysroot/lib/lean"
            parts(canonical, "Foo.Private")
            parts(library, "Foo.Private")
            selected = root / "selected"
            public = parts(selected, "Bar.Public")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_SYSROOT": str(root / "aaa-sysroot")}, 5)
            metadata = {"importArts": {"Bar.Public": public}}
            expected = [str(selected), str(canonical.resolve()), str(library.resolve())]
            self.assertEqual(
                optimizer.compilation_environment(tools, metadata)["LEAN_PATH"].split(os.pathsep),
                expected)
            value = {"importArts": {"Bar.Public": public},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            self.assertEqual(roots["Foo"],
                             [str(canonical.resolve()), str(library.resolve())])
            self.assertEqual(roots["Bar"], [str(selected)])

    def test_flat_artifact_parent_is_not_in_forced_compile_path_or_fallback(self) -> None:
        # Flat fixture artifacts live directly beneath the project
        # root, but that containing directory is not a strict module
        # root: exposing it to the forced compile would let the
        # compiler search a root private discovery deliberately does
        # not inventory.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            parts(canonical, "Foo.Private")
            public = parts(root, "Mathlib")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(canonical)}, 5)
            metadata = {"importArts": {"Mathlib": public}}
            self.assertEqual(
                optimizer.compilation_environment(tools, metadata)["LEAN_PATH"],
                str(canonical.resolve()))
            fallback = optimizer.private_fallback_artifact_paths(tools, metadata)
            self.assertFalse(any(Path(path).is_relative_to(root) and
                                 not Path(path).is_relative_to(canonical.resolve())
                                 for path in fallback))

    def test_output_nested_under_canonical_root_is_rejected(self) -> None:
        # Lean searches a canonical root wholesale, so placing the
        # mutable optimizer output beneath it is unsupported: stale
        # optimizer artifacts could otherwise be resolved even if
        # inventory scans excluded that subtree.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            parts(canonical, "Foo.Private")
            output = canonical / "Foo/optimizer-output"
            parts(output, "Foo.PriorOptimizerArtifact")
            with self.assertRaisesRegex(ValueError, "output.*trusted|trusted.*output"):
                optimizer.Tools(root, output, root / "bin/lake", root / "bin/lean",
                                root, {"LEAN_PATH": str(canonical)}, 5)

    def test_output_nested_under_selected_root_is_rejected_before_trust(self) -> None:
        # The compiler search path cannot exclude a subtree of a
        # trusted root, so an optimizer output directory nested there
        # is an unsupported placement. It must be rejected before
        # compilation inputs, fallback inventories, compilation
        # environments, or private discovery can trust stale artifacts
        # from that mutable tree.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            selected = root / "selected"
            parts(selected, "Foo.Private")
            public = parts(selected, "Foo.Public")
            output = selected / "Foo/optimizer-output"
            parts(output, "Foo.StaleOptimizerArtifact")
            tools = optimizer.Tools(root, output, root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(selected)}, 5)
            metadata = {"importArts": {"Foo.Public": public}}
            with self.assertRaisesRegex(ValueError, "output.*trusted|trusted.*output"):
                optimizer.compilation_input_paths(metadata, root, None, tools)
            with self.assertRaisesRegex(ValueError, "output.*trusted|trusted.*output"):
                optimizer.private_fallback_artifact_paths(tools, metadata)
            with self.assertRaisesRegex(ValueError, "output.*trusted|trusted.*output"):
                optimizer.compilation_environment(tools, metadata)
            value = {"importArts": {"Foo.Public": public},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            with self.assertRaisesRegex(ValueError, "output.*trusted|trusted.*output"):
                optimizer.private_dependency_roots(tools, value)

    def test_trusted_root_nested_inside_output_is_rejected_before_trust(self) -> None:
        # The inverse placement is also unsupported: compilation can
        # search a trusted root beneath the mutable output tree, but
        # inventory scans must exclude that tree, so consumed
        # artifacts would never have been pinned. Reject it
        # consistently before input/fallback/environment/discovery
        # composition rather than letting each scan silently omit it.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            parts(canonical, "Foo.Private")
            public = parts(canonical, "Foo.Public")
            output = root / "optimizer-output"
            selected = output / "external/lib/lean"
            parts(selected, "Bar.Private")
            selected_public = parts(selected, "Bar.Public")
            tools = optimizer.Tools(root, output, root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(selected)}, 5)
            metadata = {"importArts": {"Bar.Public": selected_public}}
            # compilation_input_paths is also a saved-fixture/explicit-
            # pinning surface, so it deliberately does not reject this
            # inverse direction; actual compilation trust is checked
            # by fallback/environment/discovery below.
            optimizer.compilation_input_paths(metadata, root, None, tools)
            checks = (
                lambda: optimizer.private_fallback_artifact_paths(tools, metadata),
                lambda: optimizer.compilation_environment(tools, metadata),
                lambda: optimizer.private_dependency_roots(tools, {
                    "importArts": {"Bar.Public": selected_public},
                    "snapshot_compilations": {"A.lean": {"module": "A"}}}),
            )
            for check in checks:
                with self.assertRaisesRegex(ValueError, "(?i)output.*trusted|trusted.*output"):
                    check()

    def test_saved_private_snapshot_ignores_unrelated_fallback_namespace(self) -> None:
        # Saved-row validation checks the recorded roots and discovered
        # closure pins only: adding an unrelated namespace under a
        # selected root after the snapshot must not invalidate the row,
        # while fresh exact validation still rejects it.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, _, compilation, _ = self.capture(root, False)
            setup_path = Path(compilation["snapshot_setup"]["path"])
            saved = optimizer.read_json(setup_path)
            record = saved["snapshot_private_dependencies"]
            original = optimizer.read_json(Path(record["original_setup"]["path"]))
            parts(root / "selected", "Zzz.Unrelated")
            arts = optimizer.verify_private_snapshot_dependencies(
                tools, original, record, exact=False)
            self.assertIn("Foo.Private", arts)
            rebuilt = optimizer.snapshot_setup_value(
                tools, Path(compilation["artifact_root"]),
                saved["snapshot_compilations"], saved["snapshot_kind"], record)
            self.assertEqual(rebuilt, saved)
            with self.assertRaises(ValueError):
                optimizer.verify_private_snapshot_dependencies(
                    tools, original, record, exact=True)

    def test_transient_fallback_addition_is_rejected_by_exact_inventory(self) -> None:
        # Exact-inventory recomputation proves membership: a shadow
        # created ahead of the pinned copy appears as a new entry.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            private = parts(canonical, "Foo.Private")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(canonical)}, 5)
            metadata = {"importArts": {"Foo.Public": parts(canonical, "Foo.Public")}}
            before = optimizer.private_fallback_artifact_paths(tools, metadata)
            optimizer.verify_private_fallback_inventory(tools, metadata, before)
            shadow = canonical / "Bar/Shadow.olean.private"
            shadow.parent.mkdir(parents=True, exist_ok=True)
            shadow.write_bytes(b"transient shadow\n")
            with self.assertRaises(ValueError):
                optimizer.verify_private_fallback_inventory(tools, metadata, before)
            shadow.unlink()
            optimizer.verify_private_fallback_inventory(tools, metadata, before)

    def test_empty_namespace_inventory_transient_shadow_is_rejected(self) -> None:
        # An existing empty namespace directory in an earlier trusted
        # root is still part of the resolution search space: creating
        # and deleting a shadow there during compilation must not be
        # accepted merely because the namespace had no pinned files.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            first, second = root / "first", root / "second"
            (first / "Foo").mkdir(parents=True)
            public = parts(first, "Bar.Public")
            parts(second, "Foo.Private")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(first) + ":" + str(second)}, 5)
            metadata = {"importArts": {"Bar.Public": public}}
            before = optimizer.private_fallback_artifact_paths(tools, metadata)
            self.assertIn((first / "Foo").resolve(),
                          optimizer.cached_empty_inventory_directories(tools))
            optimizer.verify_private_fallback_inventory(tools, metadata, before)
            shadow = first / "Foo/Private.olean"
            shadow.write_bytes(b"transient empty-namespace shadow\n")
            shadow.unlink()
            with self.assertRaises(ValueError):
                optimizer.verify_private_fallback_inventory(tools, metadata, before)

    def test_empty_canonical_root_transient_shadow_is_rejected(self) -> None:
        # A completely fileless canonical LEAN_PATH root is still
        # searched by the forced compile, so its root directory itself
        # must be in inventory custody: creating and removing a
        # higher-priority private artifact there must be rejected even
        # though the root contains no namespace entries to pin.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            empty = root / ".lake/packages/EmptyPkg/.lake/build/lib/lean"
            empty.mkdir(parents=True)
            optimizer.write_json(root / "lake-manifest.json", {
                "version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": [{"type": "git", "name": "EmptyPkg", "scope": "",
                              "inherited": False,
                              "url": "https://example.invalid/EmptyPkg.git",
                              "rev": "0" * 40, "inputRev": "main",
                              "manifestFile": "lake-manifest.json",
                              "configFile": "lakefile.toml"}]})
            canonical = root / ".lake/build/lib/lean"
            parts(canonical, "Foo.Private")
            public = parts(canonical, "Bar.Public")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(empty) + ":" + str(canonical)}, 5)
            metadata = {"importArts": {"Bar.Public": public}}
            self.assertIn(empty.resolve(), optimizer.private_inventory_roots(tools, metadata))
            before = optimizer.private_fallback_artifact_paths(tools, metadata)
            record = optimizer.pin_private_fallback_inputs(tools, metadata)
            self.assertIn(empty.resolve(), optimizer.cached_empty_inventory_directories(tools))
            metadata_path = root / "setup.json"
            metadata_path.write_text(json.dumps(metadata) + "\n")
            snapshot_path = root / "snapshot.json"
            snapshot_path.write_text(json.dumps({
                "importArts": metadata["importArts"],
                "snapshot_compilations": {
                    "A.lean": {"setup": optimizer.file_pin(metadata_path)},
                },
            }) + "\n")
            self.assertIn(empty.resolve(), optimizer.snapshot_dependency_identities(
                snapshot_path, tools, setup_pin=optimizer.file_pin(snapshot_path)))
            optimizer.verify_input_manifest(record, before, tools.output, tools)
            shadow = empty / "Foo/Private.olean"
            shadow.parent.mkdir(parents=True)
            shadow.write_bytes(b"transient empty-root shadow\n")
            shadow.unlink()
            shadow.parent.rmdir()
            with self.assertRaises(ValueError):
                optimizer.verify_input_manifest(record, before, tools.output, tools)

    def test_private_only_namespace_is_seeded_from_canonical_project_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "bin").mkdir()
            canonical = root / ".lake/build/lib/lean"
            (canonical / "MathlibExt").mkdir(parents=True)
            (canonical / "MathlibExt/PointCount.olean").write_bytes(b"canonical private artifact\n")
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                    root, {"LEAN_PATH": str(root / "mathlib")}, 5)
            value = {"importArts": {"Mathlib.Public": parts(root / "mathlib", "Mathlib.Public")},
                     "snapshot_compilations": {"MathlibExt/Target.lean": {"module": "MathlibExt.Target"}}}
            roots = optimizer.private_dependency_roots(tools, value)
            self.assertEqual(roots["MathlibExt"], [str(canonical.resolve())])

    def test_escaped_module_components_preserve_dots_and_spaces(self) -> None:
        self.assertEqual(optimizer.private_module_components("A.«b.c».D"), ("A", "b.c", "D"))
        self.assertEqual(optimizer.private_module_path("A.«b.c».D"), Path("A", "b.c", "D"))
        self.assertEqual(optimizer.private_module_olean_path("A.«b.c»"), Path("A", "b.c.olean"))
        self.assertEqual(optimizer.private_module_components("«A B».C"), ("A B", "C"))

    def test_helpers_traverse_by_import_level(self) -> None:
        # Helper-source regression guard for the import-level P2:
        # discovery must choose public vs private module data from the
        # requested visibility, propagate `importAll`, and key
        # visitation by (module, level) so a public-first visit cannot
        # suppress a later private visit (or vice versa emit dupes).
        helpers = Path(optimizer.__file__).parent / "import_optimizer"
        for name in ("declarations.lean", "declarations_batch.lean", "private_imports.lean"):
            source = (helpers / name).read_text()
            self.assertIn("visibility : OLeanLevel", source, name)
            self.assertIn("Std.HashMap Name OLeanLevel", source, name)
            self.assertIn("dependency.importAll", source, name)
            self.assertIn("visibility == .private", source, name)
            self.assertNotIn("(seen : IO.Ref NameSet)", source, name)

    def test_private_import_map_accepts_helper_components_for_escaped_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            selected = root / "selected"
            public = parts(selected, "A.Public")
            stem = selected / "A" / "b.c" / "D"
            private = [[str(stem) + suffix for suffix in (".olean", ".olean.server", ".olean.private")],
                       [str(stem) + suffix for suffix in (".ir.sig", ".ir")]]
            for group in private:
                for name in group:
                    path = Path(name)
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b"escaped private artifact\n")
            value = {"importArts": {"A.Public": public},
                     "snapshot_compilations": {"A.lean": {"module": "A"}}}
            rows = [{"module": "A", "artifacts": parts(selected, "A")},
                    {"module": "A.Public", "artifacts": public},
                    {"module": "A.«b.c».D", "components": ["A", "b.c", "D"],
                     "artifacts": private}]
            result = optimizer.private_import_map(value, rows, {"A": [str(selected)]})
            self.assertEqual(result["A.«b.c».D"], private)


if __name__ == "__main__":
    unittest.main()
