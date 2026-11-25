#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Snapshot binding controls with retained dependency bytes and mocked Lean calls."""

from __future__ import annotations

import hashlib
import errno
import json
import os
import select
import stat
import sys
import tempfile
import unittest
from contextlib import contextmanager, nullcontext
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery
import test_import_optimizer_snapshot_groups as groups
from test_import_optimizer_snapshot_inputs import native_sibling


class SnapshotDependencyTests(unittest.TestCase):
    def root_bindings(self, roots):
        return (patch.object(optimizer, "canonical_artifact_roots", return_value=roots),
                patch.object(optimizer, "private_search_roots", return_value=roots),
                patch.object(optimizer, "standard_library_root", return_value=None))

    @unittest.skipUnless(sys.platform == "linux", "Linux verification controls require inotify")
    def test_linux_verification_does_not_resolve_normalized_components_again(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            original = optimizer.resolve_inventory_path
            direct = []

            def resolve(path):
                if sys._getframe(1).f_code.co_name == "verify_snapshot_dependencies":
                    direct.append(str(path))
                return original(path)

            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard, patch.object(optimizer, "resolve_inventory_path", new=resolve):
                optimizer.verify_snapshot_dependencies(tools, tools.output / "target/artifacts", setup, identities)
            self.assertGreater(len(identities), 640)
            self.assertEqual(direct[0], str(tools.output))
            print(json.dumps({"fixture": "complete_linux_snapshot_dependency_verification",
                              "actual_identity_rows": len(identities), "direct_genuine_resolutions": len(direct),
                              "entire_verification_returned": True}))
            self.assertEqual(direct, [str(tools.output)],
                             "Normalized Linux identity verification repeats resolved containment for each component")

    @unittest.skipUnless(sys.platform == "linux", "Linux verification controls require inotify")
    def test_guard_ancestry_does_not_expand_each_closed_component(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            artifacts = {root / "library/Fixture/Deep" / f"M{index}.olean" for index in range(24)}
            for artifact in artifacts:
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_bytes(b"Guarded lexical ancestry fixture\n")
            identities = optimizer.path_component_identities(set(artifacts))
            original = Path.parents
            reads = 0

            def parents(path):
                nonlocal reads
                reads += 1
                return original.__get__(path, Path)

            with patch.object(Path, "parents", property(parents)):
                with optimizer.guarded_inventory_components(set(identities)):
                    pass
            print(json.dumps({"fixture": "complete_real_inotify_guard_ancestry",
                              "identity_rows": len(identities), "parent_sequence_expansions": reads,
                              "real_inotify_guard_returned": True}))
            self.assertLessEqual(reads, 2, "Guard re-expands the ancestry of every already-bound component")

    @unittest.skipUnless(sys.platform == "linux", "Linux verification controls require inotify")
    def test_linux_strict_mutable_directory_comparison_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            identities[tools.output] = optimizer.path_component_identity(tools.output, strict=True)
            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard:
                optimizer.verify_snapshot_dependencies(tools, tools.output / "target/artifacts", setup, identities)

    @unittest.skipUnless(sys.platform == "linux", "Linux verification controls require inotify")
    def test_linux_strict_immutable_directory_still_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            identities[roots[0]] = optimizer.path_component_identity(roots[0], strict=True)
            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard:
                with self.assertRaisesRegex(ValueError, "Snapshot input identity changed"):
                    optimizer.verify_snapshot_dependencies(tools, tools.output / "target/artifacts", setup, identities)

    @unittest.skipUnless(sys.platform == "linux", "Linux verification controls require inotify")
    def test_linux_verification_rejects_restored_parent_alias(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            alias = root / "alias"
            alias.symlink_to(roots[0], target_is_directory=True)
            alternate = root / "alternate"
            alternate.mkdir()
            identities.update(optimizer.path_component_identities({alias / "Fixture/Deep/M0.olean"}))
            original = optimizer.snapshot_setup_value

            def reconstruct(*arguments, **keywords):
                result = original(*arguments, **keywords)
                backup = root / "alias-backup"
                alias.rename(backup)
                alias.symlink_to(alternate, target_is_directory=True)
                alias.unlink()
                backup.rename(alias)
                return result

            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard, patch.object(optimizer, "snapshot_setup_value", side_effect=reconstruct):
                with self.assertRaisesRegex(ValueError, "(Compilation|Snapshot collection) input path identity changed"):
                    optimizer.verify_snapshot_dependencies(tools, tools.output / "target/artifacts", setup, identities)

    @unittest.skipUnless(sys.platform == "linux", "Linux verification controls require inotify")
    def test_nonlinux_verification_keeps_resolved_mutability(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            canonical, search, standard = self.root_bindings(roots)
            original = optimizer.resolve_inventory_path
            direct = []

            def resolve(path):
                if sys._getframe(1).f_code.co_name == "verify_snapshot_dependencies":
                    direct.append(str(path))
                return original(path)

            with recovery.isolated_ancestor_metadata(root), \
                    patch.object(sys, "platform", "darwin"), canonical, search, standard:
                identities = optimizer.path_component_identities(set(identities), mutable_roots={tools.output})
                identities = {path: identity for path, identity in identities.items()
                              if path == root or root in path.parents}
                with patch.object(optimizer, "resolve_inventory_path", new=resolve):
                    optimizer.verify_snapshot_dependencies(tools, tools.output / "target/artifacts", setup, identities)
            self.assertEqual(direct[0], str(tools.output))
            self.assertEqual(set(direct[1:]), {str(path) for path in identities})
            self.assertEqual(len(direct), len(identities) + 1)


    @unittest.skipUnless(sys.platform == "linux", "Linux identity classification requires inotify")
    def test_linux_component_identities_keep_binding_without_repeated_classification(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            library = root / "library"
            artifacts = {library / "Fixture/Deep" / f"M{index}.olean" for index in range(32)}
            for artifact in artifacts:
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_bytes(b"Actual dependency identity fixture\n")
            alias = root / "alias"
            alias.symlink_to(library, target_is_directory=True)
            aliased_artifact = alias / "Fixture/Deep/M0.olean"
            output = root / "output"
            output.mkdir()
            mutable_alias = root / "mutable-alias"
            mutable_alias.symlink_to(output, target_is_directory=True)
            inputs = artifacts | {aliased_artifact}
            bound = inputs | {path.resolve() for path in inputs}
            expected_components = {component for path in bound for component in (path, *path.parents)}
            with optimizer.guarded_inventory_components(
                    inputs, mutable_roots={mutable_alias}, inventory_roots={library}):
                with patch.object(optimizer, "resolve_inventory_path",
                                  wraps=optimizer.resolve_inventory_path) as resolution:
                    actual = optimizer.path_component_identities(set(inputs), mutable_roots={mutable_alias})
            self.assertEqual(set(actual), expected_components)
            self.assertIn(aliased_artifact, actual)
            self.assertIn(next(iter(artifacts)), actual)
            self.assertEqual(actual[aliased_artifact], optimizer.path_component_identity(aliased_artifact))
            called_paths = [call.args[0] for call in resolution.call_args_list]
            self.assertEqual(called_paths[0], mutable_alias)
            self.assertEqual(set(called_paths[1:len(inputs) + 1]), inputs)
            print(json.dumps({"fixture": "real_linux_component_classification",
                              "original_paths": len(inputs), "identity_rows": len(actual),
                              "actual_genuine_resolutions": resolution.call_count,
                              "lexical_alias_and_canonical_components_retained": True,
                              "original_inotify_guard_completed": True}))
            self.assertEqual(resolution.call_count, len(inputs) + 1,
                             "Linux component classification repeats genuine resolution after binding")

    def test_fallback_collection_does_not_build_parent_identity_memo(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            library = root / "library"
            artifacts = [library / "Fixture/Deep" / f"M{index}.olean" for index in range(24)]
            for artifact in artifacts:
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_bytes(b"Actual fallback inventory fixture\n")
            (library / "Fixture/Empty").mkdir()
            output = root / "output"
            output.mkdir()
            generated = output / "Generated.olean"
            generated.write_bytes(b"Mutable output fixture\n")
            (library / "Fixture/Linked.olean").symlink_to(generated)
            metadata = {"importArts": {"Fixture.Deep.M0": [[str(artifacts[0])], []]}}
            with patch.object(optimizer, "canonical_artifact_roots", return_value=[library]), \
                    patch.object(optimizer, "private_search_roots", return_value=[library]), \
                    patch.object(optimizer, "standard_library_root", return_value=None):
                tools = optimizer.Tools(root, output, root / "lake", root / "lean", root, {}, 5)
                with patch.object(optimizer, "path_component_identity",
                                  wraps=optimizer.path_component_identity) as component_reads:
                    actual = optimizer.private_fallback_artifact_paths(tools, metadata)
            self.assertEqual(actual, tuple(sorted(str(path) for path in artifacts)))
            self.assertIn(library / "Fixture/Empty", tools.library_inventories[library / "Fixture"][1])
            self.assertEqual(component_reads.call_count, 0,
                             "Fallback collection adds per-path ancestor identity reads")

    @unittest.skipUnless(sys.platform == "linux", "Linux inventory guards require inotify")
    def test_guarded_inventory_does_not_resolve_bound_artifacts_again(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            library = root / "library"
            artifacts = {library / "Fixture/Deep" / f"M{index}.olean" for index in range(24)}
            for artifact in artifacts:
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_bytes(b"Guarded inventory fixture\n")
            empty = library / "Fixture/Empty"
            empty.mkdir()
            output = root / "output"
            output.mkdir()
            generated = output / "Generated.olean"
            generated.write_bytes(b"Mutable output fixture\n")
            alias = library / "Fixture/Linked.olean"
            alias.symlink_to(generated)
            metadata = {"importArts": {"Fixture.Deep.M0": [[str(library / "Fixture/Deep/M0.olean")], []]}}
            canonical, search, standard = self.root_bindings([library])
            with canonical, search, standard:
                tools = optimizer.Tools(root, output, root / "lake", root / "lean", root, {}, 5)
                with optimizer.guarded_inventory_components(
                        artifacts | {alias, generated, empty},
                        mutable_roots={output}, inventory_roots={library}):
                    with patch.object(optimizer, "resolve_inventory_path",
                                      wraps=optimizer.resolve_inventory_path) as resolution:
                        actual = optimizer.private_fallback_artifact_paths(tools, metadata)
            called = [call.args[0] for call in resolution.call_args_list]
            self.assertEqual(actual, tuple(sorted(str(path) for path in artifacts)))
            self.assertIn(empty, tools.library_inventories[library / "Fixture"][1])
            self.assertIn(alias, called)
            repeated = sum(path in artifacts for path in called)
            print(json.dumps({"fixture": "real_guarded_fallback_output_filter",
                              "actual_artifacts": len(actual), "bound_artifact_resolutions": repeated,
                              "alias_genuinely_resolved": True, "full_guard_returned": True}))
            self.assertEqual(repeated, 0, "Output filtering resolves already guarded canonical inputs again")

    @unittest.skipUnless(sys.platform == "linux", "Linux inventory guards require inotify")
    def test_guarded_output_filter_resolves_aliases_unknown_and_parent_parts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            output.mkdir()
            generated = output / "Generated.olean"
            generated.write_bytes(b"Mutable output fixture\n")
            library = root / "library"
            library.mkdir()
            alias = library / "Alias.olean"
            alias.symlink_to(generated)
            parent_alias = root / "parent-alias"
            parent_alias.symlink_to(output, target_is_directory=True)
            aliased_child = parent_alias / generated.name
            parent_parts = library / ".." / "output" / generated.name
            double_slash = Path("/" + str(generated))
            unknown = output / "Unknown.olean"
            unknown.write_bytes(b"Unknown output fixture\n")
            paths = {generated, alias, aliased_child, parent_parts, double_slash}
            with optimizer.guarded_inventory_components(paths, mutable_roots={output}):
                with patch.object(optimizer, "resolve_inventory_path",
                                  wraps=optimizer.resolve_inventory_path) as resolution:
                    self.assertFalse(optimizer.inventory_path_outside_output(generated, output.parts))
                    self.assertEqual(resolution.call_count, 0)
                    for path in (alias, aliased_child, parent_parts, double_slash, unknown):
                        self.assertFalse(optimizer.inventory_path_outside_output(path, output.parts))
                    self.assertEqual([call.args[0] for call in resolution.call_args_list],
                                     [alias, aliased_child, parent_parts, double_slash, unknown])

    @unittest.skipUnless(sys.platform == "linux", "Linux inventory guards require inotify")
    def test_guarded_output_filter_resolves_relative_and_nonlinux_paths(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            artifact = root / "Local.olean"
            artifact.write_bytes(b"Guarded inventory fixture\n")
            previous = Path.cwd()
            try:
                os.chdir(root)
                relative = Path(artifact.name)
                with optimizer.guarded_inventory_components({artifact, relative}):
                    with patch.object(optimizer, "resolve_inventory_path",
                                      wraps=optimizer.resolve_inventory_path) as resolution:
                        self.assertTrue(optimizer.inventory_path_outside_output(relative, ("/", "absent")))
                        with patch.object(sys, "platform", "darwin"):
                            self.assertTrue(optimizer.inventory_path_outside_output(artifact, ("/", "absent")))
                        self.assertEqual([call.args[0] for call in resolution.call_args_list], [relative, artifact])
            finally:
                os.chdir(previous)

    @unittest.skipUnless(sys.platform == "linux", "Linux inventory guards require inotify")
    def test_guarded_output_filter_rejects_restored_parent_alias(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            parent = root / "library"
            parent.mkdir()
            artifact = parent / "Local.olean"
            artifact.write_bytes(b"Guarded inventory fixture\n")
            output = root / "output"
            output.mkdir()
            (output / artifact.name).write_bytes(b"Mutable output fixture\n")
            retained = root / "retained"
            with self.assertRaisesRegex(ValueError, "Compilation input path identity changed"):
                with optimizer.guarded_inventory_components({artifact}, inventory_roots={parent}):
                    with patch.object(optimizer, "resolve_inventory_path",
                                      wraps=optimizer.resolve_inventory_path) as resolution:
                        self.assertTrue(optimizer.inventory_path_outside_output(artifact, output.parts))
                        self.assertEqual(resolution.call_count, 0)
                        parent.rename(retained)
                        try:
                            parent.symlink_to(output, target_is_directory=True)
                            optimizer.inventory_path_outside_output(artifact, output.parts)
                        finally:
                            if parent.is_symlink():
                                parent.unlink()
                            retained.rename(parent)
                        self.assertTrue(optimizer.inventory_path_outside_output(artifact, output.parts))
                        self.assertEqual(resolution.call_count, 0)

    @unittest.skipUnless(sys.platform == "linux", "Linux inventory guards require inotify")
    def test_guarded_output_filter_retains_final_artifact_identity_check(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            artifact = root / "Local.olean"
            artifact.write_bytes(b"Guarded inventory fixture\n")
            with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                with optimizer.guarded_inventory_components({artifact}):
                    self.assertTrue(optimizer.inventory_path_outside_output(artifact, ("/", "absent")))
                    artifact.write_bytes(b"Changed artifact while guarded\n")

    @unittest.skipUnless(sys.platform == "linux", "Linux inventory guards require inotify")
    def test_guarded_output_filter_resets_nested_and_exception_contexts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            artifact = root / "Local.olean"
            artifact.write_bytes(b"Guarded inventory fixture\n")
            other = root / "Other.olean"
            other.write_bytes(b"Inner inventory fixture\n")
            with patch.object(optimizer, "resolve_inventory_path",
                              wraps=optimizer.resolve_inventory_path) as resolution:
                with optimizer.guarded_inventory_components({artifact}):
                    self.assertTrue(optimizer.inventory_path_outside_output(artifact, ("/", "absent")))
                    self.assertEqual(resolution.call_count, 0)
                    with self.assertRaisesRegex(RuntimeError, "explicit nested guard failure"):
                        with optimizer.guarded_inventory_components({other}):
                            # The enclosing guard is still armed, so its
                            # canonical path stays proven inside the nested one.
                            self.assertTrue(optimizer.inventory_path_outside_output(artifact, ("/", "absent")))
                            self.assertTrue(optimizer.inventory_path_outside_output(other, ("/", "absent")))
                            self.assertEqual(resolution.call_count, 0)
                            raise RuntimeError("explicit nested guard failure")
                    # The nested guard's own path left with its exception.
                    self.assertTrue(optimizer.inventory_path_outside_output(artifact, ("/", "absent")))
                    self.assertTrue(optimizer.inventory_path_outside_output(other, ("/", "absent")))
                    self.assertEqual(resolution.call_count, 1)
                self.assertTrue(optimizer.inventory_path_outside_output(artifact, ("/", "absent")))
                self.assertEqual(resolution.call_count, 2)

    def test_snapshot_rejects_changed_setup_before_reading_injected_context(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            injected = tools.output / "injected-context.json"
            optimizer.write_json(injected, {"name": "Injected", "importArts": {}})
            value = optimizer.read_json(setup)
            value["snapshot_compilations"]["Fixture.lean"]["setup"] = optimizer.file_pin(injected)
            optimizer.write_json(setup, value)
            original = optimizer.read_json
            parsed: list[Path] = []

            def read(path: Path) -> dict[str, object]:
                parsed.append(path)
                return original(path)

            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard, patch.object(optimizer, "read_json", new=read):
                with self.assertRaises(ValueError):
                    optimizer.verify_snapshot_dependencies(
                        tools, tools.output / "target/artifacts", setup, identities)
            print(json.dumps({"fixture": "changed_snapshot_setup", "actual_parsed_JSON_paths":
                              [str(path) for path in parsed], "injected_context": str(injected)}))
            self.assertNotIn(injected, parsed,
                             "Changed snapshot setup was followed before its saved identity was checked")

    def test_snapshot_rejects_changed_context_before_parsing_it(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            context = tools.output / "context-setup.json"
            optimizer.write_json(context, {"name": "Injected", "importArts": {}})
            original = optimizer.read_json
            parsed: list[Path] = []

            def read(path: Path) -> dict[str, object]:
                parsed.append(path)
                return original(path)

            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard, patch.object(optimizer, "read_json", new=read):
                with self.assertRaises(ValueError):
                    optimizer.verify_snapshot_dependencies(
                        tools, tools.output / "target/artifacts", setup, identities)
            print(json.dumps({"fixture": "changed_context_setup", "actual_parsed_JSON_paths":
                              [str(path) for path in parsed], "changed_context": str(context)}))
            self.assertNotIn(context, parsed,
                             "Changed context metadata was parsed before its saved receipt was checked")

    @unittest.skipUnless(sys.platform == "linux", "Transient setup paths require inotify")
    def test_snapshot_guards_context_lookup_against_restored_parent_move(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            context = tools.output / "context-setup.json"
            moved = root / "moved-output"
            original = optimizer.read_json
            changed = False

            def read(path: Path) -> dict[str, object]:
                nonlocal changed
                value = original(path)
                if path == context and not changed:
                    changed = True
                    tools.output.rename(moved)
                    try:
                        tools.output.symlink_to(moved, target_is_directory=True)
                    finally:
                        if tools.output.is_symlink():
                            tools.output.unlink()
                        moved.rename(tools.output)
                return value

            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard, patch.object(optimizer, "read_json", new=read):
                with self.assertRaises(ValueError):
                    optimizer.verify_snapshot_dependencies(
                        tools, tools.output / "target/artifacts", setup, identities)
            self.assertTrue(changed, "The actual setup-parent replacement branch was not exercised")
            self.assertTrue(setup.is_file())

    def validation_fixture(self, root: Path) -> tuple[
            optimizer.Tools, Path, list[Path], dict[Path, optimizer.SourceIdentity]]:
        tools, _, roots = self.collection_fixture(root)
        metadata = {**optimizer.read_json(root / "context-setup.json"),
                    "name": "Fixture", "isModule": False, "dynlibs": [], "plugins": []}
        for groups in metadata["importArts"].values():
            prefix = Path(groups[0][0]).with_suffix("")
            for suffix in (".olean.server", ".olean.private", ".ir.sig", ".ir"):
                Path(str(prefix) + suffix).write_bytes(b"Mocked native artifact part\n")
        context_setup = tools.output / "context-setup.json"
        manifest = tools.output / "input-manifest.json"
        setup = tools.output / "snapshot-setup.json"
        artifact_root = tools.output / "target/artifacts"
        artifact_root.mkdir(parents=True)
        (artifact_root / "Fixture.olean").write_bytes(b"Mocked target artifact\n")
        optimizer.write_json(context_setup, metadata)
        with patch.object(optimizer, "canonical_artifact_roots", return_value=roots), \
                patch.object(optimizer, "private_search_roots", return_value=roots), \
                patch.object(optimizer, "standard_library_root", return_value=None):
            paths = optimizer.compilation_input_paths(metadata, root, None, tools)
            optimizer.write_json(manifest, {"files": [optimizer.file_pin(Path(path)) for path in paths]})
            context = {"module": "Fixture", "setup": optimizer.file_pin(context_setup),
                       "input_manifest": optimizer.file_pin(manifest),
                       "private_fallback_manifest": optimizer.file_pin(manifest),
                       "standard_library_root": None, "artifact_root": str(artifact_root),
                       "header_is_module": False}
            optimizer.write_json(setup, optimizer.snapshot_setup_value(
                tools, artifact_root, {"Fixture.lean": context}, "single"))
            identities = optimizer.snapshot_dependency_identities(setup, tools, setup_pin=optimizer.file_pin(setup))
        return tools, setup, roots, identities

    def test_snapshot_setup_rechecks_context_before_second_parse(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, _ = self.validation_fixture(root)
            value = optimizer.read_json(setup)
            context = tools.output / "context-setup.json"
            changed_metadata = {**optimizer.read_json(context), "changed_after_validation": True}
            original_artifacts = optimizer.full_import_artifacts
            original_read = optimizer.read_json
            changed = False
            parsed_changed = []

            def artifacts(*arguments, **keywords):
                nonlocal changed
                result = original_artifacts(*arguments, **keywords)
                if not changed:
                    optimizer.write_json(context, changed_metadata)
                    changed = True
                return result

            def read(path):
                if changed and path == context:
                    parsed_changed.append(path)
                return original_read(path)

            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard, \
                    patch.object(optimizer, "full_import_artifacts", new=artifacts), \
                    patch.object(optimizer, "read_json", new=read):
                with self.assertRaises(ValueError):
                    optimizer.snapshot_setup_value(tools, tools.output / "target/artifacts",
                        value["snapshot_compilations"], value["snapshot_kind"])
            self.assertTrue(changed, "The mutation between context parses was not exercised")
            self.assertEqual(parsed_changed, [], "Changed context was parsed without its saved pin")

    def test_nonlinux_inventory_guard_accepts_absent_configured_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            setup = root / "setup.json"
            setup.write_text("{}\n")
            output = root / "not-created-output"
            with recovery.isolated_ancestor_metadata(root), \
                    patch.object(optimizer.sys, "platform", "darwin"):
                with optimizer.guarded_inventory_components({setup}, mutable_roots={output}):
                    self.assertEqual(optimizer.read_json(setup), {})
            self.assertFalse(output.exists())

    def test_nonlinux_inventory_guards_reject_child_changes(self) -> None:
        for root_only in (False, True):
            with self.subTest(root_only=root_only), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                inventory = root / "inventory"
                inventory.mkdir()
                artifact = inventory / "Extra.olean"
                with patch.object(optimizer.sys, "platform", "darwin"):
                    with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                        with optimizer.guarded_inventory_components(
                                set() if root_only else {inventory},
                                inventory_roots={inventory} if root_only else ()):
                            artifact.write_bytes(b"Newly discoverable inventory artifact\n")

    def test_watched_immutable_inventory_directory_keeps_child_stamps(self) -> None:
        @contextmanager
        def watch_all(identities):
            yield {path for path, identity in identities.items() if stat.S_ISDIR(identity[5])}

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            inventory = root / "inventory"
            inventory.mkdir()
            with patch.object(optimizer.sys, "platform", "darwin"), \
                    patch.object(optimizer, "guard_ancestor_moves", new=watch_all):
                with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                    with optimizer.guarded_inventory_components({inventory}, inventory_roots={inventory}):
                        (inventory / "Injected.olean").write_bytes(b"Immutable child mutation\n")

    @unittest.skipUnless(hasattr(select, "kqueue"), "Permitted mutable writes require a native watch")
    def test_nonlinux_inventory_guard_allows_mutable_child_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            output.mkdir()
            setup = output / "setup.json"
            setup.write_text("{}\n")
            with patch.object(optimizer.sys, "platform", "darwin"):
                with optimizer.guarded_inventory_components(
                        {setup, output}, mutable_roots={output}):
                    (output / "receipt.json").write_text("{}\n")

    @unittest.skipUnless(hasattr(select, "kqueue"), "Native ancestor watches require kqueue")
    def test_nonlinux_inventory_guard_allows_unrelated_ancestor_sibling_writes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            metadata = root / "metadata"
            metadata.mkdir()
            setup = metadata / "setup.json"
            setup.write_text("{}\n")
            with optimizer.guarded_inventory_components({setup}):
                (root / "unrelated-sibling").write_text("Unrelated activity\n")

    @unittest.skipUnless(hasattr(select, "kqueue"), "Native ancestor watches require kqueue")
    def test_nonlinux_inventory_guard_rejects_restored_explicit_mutable_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            output.mkdir()
            setup = output / "setup.json"
            setup.write_text('{"original": true}\n')
            moved = root / "saved-output"
            with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                with optimizer.guarded_inventory_components({setup, output}, mutable_roots={output}):
                    output.rename(moved)
                    output.mkdir()
                    setup.write_text('{"injected": true}\n')
                    self.assertEqual(optimizer.read_json(setup), {"injected": True})
                    setup.unlink()
                    output.rmdir()
                    moved.rename(output)

    def test_nonlinux_inventory_guard_rejects_restored_ancestor_tree(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            ancestor = root / "ancestor"
            input_directory = ancestor / "inputs"
            input_directory.mkdir(parents=True)
            setup = input_directory / "setup.json"
            setup.write_text('{"original": true}\n')
            moved = root / "saved-ancestor"
            with patch.object(optimizer.sys, "platform", "darwin"):
                with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                    with optimizer.guarded_inventory_components({setup}):
                        ancestor.rename(moved)
                        input_directory.mkdir(parents=True)
                        setup.write_text('{"injected": true}\n')
                        self.assertEqual(optimizer.read_json(setup), {"injected": True})
                        setup.unlink()
                        input_directory.rmdir()
                        ancestor.rmdir()
                        moved.rename(ancestor)
            self.assertEqual(optimizer.read_json(setup), {"original": True})

    def test_nonlinux_inventory_guard_rejects_restored_mutable_metadata_ancestor(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            ancestor = output / "metadata"
            ancestor.mkdir(parents=True)
            setup = ancestor / "setup.json"
            setup.write_text('{"original": true}\n')
            moved = output / "saved-metadata"
            with patch.object(optimizer.sys, "platform", "darwin"):
                with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                    with optimizer.guarded_inventory_components({setup}, mutable_roots={output}):
                        ancestor.rename(moved)
                        ancestor.mkdir()
                        setup.write_text('{"injected": true}\n')
                        self.assertEqual(optimizer.read_json(setup), {"injected": True})
                        setup.unlink()
                        ancestor.rmdir()
                        moved.rename(ancestor)
            self.assertEqual(optimizer.read_json(setup), {"original": True})

    def test_nonlinux_unwatched_broad_input_guard_rejects_restored_mutable_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            metadata = output / "metadata"
            metadata.mkdir(parents=True)
            setup = metadata / "setup.json"
            setup.write_text('{"original": true}\n')
            saved = output / "saved-metadata"
            with patch.object(optimizer.sys, "platform", "darwin"):
                # guard_ancestor_moves is explicitly unavailable for this case.
                with patch.object(optimizer, "guard_ancestor_moves",
                                  return_value=nullcontext(set())):
                    with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                        with optimizer.guarded_inventory_components(
                                {setup, metadata, output}, mutable_roots={output}):
                            metadata.rename(saved)
                            metadata.mkdir()
                            setup.write_text('{"injected": true}\n')
                            self.assertEqual(optimizer.read_json(setup), {"injected": True})
                            setup.unlink()
                            metadata.rmdir()
                            saved.rename(metadata)
            self.assertEqual(optimizer.read_json(setup), {"original": True})

    def test_ancestor_guard_falls_back_on_descriptor_exhaustion(self) -> None:
        class Queue:
            def control(self, *arguments):
                return []

            def close(self):
                pass

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            expected = {root: optimizer.path_component_identity(root, strict=True)}
            for code in (errno.EMFILE, errno.ENFILE):
                with self.subTest(code=code), \
                        patch.object(optimizer.select, "kqueue", create=True, return_value=Queue()), \
                        patch.multiple(optimizer.select, create=True, KQ_NOTE_RENAME=1,
                                       KQ_NOTE_DELETE=2, KQ_NOTE_ATTRIB=4, KQ_NOTE_REVOKE=8), \
                        patch.object(optimizer.os, "open", side_effect=OSError(code, "descriptor limit")):
                    with optimizer.guard_ancestor_moves(expected) as watched:
                        self.assertEqual(watched, set())

    def test_ancestor_guard_falls_back_when_queue_descriptor_is_exhausted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            expected = {root: optimizer.path_component_identity(root, strict=True)}
            for code in (errno.EMFILE, errno.ENFILE):
                with self.subTest(code=code), \
                        patch.object(optimizer.select, "kqueue", create=True,
                                     side_effect=OSError(code, "queue descriptor limit")):
                    with optimizer.guard_ancestor_moves(expected) as watched:
                        self.assertEqual(watched, set())

    def test_ancestor_guard_closes_accumulated_watches_before_fallback(self) -> None:
        class Queue:
            closed = False

            def control(self, *arguments):
                return []

            def close(self):
                self.closed = True

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            children = [root / "first", root / "second"]
            for path in children:
                path.mkdir()
            setup = root / "setup.json"
            setup.write_text("{}\n")
            identities = {path: optimizer.path_component_identity(path, strict=True) for path in children}
            original_open = os.open
            opened = []

            def open_one(path, flags):
                if opened:
                    raise OSError(errno.EMFILE, "synthetic descriptor limit")
                descriptor = original_open(path, flags)
                opened.append(descriptor)
                return descriptor

            queue = Queue()
            with patch.object(optimizer.select, "kqueue", create=True, return_value=queue), \
                    patch.multiple(optimizer.select, create=True, KQ_NOTE_RENAME=1,
                                   KQ_NOTE_DELETE=2, KQ_NOTE_ATTRIB=4, KQ_NOTE_REVOKE=8,
                                   KQ_FILTER_VNODE=1, KQ_EV_ADD=1, KQ_EV_CLEAR=2), \
                    patch.object(optimizer.select, "kevent", create=True, return_value=object()), \
                    patch.object(optimizer.os, "open", side_effect=open_one):
                with optimizer.guard_ancestor_moves(identities) as watched:
                    self.assertEqual(watched, set())
                    self.assertTrue(queue.closed)
                    with self.assertRaises(OSError):
                        os.fstat(opened[0])
                    self.assertEqual(setup.read_text(), "{}\n")

    @unittest.skipUnless(hasattr(select, "kqueue"), "Native descriptor-limit stress requires kqueue")
    def test_ancestor_guard_large_inventory_with_low_descriptor_limit(self) -> None:
        import resource

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            children = [root / f"directory-{index}" for index in range(96)]
            for path in children:
                path.mkdir()
            identities = {path: optimizer.path_component_identity(path, strict=True) for path in children}
            setup = root / "setup.json"
            setup.write_text("{}\n")
            soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
            try:
                resource.setrlimit(resource.RLIMIT_NOFILE, (min(soft, 64), hard))
                with optimizer.guard_ancestor_moves(identities) as watched:
                    self.assertEqual(watched, set())
                    self.assertEqual(setup.read_text(), "{}\n")
            finally:
                resource.setrlimit(resource.RLIMIT_NOFILE, (soft, hard))

    def test_nonlinux_inventory_guard_rejects_restored_final_symlink_target(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            target = root / "target.json"
            original = b'{"original": true}\n'
            target.write_bytes(original)
            setup = root / "setup.json"
            setup.symlink_to(target)
            with patch.object(optimizer.sys, "platform", "darwin"):
                with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                    with optimizer.guarded_inventory_components({setup}):
                        target.write_text('{"injected": true}\n')
                        self.assertEqual(optimizer.read_json(setup), {"injected": True})
                        target.write_bytes(original)
            self.assertEqual(optimizer.read_json(setup), {"original": True})

    @unittest.skipUnless(hasattr(select, "kqueue"), "Native intermediate symlink custody requires kqueue")
    def test_nonlinux_inventory_guard_rejects_restored_intermediate_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            original = root / "original"
            injected = root / "injected"
            original.mkdir()
            injected.mkdir()
            (original / "setup.json").write_text('{"original": true}\n')
            (injected / "setup.json").write_text('{"injected": true}\n')
            bridge = root / "bridge"
            bridge.symlink_to(original, target_is_directory=True)
            setup = root / "setup.json"
            setup.symlink_to(bridge / "setup.json")
            with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                with optimizer.guarded_inventory_components({setup}):
                    bridge.unlink()
                    bridge.symlink_to(injected, target_is_directory=True)
                    self.assertEqual(optimizer.read_json(setup), {"injected": True})
                    bridge.unlink()
                    bridge.symlink_to(original, target_is_directory=True)
            self.assertEqual(optimizer.read_json(setup), {"original": True})

    def test_resolution_trace_retains_intermediate_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            target = root / "target"
            target.mkdir()
            metadata = target / "setup.json"
            metadata.write_text("{}\n")
            bridge = root / "bridge"
            bridge.symlink_to(target, target_is_directory=True)
            setup = root / "setup.json"
            setup.symlink_to(bridge / "setup.json")
            resolved, identities = optimizer.resolution_component_identities(setup)
            self.assertEqual(resolved, metadata)
            self.assertTrue(stat.S_ISLNK(identities[setup][5]))
            self.assertTrue(stat.S_ISLNK(identities[bridge][5]))
            self.assertIn(metadata, identities)

    def test_nonlinux_inventory_guard_binds_final_symlink_resolution_under_custody(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            target = root / "target.json"
            target.write_text('{"original": true}\n')
            decoy = root / "decoy.json"
            decoy.write_text('{"decoy": true}\n')
            setup = root / "setup.json"
            setup.symlink_to(target)
            original_resolve = Path.resolve
            calls = 0
            entered = False

            def resolve(path, *arguments, **keywords):
                nonlocal calls
                if path == setup:
                    calls += 1
                    if calls == 1:
                        return decoy
                return original_resolve(path, *arguments, **keywords)

            with patch.object(optimizer.sys, "platform", "darwin"), \
                    patch.object(Path, "resolve", autospec=True, side_effect=resolve):
                with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                    with optimizer.guarded_inventory_components({setup}):
                        entered = True
                        self.assertEqual(optimizer.read_json(setup), {"original": True})
            self.assertFalse(entered, "The body ran before the canonical target was bound under custody")
            self.assertGreaterEqual(calls, 1)

    def test_nonlinux_inventory_guard_rejects_symlink_escape_from_mutable_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            output.mkdir()
            immutable = root / "immutable"
            guarded = immutable / "guarded"
            guarded.mkdir(parents=True)
            escape = output / "escape"
            escape.symlink_to(immutable, target_is_directory=True)
            with patch.object(optimizer.sys, "platform", "darwin"):
                with self.assertRaisesRegex(ValueError, "Snapshot collection input path identity changed"):
                    with optimizer.guarded_inventory_components(
                            {escape / "guarded"}, mutable_roots={output}):
                        (guarded / "Injected.olean").write_bytes(b"Immutable input mutation\n")

    @unittest.skipUnless(hasattr(select, "kqueue"), "Permitted mutable writes require a native watch")
    def test_nonlinux_inventory_guard_allows_symlink_ingress_into_mutable_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            guarded = output / "guarded"
            guarded.mkdir(parents=True)
            alias = root / "output-alias"
            alias.symlink_to(output, target_is_directory=True)
            with patch.object(optimizer.sys, "platform", "darwin"):
                with optimizer.guarded_inventory_components(
                        {alias / "guarded"}, mutable_roots={output}):
                    (guarded / "receipt.json").write_text("{}\n")

    def test_snapshot_setup_guards_transient_target_mode_read(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, _ = self.validation_fixture(root)
            value = optimizer.read_json(setup)
            context = tools.output / "context-setup.json"
            original_bytes = context.read_bytes()
            original_read = optimizer.read_json
            reads = 0
            changed = False

            def read(path):
                nonlocal reads, changed
                if path != context:
                    return original_read(path)
                reads += 1
                if reads != 2:
                    return original_read(path)
                metadata = original_read(context)
                metadata["isModule"] = True
                optimizer.write_json(context, metadata)
                changed = True
                try:
                    return original_read(context)
                finally:
                    context.write_bytes(original_bytes)

            canonical, search, standard = self.root_bindings(roots)
            rejected = False
            actual = None
            with canonical, search, standard, patch.object(optimizer, "read_json", new=read):
                try:
                    actual = optimizer.snapshot_setup_value(
                        tools, tools.output / "target/artifacts",
                        value["snapshot_compilations"], value["snapshot_kind"])
                except ValueError:
                    rejected = True
            self.assertTrue(changed, "The second context mode read was not exercised")
            self.assertEqual(context.read_bytes(), original_bytes)
            self.assertFalse(original_read(context)["isModule"])
            if actual is not None:
                self.assertEqual(len(actual["importArts"]["Fixture"][0]), 3,
                                 "The transient mode did not alter target artifact selection")
            self.assertTrue(rejected, "A transient mode replaced the pinned target artifact selection")

    @unittest.skipUnless(sys.platform == "linux", "Linux audit reuse requires inotify")
    def test_snapshot_validation_bounds_shared_component_reads(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            original = Path.lstat
            calls = 0

            def lstat(path: Path, **keywords: object) -> os.stat_result:
                nonlocal calls
                calls += 1
                return original(path, **keywords)

            with patch.object(optimizer, "canonical_artifact_roots", return_value=roots), \
                    patch.object(optimizer, "private_search_roots", return_value=roots), \
                    patch.object(optimizer, "standard_library_root", return_value=None), \
                    patch.object(Path, "lstat", autospec=True, side_effect=lstat):
                optimizer.verify_snapshot_dependencies(tools, tools.output / "target/artifacts", setup, identities)
            self.assertGreater(len(identities), 5 * 128)
            self.assertIn(roots[0] / "Empty/nested", identities)
            self.assertIn(roots[1] / "nested", identities)
            self.assertLess(calls, 12 * 5 * 128, "Readonly validation repeats ancestor lstat calls")

    @unittest.skipUnless(sys.platform == "linux", "Linux audit reuse requires inotify")
    def test_snapshot_validation_rejects_component_changes_before_return(self) -> None:
        for changed_component in ("directory", "artifact"):
            with self.subTest(component=changed_component), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, setup, roots, identities = self.validation_fixture(root)
                original_identity = optimizer.path_component_identity
                original_setup = optimizer.snapshot_setup_value
                changed = False
                selected = roots[0] if changed_component == "directory" else roots[0] / "Fixture/Deep/M0.olean"

                def identity(path: Path, **keywords: object) -> optimizer.SourceIdentity:
                    result = original_identity(path, **keywords)
                    return (result[0], result[1] + 1, *result[2:]) if changed and path == selected else result

                def reconstruct(*arguments: object, **keywords: object) -> dict[str, object]:
                    nonlocal changed
                    result = original_setup(*arguments, **keywords)
                    changed = True  # Mocked identity change after the genuine reconstruction.
                    return result

                with patch.object(optimizer, "canonical_artifact_roots", return_value=roots), \
                        patch.object(optimizer, "private_search_roots", return_value=roots), \
                        patch.object(optimizer, "standard_library_root", return_value=None), \
                        patch.object(optimizer, "path_component_identity", side_effect=identity), \
                        patch.object(optimizer, "snapshot_setup_value", side_effect=reconstruct):
                    with self.assertRaisesRegex(ValueError, "collection input path identity changed"):
                        optimizer.verify_snapshot_dependencies(
                            tools, tools.output / "target/artifacts", setup, identities)

    @unittest.skipUnless(sys.platform == "linux", "Linux audit reuse requires inotify")
    def test_snapshot_validation_rejects_artifact_changes_between_calls(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots, identities = self.validation_fixture(root)
            with patch.object(optimizer, "canonical_artifact_roots", return_value=roots), \
                    patch.object(optimizer, "private_search_roots", return_value=roots), \
                    patch.object(optimizer, "standard_library_root", return_value=None):
                optimizer.verify_snapshot_dependencies(tools, tools.output / "target/artifacts", setup, identities)
                artifact = roots[0] / "Fixture/Deep/M0.olean"
                artifact.write_bytes(b"Changed artifact after the first validation\n")
                with self.assertRaisesRegex(ValueError, "Snapshot input identity changed"):
                    optimizer.verify_snapshot_dependencies(
                        tools, tools.output / "target/artifacts", setup, identities)

    def collection_fixture(self, root: Path) -> tuple[optimizer.Tools, Path, list[Path]]:
        package = root / "package"
        artifacts = [package / "Fixture/Deep" / f"M{index}.olean" for index in range(128)]
        for index, path in enumerate(artifacts):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(f"Collection artifact {index}\n".encode())
        (package / "Empty/nested").mkdir(parents=True)
        empty_root = root / "empty-root"
        (empty_root / "nested").mkdir(parents=True)
        output = root / "output"
        output.mkdir()
        tools = optimizer.Tools(root, output, root / "lake", root / "lean", root, {}, 5)
        metadata = {"importArts": {
            f"Fixture.Deep.M{index}": [[str(path)], []] for index, path in enumerate(artifacts)
        }}
        context_setup = root / "context-setup.json"
        manifest = root / "input-manifest.json"
        optimizer.write_json(context_setup, metadata)
        optimizer.write_json(manifest, {"files": [
            {"path": str(path), "bytes": path.stat().st_size,
             "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in artifacts
        ]})
        setup = root / "snapshot-setup.json"
        optimizer.write_json(setup, {**metadata, "snapshot_compilations": {
            "Fixture.lean": {"module": "Fixture", "setup": optimizer.file_pin(context_setup),
                             "input_manifest": optimizer.file_pin(manifest),
                             "private_fallback_manifest": optimizer.file_pin(manifest)}
        }})
        return tools, setup, [package, empty_root]

    def test_snapshot_collection_guards_first_context_root_discovery(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots = self.collection_fixture(root)
            context = root / "context-setup.json"
            original_bytes = context.read_bytes()
            injected_root = root / "injected-namespace"
            injected = injected_root / "Injected/Extra.olean"
            injected.parent.mkdir(parents=True)
            injected.write_bytes(b"Unlisted context inventory artifact\n")
            original_read = optimizer.read_json
            changed = False
            observed = []

            def read(path):
                nonlocal changed
                if path != context or changed:
                    return original_read(path)
                metadata = original_read(context)
                metadata["importArts"]["Injected.Extra"] = [[str(injected)], []]
                optimizer.write_json(context, metadata)
                changed = True
                try:
                    value = original_read(context)
                    observed.append(value)
                    return value
                finally:
                    context.write_bytes(original_bytes)

            canonical, search, standard = self.root_bindings(roots)
            rejected = False
            actual = None
            with canonical, search, standard, patch.object(optimizer, "read_json", new=read):
                try:
                    actual = optimizer.snapshot_dependency_identities(
                        setup, tools, setup_pin=optimizer.file_pin(setup))
                except ValueError:
                    rejected = True
            self.assertTrue(changed, "The first context read was not exercised")
            self.assertEqual(len(observed), 1)
            self.assertIn("Injected.Extra", observed[0]["importArts"])
            self.assertEqual(context.read_bytes(), original_bytes)
            self.assertNotIn(str(injected_root), setup.read_text())
            if actual is not None:
                self.assertIn(injected_root, actual, "The changed metadata did not affect root discovery")
            self.assertTrue(rejected, "The collector accepted a transient unlisted context inventory root")

    def test_snapshot_collection_guards_first_manifest_path_discovery(self) -> None:
        for field in ("input_manifest", "private_fallback_manifest"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, setup, roots = self.collection_fixture(root)
                value = optimizer.read_json(setup)
                context = value["snapshot_compilations"]["Fixture.lean"]
                fallback = root / "fallback-manifest.json"
                fallback.write_bytes(Path(context["input_manifest"]["path"]).read_bytes())
                context["private_fallback_manifest"] = optimizer.file_pin(fallback)
                optimizer.write_json(setup, value)
                manifest = Path(context[field]["path"])
                original_bytes = manifest.read_bytes()
                injected = root / "unlisted/Extra.olean"
                injected.parent.mkdir()
                injected.write_bytes(b"Unlisted manifest inventory artifact\n")
                original_read = optimizer.read_json
                changed = False
                observed = []

                def read(path):
                    nonlocal changed
                    if path != manifest or changed:
                        return original_read(path)
                    metadata = original_read(manifest)
                    metadata["files"].append(optimizer.file_pin(injected))
                    optimizer.write_json(manifest, metadata)
                    changed = True
                    try:
                        parsed = original_read(manifest)
                        observed.append(parsed)
                        return parsed
                    finally:
                        manifest.write_bytes(original_bytes)

                canonical, search, standard = self.root_bindings(roots)
                rejected = False
                actual = None
                with canonical, search, standard, patch.object(optimizer, "read_json", new=read):
                    try:
                        actual = optimizer.snapshot_dependency_identities(
                            setup, tools, setup_pin=optimizer.file_pin(setup))
                    except ValueError:
                        rejected = True
                self.assertTrue(changed, "The first manifest read was not exercised")
                self.assertEqual(len(observed), 1)
                self.assertIn(str(injected), {row["path"] for row in observed[0]["files"]})
                self.assertEqual(manifest.read_bytes(), original_bytes)
                if actual is not None:
                    self.assertIn(injected, actual, "The changed manifest did not affect path discovery")
                self.assertTrue(rejected, "The collector accepted transient unlisted manifest paths")

    def test_private_inventory_roots_guard_their_context_read(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots = self.collection_fixture(root)
            value = optimizer.read_json(setup)
            context = root / "context-setup.json"
            original_bytes = context.read_bytes()
            injected_root = root / "unlisted-direct-root"
            injected = injected_root / "Injected/Extra.olean"
            injected.parent.mkdir(parents=True)
            injected.write_bytes(b"Unlisted direct root artifact\n")
            original_read = optimizer.read_json
            changed = False

            def read(path):
                nonlocal changed
                if path != context or changed:
                    return original_read(path)
                metadata = original_read(context)
                metadata["importArts"]["Injected.Extra"] = [[str(injected)], []]
                optimizer.write_json(context, metadata)
                changed = True
                try:
                    return original_read(context)
                finally:
                    context.write_bytes(original_bytes)

            canonical, search, standard = self.root_bindings(roots)
            rejected = False
            actual = None
            with canonical, search, standard, patch.object(optimizer, "read_json", new=read):
                try:
                    actual = optimizer.snapshot_private_inventory_roots(tools, value)
                except ValueError:
                    rejected = True
            self.assertTrue(changed, "The root selector's actual context read was not exercised")
            self.assertEqual(context.read_bytes(), original_bytes)
            if actual is not None:
                self.assertIn(injected_root, actual, "The transient context did not select an unlisted root")
            self.assertTrue(rejected, "Root selection returned an unlisted transient context root")

    def test_snapshot_batch_guards_group_read_before_native_watch(self) -> None:
        case = groups.GroupedSnapshotTests()
        with case.capture() as (root, _calls, invoke):
            injected = root / "unlisted-group-source.lean"
            injected.write_bytes(b"Opaque unlisted group source fixture\n")
            original_read = optimizer.read_json
            original_guard = optimizer.guard_path_component_moves
            changed = False
            group_path = None
            original_bytes = None
            armed_with_unlisted = []

            def read(path):
                nonlocal changed, group_path, original_bytes
                if path.name != "snapshot-group.json" or changed:
                    return original_read(path)
                value = original_read(path)
                group_path, original_bytes = path, path.read_bytes()
                value["members"][0]["compilation"]["source_path"] = str(injected)
                optimizer.write_json(path, value)
                changed = True
                try:
                    return original_read(path)
                finally:
                    path.write_bytes(original_bytes)

            @contextmanager
            def guard(identities, *arguments, **keywords):
                if injected in identities:
                    armed_with_unlisted.append(injected)
                with original_guard(identities, *arguments, **keywords):
                    yield

            with patch.object(optimizer, "read_json", new=read), \
                    patch.object(optimizer, "guard_path_component_moves", new=guard):
                invoke()
            self.assertTrue(changed, "The first saved-group read was not exercised")
            self.assertEqual(group_path.read_bytes(), original_bytes)
            self.assertEqual(armed_with_unlisted, [],
                             "A native watcher accepted inputs from the transient group metadata")

    @unittest.skipUnless(sys.platform == "linux", "Linux collection controls require inotify")
    def test_snapshot_collection_rechecks_context_pin_inside_fresh_guard(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots = self.collection_fixture(root)
            context = root / "context-setup.json"
            changed_metadata = {**optimizer.read_json(context), "changed_after_pin": True}
            original_guard = optimizer.guarded_inventory_components
            original_read = optimizer.read_json
            changed = False
            parsed_changed = []

            @contextmanager
            def guard(paths, *arguments, **keywords):
                nonlocal changed
                if context in paths and "inventory_roots" in keywords and not changed:
                    optimizer.write_json(context, changed_metadata)
                    changed = True
                with original_guard(paths, *arguments, **keywords):
                    yield

            def read(path):
                if changed and path == context:
                    parsed_changed.append(path)
                return original_read(path)

            canonical, search, standard = self.root_bindings(roots)
            with canonical, search, standard, \
                    patch.object(optimizer, "guarded_inventory_components", new=guard), \
                    patch.object(optimizer, "read_json", new=read):
                with self.assertRaises(ValueError):
                    optimizer.snapshot_dependency_identities(setup, tools, setup_pin=optimizer.file_pin(setup))
            self.assertTrue(changed, "The between-stage context mutation was not exercised")
            self.assertEqual(parsed_changed, [], "Changed metadata was parsed before its saved pin")

    @unittest.skipUnless(sys.platform == "linux", "Linux collection reuse requires inotify")
    def test_snapshot_collection_bounds_shared_component_reads(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots = self.collection_fixture(root)
            with patch.object(optimizer, "canonical_artifact_roots", return_value=roots), \
                    patch.object(optimizer, "private_search_roots", return_value=roots), \
                    patch.object(optimizer, "standard_library_root", return_value=None):
                expected = optimizer.snapshot_dependency_identities(setup, tools, setup_pin=optimizer.file_pin(setup))
                original = Path.lstat
                calls = 0

                def lstat(path: Path, **keywords: object) -> os.stat_result:
                    nonlocal calls
                    calls += 1
                    return original(path, **keywords)

                with patch.object(Path, "lstat", autospec=True, side_effect=lstat):
                    actual = optimizer.snapshot_dependency_identities(setup, tools, setup_pin=optimizer.file_pin(setup))
                self.assertEqual(actual, expected)
                self.assertGreater(len(actual), 128)
                self.assertIn(roots[0] / "Empty/nested", actual)
                self.assertIn(roots[1] / "nested", actual)
                self.assertLess(calls, 12 * 128, "Readonly collection repeats ancestor lstat calls")

    @unittest.skipUnless(sys.platform == "linux", "Linux collection reuse requires inotify")
    def test_snapshot_collection_rejects_component_changes_before_return(self) -> None:
        for changed_component in ("directory", "artifact"):
            with self.subTest(component=changed_component), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, setup, roots = self.collection_fixture(root)
                original_identity = optimizer.path_component_identity
                original_inventory = optimizer.private_fallback_artifact_paths
                changed = False
                selected = roots[0] if changed_component == "directory" else roots[0] / "Fixture/Deep/M0.olean"

                def identity(path: Path, **keywords: object) -> optimizer.SourceIdentity:
                    result = original_identity(path, **keywords)
                    if changed and path == selected:
                        return (result[0], result[1] + 1, *result[2:])
                    return result

                def inventory(*arguments: object, **keywords: object) -> tuple[str, ...]:
                    nonlocal changed
                    result = original_inventory(*arguments, **keywords)
                    changed = True  # Mocked identity change; no filesystem mutation.
                    return result

                with patch.object(optimizer, "canonical_artifact_roots", return_value=roots), \
                        patch.object(optimizer, "private_search_roots", return_value=roots), \
                        patch.object(optimizer, "standard_library_root", return_value=None), \
                        patch.object(optimizer, "path_component_identity", side_effect=identity), \
                        patch.object(optimizer, "private_fallback_artifact_paths", side_effect=inventory):
                    with self.assertRaisesRegex(ValueError, "collection input path identity changed"):
                        optimizer.snapshot_dependency_identities(setup, tools, setup_pin=optimizer.file_pin(setup))

    @unittest.skipUnless(sys.platform == "linux", "Linux collection reuse requires inotify")
    def test_snapshot_collection_reads_fresh_identities_between_calls(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, setup, roots = self.collection_fixture(root)
            artifact = roots[0] / "Fixture/Deep/M0.olean"
            with patch.object(optimizer, "canonical_artifact_roots", return_value=roots), \
                    patch.object(optimizer, "private_search_roots", return_value=roots), \
                    patch.object(optimizer, "standard_library_root", return_value=None):
                before = optimizer.snapshot_dependency_identities(setup, tools, setup_pin=optimizer.file_pin(setup))
                artifact.write_bytes(b"Changed artifact after the first collection\n")
                after = optimizer.snapshot_dependency_identities(setup, tools, setup_pin=optimizer.file_pin(setup))
                self.assertNotEqual(before[artifact], after[artifact])
                self.assertEqual(after[artifact], optimizer.path_component_identity(artifact))

    def test_inventory_filters_use_genuine_resolution_for_canonical_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            canonical = root / "library"
            artifact = canonical / "Fixture/Local.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"Canonical inventory fixture\n")
            output = root / "output"
            generated = output / "Generated.olean"
            generated.parent.mkdir()
            generated.write_bytes(b"Mutable output fixture\n")
            (artifact.parent / "Linked.olean").symlink_to(generated)
            tools = optimizer.Tools(root, output, root / "lake", root / "lean", root, {}, 5)
            metadata = {"importArts": {"Fixture.Local": [[str(artifact)], []]}}
            original = Path.resolve
            calls = []

            def resolve(path, *arguments, **keywords):
                frame = sys._getframe(1)
                while frame is not None and frame.f_code.co_filename != optimizer.__file__:
                    frame = frame.f_back
                caller = frame.f_code.co_name if frame is not None else ""
                if path == artifact and caller in {
                        "in_output", "namespace_artifact_paths", "canonical_namespace_artifact_paths",
                        "resolve_inventory_path"}:
                    calls.append(caller)
                return original(path, *arguments, **keywords)

            with patch.object(optimizer, "canonical_artifact_roots", return_value=[canonical]), \
                    patch.object(optimizer, "private_search_roots", return_value=[canonical]), \
                    patch.object(Path, "resolve", autospec=True, side_effect=resolve):
                self.assertEqual(optimizer.private_fallback_artifact_paths(tools, metadata),
                                 (str(artifact),))
            self.assertGreater(len(calls), 1, calls)

    def test_inventory_resolution_keeps_aliases_on_genuine_resolver(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            artifact = root / "Local.olean"
            artifact.write_bytes(b"Canonical resolution fixture\n")
            alias = root / "Alias.olean"
            alias.symlink_to(artifact)
            original = Path.resolve
            calls = []

            def resolve(path, *arguments, **keywords):
                calls.append(path)
                return original(path, *arguments, **keywords)

            with patch.object(Path, "resolve", autospec=True, side_effect=resolve):
                for path in (artifact, artifact, alias, alias):
                    self.assertEqual(optimizer.resolve_inventory_path(path), artifact)
                self.assertEqual(calls.count(artifact), 2)
                self.assertEqual(calls.count(alias), 2)
                self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                self.assertEqual(calls.count(artifact), 3)

    @unittest.skipUnless(sys.platform == "linux", "Linux alias guards require inotify")
    def test_inventory_resolution_observes_and_rejects_restored_parent_alias(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            parent = root / "package"
            parent.mkdir()
            artifact = parent / "Local.olean"
            artifact.write_bytes(b"Canonical resolution fixture\n")
            shadow = root / "shadow"
            shadow.mkdir()
            shadow_artifact = shadow / "Local.olean"
            shadow_artifact.write_bytes(b"Aliased resolution fixture\n")
            retained = root / "retained"
            with self.assertRaisesRegex(ValueError, "Compilation input path identity changed"):
                with optimizer.guarded_inventory_components({artifact}, inventory_roots=[parent]):
                    self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                    parent.rename(retained)
                    try:
                        parent.symlink_to(shadow, target_is_directory=True)
                        self.assertEqual(optimizer.resolve_inventory_path(artifact), shadow_artifact)
                    finally:
                        if parent.is_symlink():
                            parent.unlink()
                        retained.rename(parent)
                    self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)

    def test_inventory_resolution_remains_genuine_at_output_and_child_boundaries(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            artifact = root / "Local.olean"
            artifact.write_bytes(b"Canonical resolution fixture\n")
            tools = optimizer.Tools(root, root / "output", root / "lake", root / "lean", root, {}, 5)
            original = Path.resolve
            calls = []

            def resolve(path, *arguments, **keywords):
                calls.append(path)
                return original(path, *arguments, **keywords)

            with patch.object(Path, "resolve", autospec=True, side_effect=resolve), \
                    patch.object(optimizer, "run_command", return_value={"exit_code": 0}) as child:
                self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                optimizer.write_json(root / "output/receipt.json", {"actual_test_output": True})
                self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                tools.run(["explicitly-mocked-child"], root / "output/child")
                self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                self.assertEqual(calls.count(artifact), 4)
                self.assertEqual(child.call_count, 1)

    def test_inventory_resolution_remains_genuine_after_guard_exception(self) -> None:
        platforms = ("linux", "darwin") if sys.platform == "linux" else (sys.platform,)
        for platform in platforms:
            with self.subTest(platform=platform), tempfile.TemporaryDirectory() as directory:
                artifact = Path(directory).resolve() / "Local.olean"
                artifact.write_bytes(b"Canonical resolution fixture\n")
                original = Path.resolve
                calls = []

                def resolve(path, *arguments, **keywords):
                    calls.append(path)
                    return original(path, *arguments, **keywords)

                with patch.object(optimizer.sys, "platform", platform), \
                        patch.object(Path, "resolve", autospec=True, side_effect=resolve):
                    with self.assertRaisesRegex(RuntimeError, "explicit phase failure"):
                        with optimizer.guarded_inventory_components({artifact}):
                            self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                            raise RuntimeError("explicit phase failure")
                    guarded_calls = calls.count(artifact)
                    self.assertEqual(guarded_calls, 1 if platform == "linux" else 2)
                    self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                    self.assertEqual(calls.count(artifact), guarded_calls + 1)
                    self.assertEqual(optimizer.resolve_inventory_path(artifact), artifact)
                    self.assertEqual(calls.count(artifact), guarded_calls + 2)

    def test_inventory_output_filters_do_not_search_ancestors(self) -> None:
        for surface in ("standard", "namespace", "selected", "canonical"):
            with self.subTest(surface=surface), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                canonical = root / "library"
                namespace = canonical / "Fixture"
                output = namespace / "output"
                kept = [namespace / "Local.olean", namespace / "output-sibling/Keep.olean"]
                excluded = output / "Generated.olean"
                for path in [*kept, excluded]:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b"Inventory output filter fixture\n")
                empty = namespace / "empty"
                empty.mkdir()
                (namespace / "Linked.olean").symlink_to(excluded)
                tools = optimizer.Tools(root, output, root / "lake", root / "lean", root, {}, 5)
                metadata = {"importArts": {"Fixture.Local": [[str(kept[0])], []]}}
                with patch.object(optimizer, "canonical_artifact_roots", return_value=[canonical]), \
                        patch.object(optimizer, "private_search_roots", return_value=[canonical]), \
                        patch.object(Path, "is_relative_to", side_effect=AssertionError(
                            "Resolved inventory paths already have their output-prefix components")):
                    if surface == "standard":
                        paths = optimizer.standard_library_paths(namespace, tools)
                    elif surface == "namespace":
                        paths = optimizer.namespace_artifact_paths(namespace, tools)
                    elif surface == "selected":
                        paths = optimizer.selected_root_artifact_paths(metadata, root, tools)
                    else:
                        paths = optimizer.canonical_namespace_artifact_paths(root, None, tools)
                self.assertEqual(set(paths), {str(path) for path in kept})
                self.assertIn(empty, tools.library_inventories[namespace][1])

    def test_standard_library_output_root_has_no_input_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            output = root / "output"
            output.mkdir()
            (output / "Generated.olean").write_bytes(b"Mutable output fixture\n")
            tools = optimizer.Tools(root, output, root / "lake", root / "lean", root, {}, 5)
            self.assertEqual(optimizer.standard_library_paths(output, tools), ())

    @unittest.skipUnless(sys.platform == "linux", "Linux path guards require inotify")
    def test_path_guard_uses_known_lexical_parents(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            artifact = root / "package" / "namespace" / "module.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"Path guard input\n")
            identities = optimizer.path_component_identities({artifact})
            self.assertIn(root, identities)
            with patch.object(Path, "relative_to", side_effect=AssertionError(
                    "Known lexical parents do not need a second ancestor search")):
                with optimizer.guard_path_component_moves(identities):
                    self.assertEqual(artifact.read_bytes(), b"Path guard input\n")

    def test_snapshot_inventory_roots_reuses_combined_public_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            package = root / "package"
            artifact = package / "Fixture/A.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"Root selection fixture\n")
            setup = root / "setup.json"
            metadata = {"importArts": {"Fixture.A": [[str(artifact)], []]}}
            optimizer.write_json(setup, metadata)
            value = {"importArts": {"Fixture.A": [[str(artifact), str(artifact) + ".private"], []]},
                     "snapshot_compilations": {"A.lean": {"setup": optimizer.file_pin(setup)}}}
            with patch.object(optimizer, "canonical_artifact_roots", return_value=[]), \
                    patch.object(optimizer, "standard_library_root", return_value=None):
                tools = optimizer.Tools(root, root / "output", root / "lake", root / "lean", root, {}, 5)
                with patch.object(optimizer, "private_inventory_roots", wraps=optimizer.private_inventory_roots) as calls:
                    self.assertEqual(optimizer.snapshot_private_inventory_roots(tools, value), [package])
                    self.assertEqual(calls.call_count, 1)

    def test_snapshot_inventory_roots_keeps_different_context_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            packages = [root / "combined", root / "context"]
            artifacts = [package / "Fixture/A.olean" for package in packages]
            for artifact in artifacts:
                artifact.parent.mkdir(parents=True)
                artifact.write_bytes(b"Root selection fixture\n")
            setup = root / "setup.json"
            optimizer.write_json(setup, {"importArts": {"Fixture.A": [[str(artifacts[1])], []]}})
            value = {"importArts": {"Fixture.A": [[str(artifacts[0])], []]},
                     "snapshot_compilations": {"A.lean": {"setup": optimizer.file_pin(setup)}}}
            with patch.object(optimizer, "canonical_artifact_roots", return_value=[]), \
                    patch.object(optimizer, "standard_library_root", return_value=None):
                tools = optimizer.Tools(root, root / "output", root / "lake", root / "lean", root, {}, 5)
                self.assertEqual(optimizer.snapshot_private_inventory_roots(tools, value), packages)

    def test_snapshot_inventory_roots_rechecks_public_artifacts_on_fresh_call(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            packages = [root / "combined", root / "context"]
            artifacts = [package / "Fixture/A.olean" for package in packages]
            for artifact in artifacts:
                artifact.parent.mkdir(parents=True)
                artifact.write_bytes(b"Root selection fixture\n")
            contexts = [{"importArts": {"Fixture.A": [[str(artifact)], []]}} for artifact in artifacts]
            setup = root / "setup.json"
            optimizer.write_json(setup, contexts[0])
            value = {"importArts": contexts[0]["importArts"],
                     "snapshot_compilations": {"A.lean": {"setup": optimizer.file_pin(setup)}}}
            with patch.object(optimizer, "canonical_artifact_roots", return_value=[]), \
                    patch.object(optimizer, "standard_library_root", return_value=None):
                tools = optimizer.Tools(root, root / "output", root / "lake", root / "lean", root, {}, 5)
                self.assertEqual(optimizer.snapshot_private_inventory_roots(tools, value), [packages[0]])
                optimizer.write_json(setup, contexts[1])
                value["snapshot_compilations"]["A.lean"]["setup"] = optimizer.file_pin(setup)
                self.assertEqual(optimizer.snapshot_private_inventory_roots(tools, value), packages)

    def capture(self, root: Path, batch: bool, defect: str | None = None,
                phase: str = "snapshot", part: str = ".olean", *,
                real_child: bool = False, plugin_form: str = "null") -> tuple[dict[str, object], dict[str, object]]:
        if defect == "shared_parent":
            root = root / "shared"
            root.mkdir()
        recovery.main_inputs(root, ("A",))
        canonical = root / "dependencies"
        module, dependency = native_sibling(canonical)
        original = dependency.read_bytes()
        prefix = dependency.with_suffix("")
        for suffix in (".olean.server", ".olean.private", ".ir.sig", ".ir"):
            Path(str(prefix) + suffix).write_bytes(original)
        if defect == "missing_pair":
            Path(str(prefix) + part).unlink()
        dynlib, plugin = root / "fixture.so", root / "fixture-plugin.so"
        dynlib.write_bytes(b"Explicitly mocked dynamic library\n")
        plugin.write_bytes(b"Explicitly mocked plugin\n")
        plugin_input = str(plugin) if plugin_form == "string" else {
            "path": str(plugin), "initFn": "fixture_init" if plugin_form == "explicit" else None}
        metadata = {"name": "A", "isModule": True, "imports": None,
                    "importArts": {module: [[str(dependency)], []]},
                    "dynlibs": [str(dynlib)], "plugins": [plugin_input]}
        link = root / "dependency-link"
        if defect == "parent_link":
            link.symlink_to(canonical, target_is_directory=True)
            metadata["importArts"][module] = [[str(link / dependency.relative_to(canonical))], []]
        setup = root / ".lake/build/ir/A.setup.json"
        optimizer.write_json(setup, metadata)
        shadow = root / "shadow"
        _, shadow_part = native_sibling(shadow)
        shadow_part.write_bytes(original[:-1] + bytes([original[-1] ^ 1]))
        if defect == "shared_parent":
            replacement = root.parent / "replacement"
            _, replacement_part = native_sibling(replacement / "dependencies")
            replacement_part.write_bytes(shadow_part.read_bytes())
        tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                                root, {"LEAN_PATH": str(shadow) + os.pathsep + str(canonical)}, 5,
                                time_binary=root / "bin/time")
        arm = tools.output / "arm"
        calls: list[str] = []
        observed: list[Path] = []
        if real_child:
            tools.lean.write_text(f"#!{sys.executable}\n" + """import hashlib, json, pathlib, sys
args = sys.argv[1:]
if '--deps' in args:
    print(pathlib.Path(args[-1]).parent / 'artifacts/A.olean')
else:
    setup = json.loads(pathlib.Path(args[args.index('--run') + 2]).read_text())
    target = pathlib.Path(setup['importArts']['A'][0][0])
    dependency = next(parts[0][0] for module, parts in setup['importArts'].items() if module != 'A')
    declaration = {'name': 'A.x', 'level_params': [], 'kind': 'definition', 'type': 'Nat',
                   'value': hashlib.sha256(pathlib.Path(dependency).read_bytes()).hexdigest(),
                   'is_unsafe': False, 'is_partial': False, 'is_exported': True,
                   'is_private_name': False, 'axioms': []}
    row = {'module': 'A', 'resolved_olean': str(target), 'uses_module_system': True,
           'declarations': [declaration], 'declaration_count': 1,
           'loaded_modules': list(setup['importArts']), 'loaded_module_count': len(setup['importArts'])}
    if pathlib.Path(args[args.index('--run') + 1]).name == 'declarations_batch.lean':
        row.update(batch_modules=['A'], batch_module_count=1, loaded_modules_scope='whole_batch')
    print(json.dumps(row))
""")
            tools.lean.chmod(0o755)

        def mutate() -> None:
            if defect in ("unrelated_sibling", "unrelated_sibling_attributes"):
                sibling = root.parent / ("unrelated-" + phase)
                sibling.mkdir()
                if defect == "unrelated_sibling_attributes":
                    mode = sibling.stat().st_mode & 0o7777
                    sibling.chmod(mode ^ 0o020)
                    sibling.chmod(mode)
                return
            if defect == "directory_attribute":
                before = canonical.stat()
                if part == "chmod":
                    mode = before.st_mode & 0o7777
                    canonical.chmod(mode ^ 0o020)
                    canonical.chmod(mode)
                else:
                    os.chown(canonical, before.st_uid, before.st_gid)
                after = canonical.stat()
                self.assertEqual((after.st_ino, after.st_mode, after.st_uid, after.st_gid),
                                 (before.st_ino, before.st_mode, before.st_uid, before.st_gid))
                self.assertNotEqual(after.st_ctime_ns, before.st_ctime_ns)
                self.assertEqual(dependency.read_bytes(), original)
                return
            if defect == "unwatchable_ancestor":
                ancestor = root.parent
                retained = ancestor.parent / "retained"
                before = ancestor.stat()
                ancestor.rename(retained)
                retained.rename(ancestor)
                self.assertEqual(ancestor.stat().st_ino, before.st_ino)
                self.assertEqual(dependency.read_bytes(), original)
                observed.append(ancestor)
                return
            if defect == "dependency":
                selected = dynlib if part == "dynlib" else plugin if part == "plugin" else Path(str(prefix) + part)
            elif defect == "target":
                selected = arm / "artifacts/A.c"
            elif defect == "parent_link":
                link.unlink()
                link.symlink_to(shadow, target_is_directory=True)
                observed.append(link / dependency.relative_to(canonical))
                self.assertNotEqual(observed[-1].read_bytes(), original)
                link.unlink()
                link.symlink_to(canonical, target_is_directory=True)
                return
            elif defect == "shared_parent":
                retained = root.parent / "retained"
                root.rename(retained)
                root.symlink_to(replacement, target_is_directory=True)
                observed.append(dependency)
                self.assertNotEqual(dependency.read_bytes(), original)
                root.unlink()
                retained.rename(root)
                self.assertEqual(dependency.read_bytes(), original)
                return
            else:
                return
            before, raw = selected.stat(), selected.read_bytes()
            selected.write_bytes(raw + b"Transient bytes consumed during a mocked native child\n")
            observed.append(selected)
            self.assertNotEqual(selected.read_bytes(), raw)
            selected.write_bytes(raw)
            os.utime(selected, ns=(before.st_atime_ns, before.st_mtime_ns))
            self.assertEqual(selected.read_bytes(), raw)
            self.assertEqual(selected.stat().st_mtime_ns, before.st_mtime_ns)

        def external(argv: list[str], label: Path,
                     environment: dict[str, str] | None = None) -> dict[str, object]:
            if argv[0] == str(tools.time_binary):
                calls.append("compile")
                outputs.physical_parts(arm / "artifacts", Path("A.lean"))
                Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
                command = recovery.mock_compile_command(tools, argv, label)
                if phase == "compile":
                    mutate()
                return command
            current = "deps" if "--deps" in argv else "snapshot"
            calls.append(current)
            self.assertIsNotNone(environment)
            if real_child:
                command = optimizer.run_command(argv, tools.root, label, environment, tools.timeout)
                optimizer.require_success(command)
                self.assertEqual(optimizer.read_json(Path(str(label) + ".json")), command)
                self.assertTrue(Path(str(label) + ".stderr").is_file())
                print(json.dumps({"fixture": "real_python_snapshot_child", "phase": current,
                                  "command": command, "stdout": Path(str(label) + ".stdout").read_text()}))
                return command
            expected = arm / "artifacts/A.olean"
            if current == "deps":
                Path(str(label) + ".stdout").write_text(str(expected) + "\n")
            else:
                arguments = argv[argv.index("--run") + 2:]
                if arguments and Path(arguments[0]).suffix == ".json":
                    snapshot_setup = optimizer.read_json(Path(arguments[0]))
                    loaded = Path(snapshot_setup["importArts"][module][0][0])
                    self.assertEqual(snapshot_setup["importArts"]["A"][0][0], str(expected))
                    self.assertNotIn(str(shadow), environment["LEAN_PATH"].split(os.pathsep))
                else:
                    loaded = shadow_part
                snapshot = recovery.SavedSnapshotRecoveryTests.snapshot("A", expected)
                snapshot["declarations"][0]["value"] = optimizer.sha256(loaded)
                snapshot.update(loaded_modules=["A", module], loaded_module_count=2)
                if batch:
                    snapshot.update(batch_modules=["A"], batch_module_count=1,
                                    loaded_modules_scope="whole_batch")
                Path(str(label) + ".stdout").write_text(json.dumps(snapshot) + "\n")
            if current == phase:
                mutate()
            return {"exit_code": 0, "timed_out": False, "remaining_group_killed": False,
                    "external_lean_helper_mock": True}

        with patch.object(optimizer.Tools, "run", side_effect=external):
            compilation = optimizer.compile_arm(tools, Path("A.lean"), setup, arm)
            if defect == "manifest_missing":
                del compilation["input_manifest"]
            elif defect == "manifest_empty":
                compilation["input_manifest"] = {}
            elif defect == "manifest_files_empty":
                manifest = tools.output / "empty-inputs.json"
                optimizer.write_json(manifest, {"files": []})
                compilation["input_manifest"] = optimizer.file_pin(manifest)
            if batch:
                snapshot = optimizer.snapshot_batch(tools, [{"path": "A.lean", "module": "A"}],
                                                    arm / "artifacts", arm, {"A.lean": compilation})["A"]
            else:
                snapshot = optimizer.snapshot_arm(tools, "A", Path("A.lean"), arm, compilation)
        self.assertEqual(calls, ["compile", "deps", "snapshot"])
        self.assertEqual(snapshot["declaration_count"], 1)
        self.assertEqual(snapshot["loaded_module_count"], 2)
        if defect in ("dependency", "target", "parent_link", "shared_parent"):
            self.assertEqual(len(observed), 1)
        return snapshot, compilation

    def test_snapshot_uses_compile_dependency_instead_of_ambient_shadow(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                snapshot, compilation = self.capture(root, batch)
                module = next(iter(optimizer.read_json(Path(compilation["setup"]["path"]))["importArts"]))
                dependency = root / "dependencies" / Path(*module.split(".")).with_suffix(".olean")
                self.assertEqual(snapshot["declarations"][0]["value"], optimizer.sha256(dependency))

    @unittest.skipUnless(sys.platform == "linux", "Linux sibling guards require inotify")
    def test_compile_and_snapshot_accept_unrelated_ancestor_siblings(self) -> None:
        for batch in (False, True):
            for phase in ("compile", "deps", "snapshot"):
                for defect in ("unrelated_sibling", "unrelated_sibling_attributes"):
                    with self.subTest(batch=batch, phase=phase, defect=defect), \
                            tempfile.TemporaryDirectory() as directory:
                        root = Path(directory).resolve() / "fixture"
                        root.mkdir()
                        snapshot, compilation = self.capture(root, batch, defect, phase)
                        self.assertTrue((root.parent / ("unrelated-" + phase)).is_dir())
                        module = next(iter(optimizer.read_json(Path(compilation["setup"]["path"]))["importArts"]))
                        dependency = root / "dependencies" / Path(*module.split(".")).with_suffix(".olean")
                        self.assertEqual(snapshot["declarations"][0]["value"], optimizer.sha256(dependency))

    @unittest.skipUnless(sys.platform == "linux", "Linux directory attribute guards require inotify")
    def test_compile_and_snapshot_reject_restored_directory_attributes(self) -> None:
        for batch in (False, True):
            for phase in ("compile", "deps", "snapshot"):
                for part in ("chmod", "chown"):
                    with self.subTest(batch=batch, phase=phase, part=part), \
                            tempfile.TemporaryDirectory() as directory:
                        with self.assertRaisesRegex(ValueError, "Compilation input path identity changed"):
                            self.capture(Path(directory).resolve(), batch, "directory_attribute", phase, part)

    @unittest.skipUnless(sys.platform == "linux", "Linux directory watches require inotify")
    def test_compile_and_snapshot_fallback_for_execute_only_ancestors(self) -> None:
        for batch in (False, True):
            for phase in ("compile", "deps", "snapshot"):
                for moved in (False, True):
                    with self.subTest(batch=batch, phase=phase, moved=moved), \
                            tempfile.TemporaryDirectory() as directory:
                        ancestor = Path(directory).resolve() / "traverse"
                        root = ancestor / "fixture"
                        root.mkdir(parents=True)
                        ancestor.chmod(0o111)
                        try:
                            if os.access(ancestor, os.R_OK):
                                self.skipTest("Process retains directory read access despite mode 0111")
                            self.assertTrue(os.access(ancestor, os.X_OK))
                            with self.assertRaises(PermissionError):
                                list(ancestor.iterdir())
                            if moved:
                                with self.assertRaisesRegex(ValueError, "[Cc]ompil.*input path identity changed"):
                                    self.capture(root, batch, "unwatchable_ancestor", phase)
                            else:
                                snapshot, _ = self.capture(root, batch)
                                self.assertEqual(snapshot["declaration_count"], 1)
                        finally:
                            ancestor.chmod(0o700)

    def test_nonlinux_keeps_strict_ancestor_stamps_without_inotify(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                with recovery.isolated_ancestor_metadata(Path(directory).resolve()), \
                        patch.object(optimizer.sys, "platform", "darwin"), \
                        patch.object(optimizer.ctypes, "CDLL", side_effect=AssertionError("Non-Linux must not use inotify")):
                    root = Path(directory).resolve() / "clean"
                    root.mkdir()
                    snapshot, _ = self.capture(root, batch)
                    self.assertEqual(snapshot["declaration_count"], 1)
                    root = Path(directory).resolve() / "changed"
                    root.mkdir()
                    with self.assertRaisesRegex(ValueError, "input (?:path )?identity changed"):
                        self.capture(root, batch, "unrelated_sibling", "snapshot")

    def test_compile_pins_full_private_and_ir_dependency_prefix(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            _, compilation = self.capture(root, False)
            files = optimizer.read_json(Path(compilation["input_manifest"]["path"]))["files"]
            actual = {Path(row["path"]).name for row in files}
            self.assertTrue({"Statement" + suffix for suffix in
                             (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")}.issubset(actual))

    def test_compile_rejects_missing_private_or_ir_dependency_parts(self) -> None:
        for part in (".olean.server", ".olean.private", ".ir"):
            with self.subTest(part=part), tempfile.TemporaryDirectory() as directory:
                with self.assertRaisesRegex(ValueError, "Snapshot.*artifact"):
                    self.capture(Path(directory).resolve(), False, "missing_pair", part=part)

    def test_saved_snapshot_requires_exact_target_input_proofs(self) -> None:
        for defect in ("manifest", "setup", "both", "extra_context"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                result, attempt = recovery.SavedSnapshotRecoveryTests.evidence(root)
                with patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]):
                    recovery.verify_saved_fixture(result, root)
                    for arm in ("baseline", "candidate"):
                        if defect in ("manifest", "both"):
                            del result[arm]["snapshot_input_manifest"]
                        if defect in ("setup", "both"):
                            del result[arm]["snapshot_setup"]
                        if defect == "extra_context":
                            setup = Path(result[arm]["snapshot_setup"]["path"])
                            value = optimizer.read_json(setup)
                            contexts = value["snapshot_compilations"]
                            contexts["unused.lean"] = dict(contexts["A.lean"])
                            tools = recovery.saved_fixture_tools(root)
                            value = optimizer.snapshot_setup_value(tools, Path(result[arm]["artifact_root"]),
                                                                   contexts, "batch")
                            changed = attempt / (arm + "-extra-context.json")
                            optimizer.write_json(changed, value)
                            result[arm]["snapshot_setup"] = optimizer.file_pin(changed)
                            filename = "owned-before.json" if arm == "baseline" else "owned-after.json"
                            snapshot = optimizer.read_json(attempt / filename)
                            snapshot.update(batch_modules=["A", "A"], batch_module_count=2,
                                            loaded_modules_scope="whole_batch")
                            optimizer.write_json(attempt / filename, snapshot)
                            result["owned_before_sha256" if arm == "baseline" else "owned_after_sha256"] = optimizer.sha256(attempt / filename)
                    with self.assertRaisesRegex(ValueError, "receipt|inputs"):
                        recovery.verify_saved_fixture(result, root)

    def test_snapshot_bookkeeping_accepts_real_clean_child_output(self) -> None:
        for batch in (False, True):
            with self.subTest(batch=batch), tempfile.TemporaryDirectory() as directory:
                snapshot, _ = self.capture(Path(directory).resolve(), batch, real_child=True)
                self.assertEqual(snapshot["declaration_count"], 1)

    def test_snapshot_setup_preserves_official_plugin_json_forms(self) -> None:
        for plugin_form in ("string", "null", "explicit"):
            with self.subTest(plugin_form=plugin_form), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                _, compilation = self.capture(root, False, plugin_form=plugin_form)
                value = optimizer.read_json(Path(compilation["snapshot_setup"]["path"]))
                expected = str(root / "fixture-plugin.so") if plugin_form == "string" else {
                    "path": str(root / "fixture-plugin.so"),
                    "initFn": "fixture_init" if plugin_form == "explicit" else None}
                self.assertEqual(value["plugins"], [expected])

    def test_snapshot_setup_supplies_required_module_loader_fields(self) -> None:
        for batch in (False, True):
            with tempfile.TemporaryDirectory() as directory:
                _, compilation = self.capture(Path(directory).resolve(), batch)
                value = optimizer.read_json(Path(compilation["snapshot_setup"]["path"]))
                for field in ("isModule", "options"):
                    with self.subTest(batch=batch, field=field):
                        self.assertIn(field, value)
                        if field == "isModule":
                            self.assertIs(value[field], False)
                        else:
                            self.assertEqual(value[field], {})

    def test_snapshot_rejects_transient_dependency_changes_in_both_children(self) -> None:
        for batch in (False, True):
            for phase in ("deps", "snapshot"):
                for part in (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir", "dynlib", "plugin"):
                    with self.subTest(batch=batch, phase=phase, part=part), tempfile.TemporaryDirectory() as directory:
                        with self.assertRaisesRegex(ValueError, "input|snapshot|Snapshot"):
                            self.capture(Path(directory).resolve(), batch, "dependency", phase, part)

    def test_snapshot_rejects_transient_target_changes_in_both_children(self) -> None:
        for batch in (False, True):
            for phase in ("deps", "snapshot"):
                with self.subTest(batch=batch, phase=phase), tempfile.TemporaryDirectory() as directory:
                    with self.assertRaisesRegex(ValueError, "artifacts|snapshot|Snapshot"):
                        self.capture(Path(directory).resolve(), batch, "target", phase)

    def test_snapshot_rejects_missing_or_empty_compile_input_manifest(self) -> None:
        for batch in (False, True):
            for defect in ("manifest_missing", "manifest_empty", "manifest_files_empty"):
                with self.subTest(batch=batch, defect=defect), tempfile.TemporaryDirectory() as directory:
                    with self.assertRaisesRegex(ValueError, "receipt|manifest|input"):
                        self.capture(Path(directory).resolve(), batch, defect)

    def test_snapshot_rejects_transient_parent_symlink_shadow(self) -> None:
        for batch in (False, True):
            for phase in ("deps", "snapshot"):
                with self.subTest(batch=batch, phase=phase), tempfile.TemporaryDirectory() as directory:
                    with self.assertRaisesRegex(ValueError, "input|snapshot|Snapshot"):
                        self.capture(Path(directory).resolve(), batch, "parent_link", phase)

    def test_snapshot_rejects_transient_shared_ancestor_shadow(self) -> None:
        for batch in (False, True):
            for phase in ("deps", "snapshot"):
                with self.subTest(batch=batch, phase=phase), tempfile.TemporaryDirectory() as directory:
                    with self.assertRaisesRegex(ValueError, "input|snapshot|Snapshot"):
                        self.capture(Path(directory).resolve(), batch, "shared_parent", phase)


if __name__ == "__main__":
    unittest.main()
