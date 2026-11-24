# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Actual saved source-reference case; no Lean or VM is invoked."""

import copy
import hashlib
import json
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from typing import Any, Callable
from unittest.mock import patch

from import_optimizer.reference_imports import bind_owner_proposal, extract_references, location_excerpt, parse_json, suggest

DIRECTORY = Path(__file__).resolve().parent
HELPER = DIRECTORY / 'reference_imports.py'
FIXTURE = DIRECTORY / 'testdata/reference_actual037.tar.gz'
# Recorded native data with relocated path metadata; see testdata/README.md.
FIXTURE_SHA256 = 'c6e9e3c060fd92a9b55cf6aee2127fa80733dad1329a1588f37cc50212424d69'
ADDITIONAL = {
    'Mathlib.Analysis.InnerProductSpace.Defs',
    'Mathlib.MeasureTheory.Constructions.BorelSpace.Basic',
    'Mathlib.Topology.UniformSpace.Cauchy',
    'Mathlib.MeasureTheory.Measure.MeasureSpaceDef',
}


class ReferenceImportsTest(unittest.TestCase):
    root: Path
    seed: dict[str, Any]

    @classmethod
    def setUpClass(cls) -> None:
        temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(temporary.cleanup)
        cls.root = Path(temporary.name).resolve()
        if hashlib.sha256(FIXTURE.read_bytes()).hexdigest() != FIXTURE_SHA256:
            raise ValueError('Saved native fixture archive checksum differs')
        expected = {'case-inputs.jsonl', 'input/Statement.ilean', 'input/header.json',
                    'input/official-owner-proposal.json', 'input/original-compiler-prefix.json',
                    'input/original-source.lean', 'bound-case-inputs.jsonl', 'input/Statement.olean',
                    'input/reference-compiler-prefix.json'}
        with tarfile.open(FIXTURE, 'r:gz') as archive:
            members = archive.getmembers()
            if len(members) != len(expected) or {member.name for member in members} != expected:
                raise ValueError('Saved native fixture archive member set differs')
            for member in members:
                if not member.isfile():
                    raise ValueError('Saved native fixture has a non-regular member')
                destination = cls.root / member.name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(archive.extractfile(member).read())
        cls.seed = json.loads((cls.root / 'bound-case-inputs.jsonl').read_bytes())

    def test_actual_source_binders_add_four_recorded_owners(self) -> None:
        actual = suggest(self.seed, self.root)
        self.assertEqual(len(actual['unreduced_required_modules']), 29)
        self.assertTrue(ADDITIONAL <= set(actual['unreduced_required_modules']))

    def test_actual_native_ranges_and_reduced_starter(self) -> None:
        actual = suggest(self.seed, self.root)
        self.assertEqual(actual['reference_module_count'], 14)
        self.assertEqual(actual['reference_identifier_count'], 22)
        self.assertEqual(actual['native_owned_declaration_count'], 5)
        self.assertEqual(actual['native_declaration_range_count'], 5)
        self.assertEqual(actual['additional_reference_modules'], sorted(ADDITIONAL))
        self.assertEqual(len(actual['reduced_plus_reference_seeds']), 6)
        refs = {row['name']: row for row in actual['reference_evidence']}
        for name, provider in (
                ('InnerProductSpace', 'Mathlib.Analysis.InnerProductSpace.Defs'),
                ('CompleteSpace', 'Mathlib.Topology.UniformSpace.Cauchy'),
                ('BorelSpace', 'Mathlib.MeasureTheory.Constructions.BorelSpace.Basic')):
            self.assertEqual(refs[name]['module'], provider)
            self.assertTrue(refs[name]['included_as_import'])
            self.assertEqual(len(refs[name]['usages'][0]), 4)
            self.assertEqual(refs[name]['locations'][0]['source_excerpt'], name)
        self.assertIn('ℝ', [row['source_excerpt'] for row in refs['Real']['locations']])
        self.assertIn('2', [row['source_excerpt'] for row in refs['Prod.snd']['locations']])
        self.assertEqual(refs['Prod.snd']['exclusion_reason'], 'implicit_Init')
        self.assertEqual(actual['source_sha256'], self.seed['files']['source']['sha256'])
        self.assertEqual(actual['ilean_sha256'], self.seed['files']['ilean']['sha256'])
        self.assertTrue(actual['suggestion_only'])
        self.assertEqual(actual['candidate_acceptance'], 'pending_real_compile_all10_owned_fields_and_consumers')

    def staged(self, root: Path) -> dict[str, Any]:
        seed = copy.deepcopy(self.seed)
        for role, pin in seed['files'].items():
            destination = root / (role + '.input')
            destination.write_bytes((self.root / pin['path']).read_bytes())
            pin['path'] = destination.name
        prefix = json.loads((root / seed['files']['compiler_prefix']['path']).read_bytes())
        artifact = prefix['owner_proposal_evidence']['artifact_file']
        (root / 'original.olean').write_bytes((self.root / artifact['path']).read_bytes())
        artifact['path'] = 'original.olean'
        self.rewrite(seed, root, 'compiler_prefix', json.dumps(prefix).encode())
        return seed

    def rewrite(self, seed: dict[str, Any], root: Path, role: str, data: bytes) -> None:
        pin = seed['files'][role]
        (root / pin['path']).write_bytes(data)
        pin.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())

    def mutate(self, role: str, change: Callable[[Any], None], expected: str,
               rebind_ilean: bool = False, rebind_owner: bool = False) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed = self.staged(root)
            value = json.loads((root / seed['files'][role]['path']).read_bytes())
            change(value)
            self.rewrite(seed, root, role, json.dumps(value).encode())
            if rebind_ilean:
                prefix = json.loads((root / seed['files']['compiler_prefix']['path']).read_bytes())
                part = next(part for part in prefix['artifacts'] if part['path'].endswith('.ilean'))
                part.update(bytes=seed['files']['ilean']['bytes'], sha256=seed['files']['ilean']['sha256'])
                self.rewrite(seed, root, 'compiler_prefix', json.dumps(prefix).encode())
            if rebind_owner:
                prefix = json.loads((root / seed['files']['compiler_prefix']['path']).read_bytes())
                if 'owner_proposal_evidence' in prefix:
                    prefix['owner_proposal_evidence']['owner_proposal'].update(
                        bytes=seed['files']['owner_proposal']['bytes'], sha256=seed['files']['owner_proposal']['sha256'])
                    self.rewrite(seed, root, 'compiler_prefix', json.dumps(prefix).encode())
            with self.assertRaisesRegex(ValueError, expected):
                suggest(seed, root)

    def test_owner_array_digest_refresh_cannot_replace_original_proposal(self) -> None:
        for remove_import in (False, True):
            with self.subTest(remove_compiled_import=remove_import):
                def change(value: dict[str, Any]) -> None:
                    value.update(required_modules=[], required_module_count=0,
                                 unreduced_required_modules=[], unreduced_required_module_count=0)
                    if remove_import:
                        value['compiled_direct_imports'] = [item for item in value['compiled_direct_imports'] if item['module'] != 'Mathlib']
                self.mutate('owner_proposal', change, 'Owner proposal provenance differs')

    def test_owner_compiled_imports_match_native_header_after_rebinding(self) -> None:
        self.mutate('owner_proposal',
                    lambda value: value.update(compiled_direct_imports=[item for item in value['compiled_direct_imports']
                                                                        if item['module'] != 'Mathlib']),
                    'Compiled owner imports differ', rebind_owner=True)

    def test_native_declared_names_are_covered_by_owner_after_rebinding(self) -> None:
        self.mutate('owner_proposal', lambda value: value['owned_declaration_names'].__setitem__(0, 'Different.declaration'),
                    'Ilean declaration names lack owner coverage', rebind_owner=True)

    def test_binding_uses_real_olean_and_keeps_raw_native_records(self) -> None:
        prefix_raw = (self.root / 'input/original-compiler-prefix.json').read_bytes()
        prefix = json.loads(prefix_raw)
        owner_raw = (self.root / self.seed['files']['owner_proposal']['path']).read_bytes()
        bound = bind_owner_proposal(prefix, owner_raw, Path('input/Statement.olean'), self.root)
        expected = json.loads((self.root / self.seed['files']['compiler_prefix']['path']).read_bytes())
        self.assertEqual(bound, expected)
        self.assertNotIn('owner_proposal_evidence', prefix)
        self.assertEqual((self.root / 'input/original-compiler-prefix.json').read_bytes(), prefix_raw)
        with self.assertRaisesRegex(ValueError, 'already has owner evidence'):
            bind_owner_proposal(bound, owner_raw, Path('input/Statement.olean'), self.root)

    def test_owner_binding_rejects_missing_and_mismatched_receipts(self) -> None:
        self.mutate('compiler_prefix', lambda value: value.pop('owner_proposal_evidence'), 'Owner proposal provenance differs')
        self.mutate('compiler_prefix', lambda value: value['owner_proposal_evidence']['owner_proposal'].update(bytes=True),
                    'Owner proposal provenance differs')
        for section, key, changed in [('compiled_olean', 'path', '/different/Statement.olean'),
                                      ('compiled_olean', 'bytes', 1), ('compiled_olean', 'bytes', 36064.0),
                                      ('compiled_olean', 'sha256', '0' * 64),
                                      ('artifact_file', 'bytes', True), ('artifact_file', 'sha256', '0' * 64)]:
            with self.subTest(section=section, key=key):
                self.mutate('compiler_prefix', lambda value: value['owner_proposal_evidence'][section].update({key: changed}),
                            'Owner proposal compiled olean receipt differs')

    def test_bound_olean_bytes_are_checked_beyond_proposal_and_prefix_hashes(self) -> None:
        for change in ('same_size_bytes', 'empty', 'missing', 'symlink'):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                seed = self.staged(root)
                path = root / 'original.olean'
                if change == 'same_size_bytes':
                    data = path.read_bytes()
                    path.write_bytes(bytes([data[0] ^ 1]) + data[1:])
                elif change == 'empty':
                    path.write_bytes(b'')
                else:
                    path.unlink()
                    if change == 'symlink':
                        path.symlink_to(self.root / 'input/Statement.olean')
                expected = 'Input checksum differs' if change in ('same_size_bytes', 'empty') else 'Missing regular input'
                with self.assertRaisesRegex(ValueError, expected + ': owner compiled olean'):
                    suggest(seed, root)

    def test_olean_edit_and_restore_during_read_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed = self.staged(root)
            target = root / 'original.olean'
            original_read = Path.read_bytes
            visits = []
            def edit_and_restore(path: Path) -> bytes:
                data = original_read(path)
                if path == target:
                    visits.append(path)
                    path.write_bytes(b'changed')
                    path.write_bytes(data)
                return data
            with patch.object(Path, 'read_bytes', edit_and_restore):
                with self.assertRaisesRegex(ValueError, 'Input changed during read: owner compiled olean'):
                    suggest(seed, root)
            self.assertEqual(visits, [target])
            self.assertEqual(target.read_bytes(), (self.root / 'input/Statement.olean').read_bytes())

    def test_compiled_import_flags_and_init_are_fully_checked(self) -> None:
        cases = [('non_boolean', lambda value: value['compiled_direct_imports'][-1].update(is_exported=1), 'import flags need booleans'),
                 ('exported', lambda value: value['compiled_direct_imports'][-1].update(is_exported=False), 'imports differ'),
                 ('all', lambda value: value['compiled_direct_imports'][-1].update(import_all=True), 'imports differ'),
                 ('meta', lambda value: value['compiled_direct_imports'][-1].update(is_meta=True), 'imports differ'),
                 ('missing_meta_Init', lambda value: value['compiled_direct_imports'].pop(1), 'imports differ'),
                 ('duplicate_import', lambda value: value['compiled_direct_imports'].append(value['compiled_direct_imports'][-1]), 'imports differ')]
        for label, change, expected in cases:
            with self.subTest(change=label):
                self.mutate('owner_proposal', change, 'Compiled owner ' + expected, rebind_owner=True)

    def test_owner_names_allow_generated_extras_and_reject_malformed_coverage(self) -> None:
        for label, change in [('empty_name', lambda value: value['owned_declaration_names'].__setitem__(0, '')),
                              ('non_string', lambda value: value['owned_declaration_names'].__setitem__(0, 7)),
                              ('duplicate', lambda value: value['owned_declaration_names'].__setitem__(0, value['owned_declaration_names'][1]))]:
            with self.subTest(change=label):
                self.mutate('owner_proposal', change, 'Official owner declaration coverage differs', rebind_owner=True)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed = self.staged(root)
            owner = json.loads((root / seed['files']['owner_proposal']['path']).read_bytes())
            owner['owned_declaration_names'].append('_private.Generated.helper')
            owner['owned_declaration_count'] += 1
            self.rewrite(seed, root, 'owner_proposal', json.dumps(owner).encode())
            prefix = json.loads((root / seed['files']['compiler_prefix']['path']).read_bytes())
            prefix['owner_proposal_evidence']['owner_proposal'].update(
                bytes=seed['files']['owner_proposal']['bytes'], sha256=seed['files']['owner_proposal']['sha256'])
            self.rewrite(seed, root, 'compiler_prefix', json.dumps(prefix).encode())
            result = suggest(seed, root)
            self.assertEqual(result['native_owned_declaration_count'], 6)
            self.assertEqual(result['native_declaration_range_count'], 5)

    def test_source_and_ilean_hashes_are_bound_to_real_prefix(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed = self.staged(root)
            path = root / seed['files']['source']['path']
            path.write_bytes(path.read_bytes().replace(b'InnerProductSpace', b'NoSuchBinderHere_'))
            with self.assertRaisesRegex(ValueError, 'Input checksum differs: source'):
                suggest(seed, root)
        self.mutate('native_header', lambda value: value.update(source_sha256='0' * 64), 'Source provenance differs')
        self.mutate('ilean', lambda value: value.update(decls={}), 'Ilean does not belong')

    def test_schema_corruption_reaches_each_guard_after_hash_rebinding(self) -> None:
        cases = [
            ('version', lambda value: value.update(version=6), 'Unsupported native Ilean version'),
            ('module', lambda value: value.update(module='Different.Statement'), 'Module identity differs'),
            ('numeric_import_flag', lambda value: value.update(directImports=[['Mathlib', 0, False, False]]), 'visibility differs'),
            ('private_import_drift', lambda value: value.update(directImports=[['Mathlib', True, False, False]]), 'visibility differs'),
            ('declaration_coordinate', lambda value: next(iter(value['decls'].values())).__setitem__(0, -1), 'natural coordinates'),
            ('range_past_source', lambda value: next(iter(value['references'].values()))['usages'][0].__setitem__(0, 999), 'outside source'),
            ('bool_coordinate', lambda value: next(iter(value['references'].values()))['usages'][0].__setitem__(0, True), 'natural coordinates'),
            ('parent_decl_type', lambda value: next(iter(value['references'].values()))['usages'][0].__setitem__(4, 5), 'needs a string'),
            ('unknown_identifier_tag', lambda value: value['references'].update({'{"x":{"m":"X","n":"y"}}': {'definition': None, 'usages': []}}), 'identifier tag'),
            ('bad_reference_module', lambda value: value['references'].update({'{"c":{"m":7,"n":"y"}}': {'definition': None, 'usages': []}}), 'Malformed native reference identifier'),
            ('duplicate_decoded_id', lambda value: value['references'].update({json.dumps(json.loads(next(iter(value['references'])))): next(iter(value['references'].values()))}), 'Duplicate decoded'),
        ]
        for label, change, expected in cases:
            with self.subTest(control=label):
                self.mutate('ilean', change, expected, rebind_ilean=True)

    def test_native_header_and_original_compiler_are_positive(self) -> None:
        self.mutate('compiler_prefix', lambda value: value['compile_command'].update(exit_code=37), 'prefix did not pass')
        self.mutate('compiler_prefix', lambda value: value['actual_compiler']['argv'].__setitem__(2, '/different/Statement.lean'), 'native source differs')
        self.mutate('native_header', lambda value: value['imports'][0].update(is_exported=1), 'flags need booleans')
        self.mutate('native_header', lambda value: value.update(status='parse_error'), 'header provenance is invalid')
        self.mutate('owner_proposal', lambda value: value.update(resolved_olean='/different/Statement.olean'), 'artifact identity differs')
        self.mutate('owner_proposal', lambda value: value.update(owned_declaration_count=6), 'declaration coverage differs', rebind_owner=True)

    def test_repinned_native_import_and_token_spans_match_source(self) -> None:
        for label, change in (
                ('import_span', lambda value: value['imports'][0]['source']['span'].update(start_byte=0, end_byte=1)),
                ('token_span', lambda value: value['imports'][0]['source']['tokens'][0]['span'].update(start_byte=0, end_byte=1))):
            with self.subTest(change=label):
                self.mutate('native_header', change, 'Native')

    def test_repinned_native_token_contents_match_source(self) -> None:
        for key in ('text', 'parsed_text'):
            with self.subTest(changed_field=key):
                self.mutate('native_header',
                            lambda value: value['imports'][0]['source']['tokens'][0].update({key: 'OtherPublic'}),
                            'Native')

    def test_repinned_native_body_boundary_matches_header(self) -> None:
        self.mutate('native_header', lambda value: value.update(body_boundary_byte=0), 'header byte boundary')

    def test_empty_reference_maps_and_local_fvars_are_supported_schema_branches(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed = self.staged(root)
            ilean = json.loads((root / seed['files']['ilean']['path']).read_bytes())
            ilean['references']['{"f":{"m":"Local.Other","i":"id42"}}'] = {'definition': None, 'usages': [[40,10,40,11]]}
            self.rewrite(seed, root, 'ilean', json.dumps(ilean).encode())
            prefix = json.loads((root / seed['files']['compiler_prefix']['path']).read_bytes())
            part = next(part for part in prefix['artifacts'] if part['path'].endswith('.ilean'))
            part.update(bytes=seed['files']['ilean']['bytes'], sha256=seed['files']['ilean']['sha256'])
            self.rewrite(seed, root, 'compiler_prefix', json.dumps(prefix).encode())
            value = suggest(seed, root)
            self.assertNotIn('Local.Other', value['reference_modules'])
            self.assertEqual(value['reference_identifier_count'], 23)
            ilean['references'] = {}; ilean['decls'] = {}
            self.rewrite(seed, root, 'ilean', json.dumps(ilean).encode())
            part.update(bytes=seed['files']['ilean']['bytes'], sha256=seed['files']['ilean']['sha256'])
            self.rewrite(seed, root, 'compiler_prefix', json.dumps(prefix).encode())
            value = suggest(seed, root)
            self.assertEqual(value['reference_modules'], [])
            self.assertEqual(value['unreduced_required_module_count'], 25)

    def test_utf16_ranges_use_native_columns_not_python_codepoints(self) -> None:
        self.assertEqual(location_excerpt('😀 InnerProductSpace\n', [0,3,0,20]), 'InnerProductSpace')
        self.assertEqual(location_excerpt('😀 A\nB C\n', [0,3,1,1]), 'A\nB')
        with self.assertRaisesRegex(ValueError, 'surrogate pair'):
            location_excerpt('😀 X\n', [0,1,0,2])
        with self.assertRaisesRegex(ValueError, 'reversed'):
            location_excerpt('abc\n', [0,2,0,1])

    def test_decoder_prefix_boundary_and_duplicate_json_keys(self) -> None:
        ilean = {'decls': {}, 'references': {
            '{"c":{"m":"Initialization.Other","n":"Foo"}}': {'definition': None, 'usages': [[0,0,0,3]]},
            '{"c":{"m":"Init.Prelude","n":"Foo"}}': {'definition': None, 'usages': [[0,0,0,3]]},
        }}
        owners, _ = extract_references(ilean, 'Foo', 'Current.Module', implicit_init=True)
        self.assertEqual(owners, ['Initialization.Other'])
        owners, _ = extract_references(ilean, 'Foo', 'Current.Module', implicit_init=False)
        self.assertEqual(owners, ['Init.Prelude', 'Initialization.Other'])
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
            parse_json('{"version":5,"version":6}')

    def test_duplicate_request_retains_prefix_but_cannot_report_success(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seed = self.staged(root)
            path = root / 'duplicate-seeds.jsonl'
            path.write_text((json.dumps(seed) + '\n') * 2)
            command = [sys.executable, '-B', str(HELPER), str(path)]
            process = subprocess.run(command, capture_output=True)
            self.assertNotEqual(process.returncode, 0)
            self.assertIn(b'Duplicate requested module', process.stderr)
            self.assertEqual(len(process.stdout.splitlines()), 1)

    def test_actual_single_jsonl_cli_result_is_populated(self) -> None:
        command = [sys.executable, '-B', str(HELPER), str(self.root / 'bound-case-inputs.jsonl')]
        process = subprocess.run(command, check=True, capture_output=True)
        rows = process.stdout.splitlines()
        self.assertEqual(len(rows), 1)
        result = json.loads(rows[0])
        self.assertEqual(result['unreduced_required_module_count'], 29)
        self.assertEqual(result['additional_reference_modules'], sorted(ADDITIONAL))
        self.assertEqual(len(result['reference_evidence']), 22)
        self.assertEqual(result['native_owned_declaration_count'], 5)


if __name__ == '__main__':
    unittest.main()
