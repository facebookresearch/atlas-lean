# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Combine official declaration-owner suggestions with native source-reference owners."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

Json = dict[str, Any]
ROLES = {'source', 'ilean', 'native_header', 'compiler_prefix', 'owner_proposal'}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def unique_object(pairs: list[tuple[str, Any]]) -> Json:
    result: Json = {}
    for name, value in pairs:
        require(name not in result, 'Duplicate JSON key: ' + name)
        result[name] = value
    return result


def parse_json(data: bytes | str) -> Any:
    return json.loads(data, object_pairs_hook=unique_object)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_file(pin: Json, base: Path, label: str) -> bytes:
    path = base / pin['path']
    require(path.is_file() and not path.is_symlink(), 'Missing regular input: ' + label)
    before = path.stat()
    data = path.read_bytes()
    after = path.stat()
    identity = lambda value: (value.st_dev, value.st_ino, value.st_ctime_ns,
                              value.st_mtime_ns, value.st_size, value.st_mode)
    require(identity(before) == identity(after), 'Input changed during read: ' + label)
    require(type(pin['bytes']) is int and len(data) == pin['bytes'] > 0 and digest(data) == pin['sha256'],
            'Input checksum differs: ' + label)
    return data


def checked_inputs(seed: Json, base: Path) -> dict[str, bytes]:
    require(set(seed['files']) == ROLES, 'Expected exactly five pinned native inputs')
    return {role: checked_file(pin, base, role) for role, pin in seed['files'].items()}


def bind_owner_proposal(prefix: Json, owner_raw: bytes, artifact_file: Path, base: Path) -> Json:
    """Wrap an accepted compiler prefix after the official owner process and artifact guards."""
    require('owner_proposal_evidence' not in prefix, 'Compiler prefix already has owner evidence')
    olean = next(part for part in prefix['artifacts'] if part['path'].endswith('.olean'))
    receipt = {key: olean[key] for key in ('path', 'bytes', 'sha256')}
    artifact = {'path': str(artifact_file), 'bytes': receipt['bytes'], 'sha256': receipt['sha256']}
    checked_file(artifact, base, 'owner compiled olean')
    owner = parse_json(owner_raw)
    require(owner['module'] == prefix['module'] and owner['resolved_olean'] == receipt['path'],
            'Owner proposal artifact identity differs')
    return {**prefix, 'owner_proposal_evidence': {
        'owner_proposal': {'bytes': len(owner_raw), 'sha256': digest(owner_raw)},
        'compiled_olean': receipt, 'artifact_file': artifact}}


def names(value: Any, label: str) -> list[str]:
    require(isinstance(value, list) and all(isinstance(item, str) and item for item in value),
            'Malformed module list: ' + label)
    require(len(value) == len(set(value)), 'Duplicate modules: ' + label)
    return value


def point(source: str, line: Any, column: Any) -> int:
    require(type(line) is int and type(column) is int and line >= 0 and column >= 0, 'Range needs natural coordinates')
    lines = source.split('\n')
    require(line < len(lines), 'Range line is outside source')
    encoded = lines[line].encode('utf-16-le')
    require(column * 2 <= len(encoded), 'Range column is outside source')
    try:
        prefix = encoded[:column * 2].decode('utf-16-le')
    except UnicodeDecodeError as error:
        raise ValueError('Range splits a UTF16 surrogate pair') from error
    return sum(len(item) + 1 for item in lines[:line]) + len(prefix)


def location_excerpt(source: str, location: Any) -> str:
    require(isinstance(location, list) and len(location) in (4, 5), 'Reference location needs four or five fields')
    if len(location) == 5:
        require(isinstance(location[4], str), 'Parent declaration needs a string')
    first, last = point(source, *location[:2]), point(source, *location[2:4])
    require(first <= last, 'Reference range is reversed')
    return source[first:last]


def extract_references(ilean: Json, source: str, module: str, implicit_init: bool) -> tuple[list[str], list[Json]]:
    require(isinstance(ilean['references'], dict) and isinstance(ilean['decls'], dict), 'Malformed reference/declaration maps')
    for name, positions in ilean['decls'].items():
        require(isinstance(name, str) and name and isinstance(positions, list) and len(positions) == 8,
                'Declaration range needs a name and eight coordinates')
        location_excerpt(source, positions[:4])
        location_excerpt(source, positions[4:])
        require(point(source, *positions[:2]) <= point(source, *positions[4:6]) <=
                point(source, *positions[6:8]) <= point(source, *positions[2:4]),
                'Declaration selection is outside its range')
    owners: set[str] = set()
    identifiers: set[tuple[str, str, str]] = set()
    evidence: list[Json] = []
    for raw_key, info in sorted(ilean['references'].items()):
        key = parse_json(raw_key)
        require(isinstance(key, dict) and set(key) in ({'c'}, {'f'}), 'Unknown native reference identifier tag')
        tag = next(iter(key))
        identifier = key[tag]
        field = 'n' if tag == 'c' else 'i'
        require(isinstance(identifier, dict) and set(identifier) == {'m', field} and
                all(isinstance(item, str) and item for item in identifier.values()), 'Malformed native reference identifier')
        owner, name = identifier['m'], identifier[field]
        identity = (tag, owner, name)
        require(identity not in identifiers, 'Duplicate decoded native reference identifier')
        identifiers.add(identity)
        require(isinstance(info, dict) and set(info) == {'definition', 'usages'} and
                isinstance(info['usages'], list), 'Malformed native reference information')
        locations: list[Json] = []
        if info['definition'] is not None:
            locations.append({'role': 'definition', 'range': info['definition'],
                              'source_excerpt': location_excerpt(source, info['definition'])})
        for usage in info['usages']:
            locations.append({'role': 'usage', 'range': usage, 'source_excerpt': location_excerpt(source, usage)})
        reason = ('local_fvar' if tag == 'f' else 'owned_by_target' if owner == module else
                  'implicit_Init' if implicit_init and (owner == 'Init' or owner.startswith('Init.')) else None)
        if reason is None:
            owners.add(owner)
        evidence.append({'native_key': raw_key, 'native_identifier': key, 'kind': 'constant' if tag == 'c' else 'fvar',
                         'module': owner, 'name': name, 'definition': info['definition'], 'usages': info['usages'],
                         'locations': locations, 'included_as_import': reason is None, 'exclusion_reason': reason})
    return sorted(owners), evidence


def suggest(seed: Json, base: Path) -> Json:
    from generate_import_inventory import verify_header

    raw = checked_inputs(seed, base)
    source = raw['source'].decode('utf-8')
    ilean, header, prefix, owner = (parse_json(raw[role]) for role in
                                   ('ilean', 'native_header', 'compiler_prefix', 'owner_proposal'))
    module = seed['module']
    require(isinstance(module, str) and module and ilean['module'] == prefix['module'] == owner['module'] == module,
            'Module identity differs among native inputs')
    relative_source = module.replace('.', '/') + '.lean'
    require(prefix['source_path'] == seed['original_guest_source_path'] and
            prefix['source_path'].endswith('/' + relative_source), 'Original module source path differs')
    source_hash, ilean_hash = digest(raw['source']), digest(raw['ilean'])
    require(prefix['source_sha256'] == header['source_sha256'] == source_hash, 'Source provenance differs')
    require(type(ilean['version']) is int and ilean['version'] == 5, 'Unsupported native Ilean version')
    require(header['status'] == 'parsed' and header['parse_errors'] == [] and header['is_module'] is True and
            type(header['is_prelude']) is bool and header['source_utf8_bytes'] == len(raw['source']) and
            header['relative_path'] == relative_source, 'Native header provenance is invalid')
    require(owner['backend'] == 'ImportGraph.Tools.MinImports' and owner['suggestion_only'] is True and
            owner['uses_module_system'] is True, 'Expected official modern owner proposal')
    compile_command = prefix['compile_command']
    legacy_completion = ('remaining_group_killed' not in compile_command and
                         compile_command['remaining_group_members'] == [])
    modern_completion = (compile_command.get('remaining_group_killed') is False and
                         compile_command['remaining_group_members'] == [])
    require(type(compile_command['exit_code']) is int and compile_command['exit_code'] == 0 and
            compile_command['timed_out'] is False and
            (legacy_completion or modern_completion), 'Original compiler prefix did not pass')
    fields = prefix['native_setup_fields']
    require(fields['name'] == module and fields['isModule'] is True, 'Original native setup name/module flag differs')
    parts = prefix['artifacts']
    require(len(parts) == 7 and len({part['path'] for part in parts}) == 7 and
            all(type(part['bytes']) is int and part['bytes'] > 0 and len(part['sha256']) == 64 for part in parts),
            'Incomplete original seven-part prefix')
    olean = next((part for part in parts if part['path'].endswith('.olean')), None)
    compiled_ilean = next((part for part in parts if part['path'].endswith('.ilean')), None)
    require(olean is not None and compiled_ilean is not None and
            compiled_ilean['bytes'] == len(raw['ilean']) and compiled_ilean['sha256'] == ilean_hash,
            'Ilean does not belong to the pinned original compiler prefix')
    require(owner['resolved_olean'] == olean['path'] and
            olean['path'].endswith('/' + relative_source[:-5] + '.olean') and
            compiled_ilean['path'].endswith('/' + relative_source[:-5] + '.ilean'), 'Original canonical artifact identity differs')
    binding = prefix.get('owner_proposal_evidence')
    require(isinstance(binding, dict) and isinstance(binding.get('owner_proposal'), dict) and
            type(binding['owner_proposal'].get('bytes')) is int and
            binding['owner_proposal']['bytes'] == len(raw['owner_proposal']) and
            binding['owner_proposal'].get('sha256') == digest(raw['owner_proposal']), 'Owner proposal provenance differs')
    receipt = {key: olean[key] for key in ('path', 'bytes', 'sha256')}
    artifact = binding.get('artifact_file')
    require(isinstance(binding.get('compiled_olean'), dict) and
            type(binding['compiled_olean'].get('bytes')) is int and binding['compiled_olean'] == receipt and isinstance(artifact, dict) and
            type(artifact.get('bytes')) is int and artifact['bytes'] == receipt['bytes'] and
            artifact.get('sha256') == receipt['sha256'] and isinstance(artifact.get('path'), str),
            'Owner proposal compiled olean receipt differs')
    checked_file(artifact, base, 'owner compiled olean')
    argv = prefix['actual_compiler']['argv']
    c_part = next((part for part in parts if part['path'].endswith('.c')), None)
    require(c_part is not None and c_part['path'].endswith('/' + relative_source[:-5] + '.c') and
            {part['path'] for part in parts} == {olean['path'][:-6] + suffix for suffix in
                ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig')} | {c_part['path']},
            'Original artifact part names are incomplete')
    for flag, expected in (('-o', olean['path']), ('-i', compiled_ilean['path']), ('-c', c_part['path']),
                           ('--setup', prefix['native_setup']['path'])):
        require(argv.count(flag) == 1 and argv[argv.index(flag) + 1] == expected, 'Observed native compiler artifact/setup differs')
    require(Path(argv[0]).name == 'lean' and argv.count(prefix['source_path']) == 1, 'Observed original native source differs')
    require(isinstance(header['imports'], list) and all(type(item[flag]) is bool for item in header['imports']
            for flag in ('is_exported', 'import_all', 'is_meta')), 'Native header import flags need booleans')
    verify_header(header, raw['source'], Counter())
    direct = [[item['module'], not item['is_exported'], item['import_all'], item['is_meta']] for item in header['imports']]
    require(isinstance(ilean['directImports'], list) and all(isinstance(item, list) and len(item) == 4 and
            isinstance(item[0], str) and item[0] and all(type(flag) is bool for flag in item[1:])
            for item in ilean['directImports']) and
            ilean['directImports'] == direct, 'Native header/import visibility differs from Ilean')
    implicit_init = not header['is_prelude']
    compiled_imports = owner['compiled_direct_imports']
    require(isinstance(compiled_imports, list) and all(isinstance(item, dict) and
            isinstance(item.get('module'), str) and item['module'] and
            all(type(item.get(flag)) is bool for flag in ('is_exported', 'import_all', 'is_meta'))
            for item in compiled_imports), 'Compiled owner import flags need booleans')
    compiled_direct = [[item['module'], not item['is_exported'], item['import_all'], item['is_meta']]
                       for item in compiled_imports]
    init = [['Init', False, False, False], ['Init', False, False, True]] if implicit_init else []
    require(compiled_direct == init + direct, 'Compiled owner imports differ from native header and Ilean')
    reduced = names(owner['required_modules'], 'official reduced owners')
    unreduced = names(owner['unreduced_required_modules'], 'official unreduced owners')
    require(type(owner['required_module_count']) is type(owner['unreduced_required_module_count']) is int and
            owner['required_module_count'] == len(reduced) and owner['unreduced_required_module_count'] == len(unreduced),
            'Official owner proposal count differs')
    owned_names = owner['owned_declaration_names']
    require(isinstance(owned_names, list) and all(isinstance(name, str) and name for name in owned_names) and
            type(owner['owned_declaration_count']) is int and owner['owned_declaration_count'] == len(owned_names) and
            len(set(owned_names)) == owner['owned_declaration_count'], 'Official owner declaration coverage differs')
    references, evidence = extract_references(ilean, source, module, implicit_init)
    require(set(ilean['decls']) <= set(owned_names), 'Ilean declaration names lack owner coverage')
    added = sorted(set(references) - set(unreduced))
    union = sorted(set(unreduced) | set(references))
    boundary = header['body_boundary_byte']
    require(type(boundary) is int and 0 <= boundary <= len(raw['source']), 'Body byte boundary is invalid')
    return {'module': module, 'suggestion_only': True, 'backend': 'native_Ilean_v5_plus_ImportGraph.Tools.MinImports',
            'source_sha256': source_hash, 'source_utf8_bytes': len(raw['source']), 'ilean_sha256': ilean_hash,
            'original_guest_source_path': prefix['source_path'], 'canonical_olean': olean,
            'owner_proposal_evidence': binding,
            'native_setup': prefix['native_setup'], 'native_setup_fields': fields,
            'body_boundary_byte': boundary, 'body_sha256': digest(raw['source'][boundary:]),
            'native_required_modules': reduced, 'native_unreduced_required_modules': unreduced,
            'reference_modules': references, 'reference_module_count': len(references),
            'additional_reference_modules': added, 'additional_reference_module_count': len(added),
            'unreduced_required_modules': union, 'unreduced_required_module_count': len(union),
            'reduced_plus_reference_seeds': sorted(set(reduced) | set(added)),
            'reference_identifier_count': len(evidence), 'native_declaration_range_count': len(ilean['decls']),
            'native_owned_declaration_count': owner['owned_declaration_count'], 'implicit_Init': implicit_init,
            'original_imports': header['imports'], 'reference_evidence': evidence,
            'input_pins': seed['files'], 'candidate_acceptance': 'pending_real_compile_all10_owned_fields_and_consumers',
            'limitations': ['Native references omit canonical/generated syntax and some implicit elaboration state.',
                            'Notation, tactic and instance coverage still requires a real candidate compile.',
                            'Keep original public/private/meta/all modifiers when rendering; this parser does not rewrite source.',
                            'Outer gate must retain source/toolchain/setup and all seven physical artifact receipts.']}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('seeds', type=Path, nargs='+', help='JSONL source-bound seed records')
    args = parser.parse_args()
    seen: set[str] = set()
    for path in args.seeds:
        for line in path.read_bytes().splitlines():
            seed = parse_json(line)
            require(seed['module'] not in seen, 'Duplicate requested module')
            seen.add(seed['module'])
            print(json.dumps(suggest(seed, path.parent), ensure_ascii=False), flush=True)


if __name__ == '__main__':
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    main()
