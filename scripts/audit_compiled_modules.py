#!/usr/bin/env python3
"""Audit every project module in bounded, initialized Lean environments.

With ATLAS_AUDIT_RESTORED=FILE, written by `--record FILE` right after CI
restores a build that passed this audit under the same policy, only modules
whose .olean is missing, new or rewritten since are audited. Lake rebuilds a
module whenever its source or what it needs from its imports changes, and
anything else such a module reaches changed in a rebuilt module.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOTS = ('CSLibExt', 'CSLibExtTest', 'MathlibExt', 'MathlibExtTest',
         'PhyslibExt', 'PhyslibExtTest', 'Domains', 'DomainsTest', 'WantedExt')
BATCH_SIZE = 1024
COLLISION = re.compile(r"^.*:\d+:\d+: error: import [^\n]* failed, environment already contains[^\n]*$")
OLEANS = Path('.lake/build/lib/lean')


def only_import_collision(output: str) -> bool:
    errors = [line for line in output.splitlines() if ': error: ' in line]
    return len(errors) == 1 and COLLISION.fullmatch(errors[0]) is not None


class AuditFailure(RuntimeError):
    pass


def inventory(root: Path) -> list[str]:
    modules = []
    for library in ROOTS:
        if not (root / library).is_dir() or (root / library).is_symlink():
            raise AuditFailure(f'audited library directory is missing or symlinked: {library}')
        for path in sorted((root / library).rglob('*.lean')):
            if path.is_symlink():
                raise AuditFailure(f'audited source is symlinked: {path}')
            module = path.relative_to(root).as_posix().removesuffix('.lean').replace('/', '.')
            if any(character in module for character in ('\n', '\r', '\0')):
                raise AuditFailure(f'audited module name contains a line break: {path}')
            modules.append(module)
    if len(set(modules)) != len(modules):
        raise AuditFailure('audited source paths have duplicated module names')
    if not modules:
        raise AuditFailure('the audited source inventory is empty')
    return modules


def compiled(root: Path) -> dict[str, list[int]]:
    """Each compiled module's .olean, identified by its inode, size and timestamps."""
    result = {}
    for path in (root / OLEANS).rglob('*.olean'):
        status = path.stat()
        result[path.relative_to(root / OLEANS).as_posix()] = [
            status.st_ino, status.st_size, status.st_mtime_ns, status.st_ctime_ns]
    return result


def rebuilt(root: Path, modules: list[str], restored: dict[str, list[int]]) -> list[str]:
    """The modules whose .olean is missing, new or rewritten since `restored`."""
    current = compiled(root)
    rewritten = []
    for module in modules:
        olean = module.replace('.', '/') + '.olean'
        if olean not in current or current[olean] != restored.get(olean):
            rewritten.append(module)
    return rewritten


def audit(root: Path, modules: list[str], checker: str, *, batch_size: int = BATCH_SIZE) -> dict:
    """Each assigned module succeeds once, or the whole audit fails.

    Normal Lean imports initialize all environment extensions. Only an import
    name collision may split a group; policy and every other import failure
    remain failures. At most 2*N-G attempts are possible for N modules initially
    placed in G groups, and successful groups never share assigned modules.
    """
    if not modules or len(set(modules)) != len(modules) or batch_size < 1:
        raise AuditFailure('invalid nonempty, unique audit inventory or batch bound')
    checked = []
    attempts = 0
    splits = 0
    groups = 0

    def check(batch: list[str]) -> None:
        nonlocal attempts, splits, groups
        attempts += 1
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='atlas-axioms-',
                                         encoding='utf-8') as driver:
            driver.write(''.join(f'import {module}\n' for module in batch))
            driver.write(checker)
            driver.flush()
            result = subprocess.run(['lake', 'env', 'lean', driver.name], cwd=root,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, timeout=1200)
        if result.returncode == 0:
            checked.extend(batch)
            groups += 1
            return
        if only_import_collision(result.stdout) and len(batch) > 1:
            splits += 1
            middle = len(batch) // 2
            check(batch[:middle])
            check(batch[middle:])
            return
        raise AuditFailure(result.stdout.rstrip() or f'Lean audit exited {result.returncode}')

    initial_groups = (len(modules) + batch_size - 1) // batch_size
    for offset in range(0, len(modules), batch_size):
        check(modules[offset:offset + batch_size])
        print(f'compiled audit: {len(checked)}/{len(modules)} assigned modules checked', flush=True)
    if checked != modules or len(set(checked)) != len(modules):
        raise AuditFailure('successful audit groups differ from the complete assigned inventory')
    return {'modules': len(modules), 'batchSize': batch_size, 'initialGroups': initial_groups,
            'successfulGroups': groups, 'importCollisionSplits': splits, 'attempts': attempts,
            'maximumAttempts': 2 * len(modules) - initial_groups,
            'checkedModules': checked}


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    if sys.argv[1:2] == ['--record'] and len(sys.argv) == 3:
        Path(sys.argv[2]).write_text(json.dumps(compiled(root)), encoding='utf-8')
        return 0
    try:
        modules = inventory(root)
        restored = os.environ.get('ATLAS_AUDIT_RESTORED')
        if restored:
            modules = rebuilt(root, modules, json.loads(Path(restored).read_text(encoding='utf-8')))
            print(f'compiled audit: {len(modules)} modules rebuilt since the restored build', flush=True)
        checker = (root / 'scripts/check_axioms.lean').read_text()
        result = audit(root, modules, checker) if modules else {'modules': 0}
    except (AuditFailure, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f'FAIL [environment]: {error}', flush=True)
        return 1
    summary = {key: value for key, value in result.items() if key != 'checkedModules'}
    print('ATLAS_COMPILED_AUDIT_RESULT ' + json.dumps(summary, sort_keys=True), flush=True)
    print('ok [environment]: compiled libraries satisfy trust and dependency policies.', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
