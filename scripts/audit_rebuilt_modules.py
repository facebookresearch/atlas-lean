#!/usr/bin/env python3
"""Audit only the modules that a pull request's build rewrote.

`record FILE REVISION` runs right after CI restores a build that passed the
full audit (audit_compiled_modules.py) at REVISION. It records the .olean of
each module REVISION audited, but only if REVISION has the same
audit_compiled_modules.py and check_axioms.lean. With ATLAS_AUDIT_RESTORED=FILE,
this script then audits every module whose .olean is missing, new, rewritten or
unrecorded. Lake rebuilds a module whenever its source or what it needs from its
imports changes, so every other module keeps declarations that passed at
REVISION, and anything new it reaches changed in a rebuilt module.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

import audit_compiled_modules as full

POLICY = ('scripts/audit_compiled_modules.py', 'scripts/check_axioms.lean')


def olean(root: Path, module: str) -> list[int] | None:
    """The inode, size and timestamps of a module's .olean, or None if it has none."""
    try:
        status = (root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')).stat()
    except FileNotFoundError:
        return None
    return [status.st_ino, status.st_size, status.st_mtime_ns, status.st_ctime_ns]


def record(root: Path, revision: str) -> dict[str, list[int]] | None:
    """The .olean of each module audited at `revision`, or None if its policy differs."""
    def git(*args: str) -> bytes:
        return subprocess.run(['git', *args], cwd=root, check=True, stdout=subprocess.PIPE).stdout
    if any(git('show', f'{revision}:{name}') != (root / name).read_bytes() for name in POLICY):
        return None
    paths = git('ls-tree', '-r', '-z', '--name-only', revision, '--', *full.ROOTS).decode().split('\0')
    modules = [path.removesuffix('.lean').replace('/', '.') for path in paths if path.endswith('.lean')]
    return {module: status for module in modules if (status := olean(root, module)) is not None}


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    if sys.argv[1:2] == ['record'] and len(sys.argv) == 4:
        restored = record(root, sys.argv[3])
        if restored is None:
            print('The audit policy changed since the restored build; the audit checks every module.')
            return 1
        Path(sys.argv[2]).write_text(json.dumps(restored), encoding='utf-8')
        return 0
    if len(sys.argv) != 1:
        print('usage: audit_rebuilt_modules.py [record FILE REVISION]')
        return 2
    try:
        restored = json.loads(Path(os.environ['ATLAS_AUDIT_RESTORED']).read_text(encoding='utf-8'))
        modules = [module for module in full.inventory(root)
                   if olean(root, module) is None or olean(root, module) != restored.get(module)]
        print(f'compiled audit: {len(modules)} modules rebuilt since the restored build', flush=True)
        checker = (root / 'scripts/check_axioms.lean').read_text()
        result = full.audit(root, modules, checker) if modules else {'modules': 0}
    except (full.AuditFailure, KeyError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f'FAIL [environment]: {error}', flush=True)
        return 1
    summary = {key: value for key, value in result.items() if key != 'checkedModules'}
    print('ATLAS_COMPILED_AUDIT_RESULT ' + json.dumps(summary, sort_keys=True), flush=True)
    print('ok [environment]: rebuilt modules satisfy trust and dependency policies.', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
