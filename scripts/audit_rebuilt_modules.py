#!/usr/bin/env python3
"""Audit only the modules that a pull request's build rewrote.

`record FILE REVISION` runs right after CI restores a build that passed the
full audit (audit_compiled_modules.py) at REVISION. It records the .olean of
each module REVISION audited, but only if REVISION has the same
audit_compiled_modules.py, check_axioms.lean and this script. With
ATLAS_AUDIT_RESTORED=FILE, this script then runs, exactly as the full audit runs
them, the full audit's batches that hold or import a module whose .olean is
missing, new, rewritten or unrecorded: modules can also conflict when imported
together. Every other batch loads only modules whose .olean passed at REVISION.
"""
from __future__ import annotations

from collections import defaultdict
import json
import os
from pathlib import Path
import re
import subprocess
import sys

import audit_compiled_modules as full

POLICY = ('scripts/audit_compiled_modules.py', 'scripts/check_axioms.lean', 'scripts/audit_rebuilt_modules.py')
# Generous on purpose: any `import X` in a source, comments included, counts.
IMPORT = re.compile(r"\bimport\s+(?:all\s+)?([\w.'«»!?]+)")
COMMENT = re.compile(r'/-(?:(?!/-|-/).)*-/|--[^\n]*', re.S)


def uncommented(text: str) -> str:
    """The text with Lean comments, nested block comments included, replaced by spaces."""
    while (stripped := COMMENT.sub(' ', text)) != text:
        text = stripped
    return text


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
    try:
        if any(git('show', f'{revision}:{name}') != (root / name).read_bytes() for name in POLICY):
            return None
    except subprocess.CalledProcessError:
        return None
    paths = git('ls-tree', '-r', '-z', '--name-only', revision, '--', *full.ROOTS).decode().split('\0')
    modules = [path.removesuffix('.lean').replace('/', '.') for path in paths if path.endswith('.lean')]
    return {module: status for module in modules if (status := olean(root, module)) is not None}


def importers(root: Path, changed: set[str]) -> set[str]:
    """`changed` and every project module that imports one of them, directly or not."""
    imported_by = defaultdict(set)
    for library in full.ROOTS:
        for path in (root / library).rglob('*.lean'):
            module = path.relative_to(root).as_posix().removesuffix('.lean').replace('/', '.')
            text = path.read_text(encoding='utf-8', errors='replace')
            for target in set(IMPORT.findall(text)) | set(IMPORT.findall(uncommented(text))):
                imported_by[target.replace('«', '').replace('»', '')].add(module)
    affected, pending = set(changed), list(changed)
    while pending:
        for module in imported_by[pending.pop()] - affected:
            affected.add(module)
            pending.append(module)
    return affected


def batches_with(inventory: list[str], rebuilt: set[str], size: int = full.BATCH_SIZE) -> list[str]:
    """The full audit's batches of `inventory` that hold a rebuilt module, in order."""
    batches = (inventory[start:start + size] for start in range(0, len(inventory), size))
    return [module for batch in batches if rebuilt.intersection(batch) for module in batch]


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
        inventory = full.inventory(root)
        rebuilt = {module for module in inventory
                   if olean(root, module) is None or olean(root, module) != restored.get(module)}
        affected = importers(root, rebuilt)
        modules = batches_with(inventory, affected)
        print(f'compiled audit: {len(rebuilt)} modules rebuilt since the restored build, '
              f'{len(affected)} with their importers, {len(modules)} modules in their batches', flush=True)
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
