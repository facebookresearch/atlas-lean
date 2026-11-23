#!/usr/bin/env python3
"""Audit every project module in bounded, initialized Lean environments."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import threading

ROOTS = ('CSLibExt', 'CSLibExtTest', 'MathlibExt', 'MathlibExtTest',
         'PhyslibExt', 'PhyslibExtTest', 'Domains', 'DomainsTest', 'WantedExt')
BATCH_SIZE = 1024
# Memory allowed per parallel batch. An initial group of 1,024 modules peaks at
# 5-8 GB resident, nearly all of it mapped .olean pages that parallel batches
# share; its own memory is under 1 GB. 6 GiB keeps the 16 GB standard runner at
# two batches. ATLAS_AUDIT_WORKERS overrides the count; 1 runs them one by one.
BATCH_MEMORY = 6 * 2**30
WORKERS_VARIABLE = 'ATLAS_AUDIT_WORKERS'
COLLISION = re.compile(r"^.*:\d+:\d+: error: import [^\n]* failed, environment already contains[^\n]*$")


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


def cgroup_usage(group: Path) -> int:
    """A cgroup's memory use without its inactive file pages, which the kernel reclaims first."""
    current = int((group / 'memory.current').read_text(encoding='ascii'))
    try:
        stat = (group / 'memory.stat').read_text(encoding='ascii').split('\n')
        inactive = next((int(line.split()[1]) for line in stat if line.startswith('inactive_file ')), 0)
    except (OSError, ValueError, IndexError):
        inactive = 0
    return max(0, current - inactive)


def cgroup_headroom() -> int | None:
    """The memory this process's cgroup v2 and its ancestors still allow, if any of them limits it."""
    try:
        with open('/proc/self/cgroup', encoding='utf-8') as membership:
            paths = [line.rstrip('\n').split(':', 2)[2] for line in membership if line.startswith('0::')]
    except (OSError, IndexError):
        return None
    if not paths:
        return None
    headroom = None
    group = Path('/sys/fs/cgroup') / paths[0].lstrip('/')
    while True:
        try:
            limit = (group / 'memory.max').read_text(encoding='ascii').strip()
            if limit != 'max':
                left = int(limit) - cgroup_usage(group)
                headroom = left if headroom is None else min(headroom, left)
        except (OSError, ValueError):
            pass
        if group == Path('/sys/fs/cgroup') or group.parent == group:
            return headroom
        group = group.parent


def available_memory() -> int | None:
    """Bytes new processes can use: MemAvailable, capped by any cgroup limit; None if unknown."""
    try:
        with open('/proc/meminfo', encoding='ascii') as meminfo:
            available = next((int(line.split()[1]) * 1024 for line in meminfo
                              if line.startswith('MemAvailable:')), None)
    except (OSError, ValueError, IndexError):
        return None
    if available is None:
        return None
    headroom = cgroup_headroom()
    return available if headroom is None else min(available, headroom)


def worker_count(groups: int) -> int:
    """How many initial groups run at once: ATLAS_AUDIT_WORKERS, else what memory holds."""
    value = os.environ.get(WORKERS_VARIABLE, '').strip()
    if value:
        if not value.isdigit() or int(value) < 1:
            raise AuditFailure(f'{WORKERS_VARIABLE} must be a positive integer, not {value!r}')
        workers = int(value)
    else:
        available = available_memory()
        workers = 1 if available is None else available // BATCH_MEMORY
        cores = len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else os.cpu_count()
        workers = min(workers, cores or 1)
    return max(1, min(workers, groups))


class MemoryGate:
    """Starts a Lean batch only while no other one runs or BATCH_MEMORY is still available.

    The worker count is sized once; the gate keeps parallel batches from
    starting while something else on the machine has taken the memory since.
    """

    def __init__(self) -> None:
        self.condition = threading.Condition()
        self.running = 0

    def __enter__(self) -> None:
        with self.condition:
            while self.running and (available_memory() or 0) < BATCH_MEMORY:
                self.condition.wait(timeout=5)
            self.running += 1

    def __exit__(self, *_: object) -> None:
        with self.condition:
            self.running -= 1
            self.condition.notify_all()


def audit(root: Path, modules: list[str], checker: str, *, batch_size: int = BATCH_SIZE,
          workers: int | None = None) -> dict:
    """Each assigned module succeeds once, or the whole audit fails.

    Normal Lean imports initialize all environment extensions. Only an import
    name collision may split a group; policy and every other import failure
    remain failures. At most 2*N-G attempts are possible for N modules initially
    placed in G groups, and successful groups never share assigned modules.

    The initial groups are consecutive `batch_size` slices of `modules`, as in a
    sequential run. They may run in parallel (`workers`, default `worker_count`),
    but their results are combined in group order: the checked modules, the
    counts and the progress lines are those of a sequential run, and a failure
    reported is the first failing group's.
    """
    if not modules or len(set(modules)) != len(modules) or batch_size < 1:
        raise AuditFailure('invalid nonempty, unique audit inventory or batch bound')
    if workers is not None and workers < 1:
        raise AuditFailure('invalid audit worker count')
    gate = MemoryGate()

    def check(batch: list[str], tally: dict) -> None:
        tally['attempts'] += 1
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='atlas-axioms-',
                                         encoding='utf-8') as driver:
            driver.write(''.join(f'import {module}\n' for module in batch))
            driver.write(checker)
            driver.flush()
            with gate:
                result = subprocess.run(['lake', 'env', 'lean', driver.name], cwd=root,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        text=True, timeout=1200)
        if result.returncode == 0:
            tally['checked'].extend(batch)
            tally['groups'] += 1
            return
        if only_import_collision(result.stdout) and len(batch) > 1:
            tally['splits'] += 1
            middle = len(batch) // 2
            check(batch[:middle], tally)
            check(batch[middle:], tally)
            return
        raise AuditFailure(result.stdout.rstrip() or f'Lean audit exited {result.returncode}')

    stop = threading.Event()

    def run_group(batch: list[str]) -> dict | None:
        # After a failure, groups that have not started are skipped; groups that
        # have started finish, so the first failing group can still be found.
        if stop.is_set():
            return None
        tally = {'checked': [], 'attempts': 0, 'splits': 0, 'groups': 0}
        try:
            check(batch, tally)
        except BaseException:
            stop.set()
            raise
        return tally

    initial = [modules[offset:offset + batch_size] for offset in range(0, len(modules), batch_size)]
    initial_groups = len(initial)
    count = worker_count(initial_groups) if workers is None else min(workers, initial_groups)
    checked = []
    attempts = splits = groups = 0
    with ThreadPoolExecutor(max_workers=count) as pool:
        futures = [pool.submit(run_group, batch) for batch in initial]
        try:
            for future in futures:
                tally = future.result()
                if tally is None:
                    raise AuditFailure('an audit group was skipped without an earlier failure')
                checked.extend(tally['checked'])
                attempts += tally['attempts']
                splits += tally['splits']
                groups += tally['groups']
                print(f'compiled audit: {len(checked)}/{len(modules)} assigned modules checked', flush=True)
        except BaseException:
            for pending in futures:
                pending.cancel()
            raise
    if checked != modules or len(set(checked)) != len(modules):
        raise AuditFailure('successful audit groups differ from the complete assigned inventory')
    return {'modules': len(modules), 'batchSize': batch_size, 'initialGroups': initial_groups,
            'successfulGroups': groups, 'importCollisionSplits': splits, 'attempts': attempts,
            'maximumAttempts': 2 * len(modules) - initial_groups, 'workers': count,
            'checkedModules': checked}


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    try:
        result = audit(root, inventory(root), (root / 'scripts/check_axioms.lean').read_text())
    except (AuditFailure, OSError, subprocess.SubprocessError) as error:
        print(f'FAIL [environment]: {error}', flush=True)
        return 1
    summary = {key: value for key, value in result.items() if key != 'checkedModules'}
    print('ATLAS_COMPILED_AUDIT_RESULT ' + json.dumps(summary, sort_keys=True), flush=True)
    print('ok [environment]: compiled libraries satisfy trust and dependency policies.', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
