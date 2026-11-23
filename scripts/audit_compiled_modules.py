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


def unescape_mount_path(path: str) -> str:
    """Undo the octal escapes (`\040` for a space) of /proc/self/mountinfo paths."""
    return re.sub(r'\\([0-7]{3})', lambda match: chr(int(match.group(1), 8)), path)


def cgroup_directories() -> tuple[Path, Path] | None:
    """This process's cgroup v2 directory and the cgroup2 mount point above it; None without one.

    /proc/self/cgroup gives the membership relative to the cgroup namespace, and
    /proc/self/mountinfo which part of the hierarchy the cgroup2 mount shows and
    where. Raises LookupError when a memory cgroup applies but cannot be read
    here: a cgroup v1 memory controller, or a membership the mount does not show.
    """
    try:
        with open('/proc/self/cgroup', encoding='utf-8') as membership:
            lines = membership.read().splitlines()
    except OSError as error:
        if not os.path.isdir('/proc/self'):
            return None  # no procfs (macOS, say): no cgroup to read
        raise LookupError('/proc/self/cgroup cannot be read') from error
    fields = [line.split(':', 2) for line in lines]
    if any(len(field) == 3 and 'memory' in field[1].split(',') for field in fields):
        raise LookupError('a cgroup v1 memory controller applies')
    unified = [field[2] for field in fields if len(field) == 3 and field[0] == '0' and field[1] == '']
    if not unified:
        return None
    member = unified[0]
    try:
        with open('/proc/self/mountinfo', encoding='utf-8') as mounts:
            entries = [line.split() for line in mounts]
    except OSError as error:
        raise LookupError('the cgroup2 mount is unknown') from error
    for entry in entries:
        if '-' not in entry:
            continue
        separator = entry.index('-')
        if separator < 5 or len(entry) <= separator + 1 or entry[separator + 1] != 'cgroup2':
            continue
        root, mount = unescape_mount_path(entry[3]).rstrip('/'), Path(unescape_mount_path(entry[4]))
        if member == root or member.startswith(root + '/'):
            return mount / member[len(root):].lstrip('/'), mount
    raise LookupError('the cgroup2 mount does not show this process\'s cgroup')


def cgroup_headroom() -> int | None:
    """Memory this process's cgroup v2 and its visible ancestors still allow, if any limits it.

    None when no cgroup limit applies; 0 when one may apply but cannot be read
    (an unreadable or malformed memory interface file, a missing cgroup directory).
    A level without memory.max has no memory controller and sets no limit.
    """
    try:
        found = cgroup_directories()
    except LookupError:
        return 0
    if found is None:
        return None
    group, mount = found
    if not group.is_dir():
        return 0
    headroom = None
    while True:
        try:
            limit = (group / 'memory.max').read_text(encoding='ascii').strip()
        except FileNotFoundError:
            limit = 'max'  # no memory controller at this level
        except OSError:
            return 0
        if limit != 'max':
            try:
                left = int(limit) - cgroup_usage(group)
            except (OSError, ValueError):
                return 0
            headroom = left if headroom is None else min(headroom, left)
        if group == mount or group.parent == group:
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
    return available if headroom is None else max(0, min(available, headroom))


def worker_count(groups: int) -> int:
    """How many initial groups run at once: ATLAS_AUDIT_WORKERS, else what memory holds."""
    value = os.environ.get(WORKERS_VARIABLE, '').strip()
    if value:
        if not re.fullmatch(r'[0-9]{1,4}', value, re.ASCII) or int(value) < 1:
            raise AuditFailure(f'{WORKERS_VARIABLE} must be an integer from 1 to 9999, not {value!r}')
        workers = int(value)
    else:
        available = available_memory()
        workers = 1 if available is None else available // BATCH_MEMORY
        cores = len(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else os.cpu_count()
        workers = min(workers, cores or 1)
    return max(1, min(workers, groups))


UNSAMPLED = object()  # Admission.start has not read the available memory yet


class SkippedGroup(AuditFailure):
    """A group not started because an earlier group failed or the audit was cancelled."""


class Admission:
    """Decides when a Lean batch of an initial group may start.

    A batch of group i does not start once a group before i has failed, nor
    after the audit is cancelled; earlier groups keep running, so the first
    failing group is always found. Batches waiting to start do so in group
    order. Each running batch reserves BATCH_MEMORY: a
    new one starts while none runs, or while the available memory covers the
    running batches' reservations and its own (when the available memory is
    unknown, an explicit ATLAS_AUDIT_WORKERS count applies as given). The worker
    count is sized once; this keeps parallel batches from starting when
    something else on the machine has taken the memory since.
    """

    def __init__(self) -> None:
        self.condition = threading.Condition()
        self.running = 0
        self.next_group = 0
        self.waiting: set[int] = set()
        self.first_failure: int | None = None
        self.cancelled = False

    def blocked(self, index: int) -> bool:
        return self.cancelled or (self.first_failure is not None and index > self.first_failure)

    def start(self, index: int, first: bool) -> None:
        """Wait until a batch of group `index` may start (`first`: the group's first batch).

        Groups start in group order, and waiting batches start lowest group first.
        Memory is sampled without the lock, so that recording a failure or a
        finished batch never waits for it; each decision re-checks them.
        """
        with self.condition:
            self.waiting.add(index)
        try:
            memory: object = UNSAMPLED
            while True:
                with self.condition:
                    if self.blocked(index):
                        raise SkippedGroup('an audit group was skipped without an earlier failure')
                    if index != min(self.waiting) or (first and index != self.next_group):
                        memory = UNSAMPLED
                        self.condition.wait(timeout=5)
                        continue
                    if not self.running or (memory is not UNSAMPLED and (
                            memory is None or memory >= (self.running + 1) * BATCH_MEMORY)):
                        self.running += 1
                        if first:
                            self.next_group += 1
                        return
                    if memory is not UNSAMPLED:
                        # Too little memory: wait for a batch to finish or fail, then sample again.
                        self.condition.wait(timeout=5)
                memory = available_memory()
        finally:
            with self.condition:
                self.waiting.discard(index)
                self.condition.notify_all()

    def finish(self) -> None:
        with self.condition:
            self.running -= 1
            self.condition.notify_all()

    def fail(self, index: int) -> None:
        with self.condition:
            if self.first_failure is None or index < self.first_failure:
                self.first_failure = index
            self.condition.notify_all()

    def cancel(self) -> None:
        with self.condition:
            self.cancelled = True
            self.condition.notify_all()


def audit(root: Path, modules: list[str], checker: str, *, batch_size: int = BATCH_SIZE,
          workers: int | None = None) -> dict:
    """Each assigned module succeeds once, or the whole audit fails.

    Normal Lean imports initialize all environment extensions. Only an import
    name collision may split a group; policy and every other import failure
    remain failures. At most 2*N-G attempts are possible for N modules initially
    placed in G groups, and successful groups never share assigned modules.

    The initial groups are consecutive `batch_size` slices of `modules`, as in a
    sequential run. With more than one worker (`workers`, default `worker_count`)
    they run in parallel, and their results are combined in group order: the
    checked modules, the counts and the progress lines are those of a sequential
    run, and the failure reported is the first failing group's. With one worker
    they run one after another in the calling thread, as before.
    """
    if not modules or len(set(modules)) != len(modules) or batch_size < 1:
        raise AuditFailure('invalid nonempty, unique audit inventory or batch bound')
    if workers is not None and workers < 1:
        raise AuditFailure('invalid audit worker count')
    initial = [modules[offset:offset + batch_size] for offset in range(0, len(modules), batch_size)]
    initial_groups = len(initial)
    count = worker_count(initial_groups) if workers is None else min(workers, initial_groups)
    admission = Admission()

    def check(index: int, batch: list[str], tally: dict, first: bool = False) -> None:
        tally['attempts'] += 1
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='atlas-axioms-',
                                         encoding='utf-8') as driver:
            driver.write(''.join(f'import {module}\n' for module in batch))
            driver.write(checker)
            driver.flush()
            admission.start(index, first)
            try:
                result = subprocess.run(['lake', 'env', 'lean', driver.name], cwd=root,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        text=True, timeout=1200)
                split = result.returncode != 0 and only_import_collision(result.stdout) and len(batch) > 1
                if result.returncode != 0 and not split:
                    admission.fail(index)
            except BaseException:
                admission.fail(index)
                raise
            finally:
                # A failure is recorded before the gate lets a later batch start.
                admission.finish()
        if result.returncode == 0:
            tally['checked'].extend(batch)
            tally['groups'] += 1
            return
        if split:
            tally['splits'] += 1
            middle = len(batch) // 2
            check(index, batch[:middle], tally)
            check(index, batch[middle:], tally)
            return
        raise AuditFailure(result.stdout.rstrip() or f'Lean audit exited {result.returncode}')

    def run_group(index: int, batch: list[str]) -> dict:
        tally = {'checked': [], 'attempts': 0, 'splits': 0, 'groups': 0}
        try:
            check(index, batch, tally, first=True)
        except SkippedGroup:
            raise
        except BaseException:
            admission.fail(index)
            raise
        return tally

    if count > 1:
        # Lake loads, and if needed rewrites, its workspace configuration under a
        # lock it does not wait for, so load it once before the batches run at once.
        warm = subprocess.run(['lake', 'env', 'true'], cwd=root, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True, timeout=1200)
        if warm.returncode != 0:
            raise AuditFailure(warm.stdout.rstrip() or f'lake env exited {warm.returncode}')
    checked = []
    attempts = splits = groups = 0

    def combine(tally: dict) -> None:
        nonlocal attempts, splits, groups
        checked.extend(tally['checked'])
        attempts += tally['attempts']
        splits += tally['splits']
        groups += tally['groups']
        print(f'compiled audit: {len(checked)}/{len(modules)} assigned modules checked', flush=True)

    if count == 1:
        for index, batch in enumerate(initial):
            combine(run_group(index, batch))
    else:
        with ThreadPoolExecutor(max_workers=count) as pool:
            futures = [pool.submit(run_group, index, batch) for index, batch in enumerate(initial)]
            try:
                for future in futures:
                    combine(future.result())
            except BaseException:
                admission.cancel()
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
