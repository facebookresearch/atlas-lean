#!/usr/bin/env python3
"""Audit every project module in bounded, initialized Lean environments."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import threading

ROOTS = ('CSLibExt', 'CSLibExtTest', 'MathlibExt', 'MathlibExtTest',
         'PhyslibExt', 'PhyslibExtTest', 'Domains', 'DomainsTest', 'WantedExt')
BATCH_SIZE = 1024
# Memory allowed per parallel batch when the worker count is sized. An initial
# group of 1,024 modules peaks at 5-8 GB resident, nearly all of it mapped .olean
# pages that parallel batches share; its own memory is 0.2-0.3 GB. 6 GiB keeps
# the 16 GB standard runner at two batches. ATLAS_AUDIT_WORKERS overrides the
# count; 1 runs the batches one by one, as before.
BATCH_MEMORY = 6 * 2**30
WORKERS_VARIABLE = 'ATLAS_AUDIT_WORKERS'
# Prints every variable as NAME=value, each ended by a NUL byte. It links only
# libc, so Lake's library path cannot break it, and its output, which holds
# secrets, goes to a private file that no error message quotes.
ENVIRONMENT_COMMAND = ['env', '-0']
BATCH_TIMEOUT = 1200  # seconds for one Lean batch, and for Lake to give its environment
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


def read_kernel_text(path: str | Path) -> str:
    """A /proc or cgroup file's text; undecodable bytes become surrogates instead of errors."""
    with open(path, encoding='utf-8', errors='surrogateescape') as handle:
        return handle.read()


def kernel_number(text: str) -> int:
    """A decimal number as the kernel writes it, in ASCII digits only."""
    if not re.fullmatch(r'[0-9]+', text.strip(), re.ASCII):
        raise ValueError(f'not a kernel number: {text!r}')
    return int(text)


def unescape_mount_path(path: str) -> str:
    """Undo the octal escapes (`\040` for a space) of /proc/self/mountinfo paths."""
    return re.sub(r'\\([0-7]{3})', lambda match: chr(int(match.group(1), 8)), path)


def cgroup_usage(group: Path) -> int:
    """A cgroup's memory use without its inactive file pages, which the kernel reclaims first."""
    current = kernel_number(read_kernel_text(group / 'memory.current'))
    inactive = 0
    try:
        for line in read_kernel_text(group / 'memory.stat').splitlines():
            if line.startswith('inactive_file '):
                inactive = kernel_number(line.split()[1])
    except (OSError, ValueError, IndexError):
        inactive = 0
    return max(0, current - inactive)


def cgroup_limit(group: Path) -> int | None:
    """The tighter of a cgroup's memory.max and memory.high, None if neither is set.

    Past memory.high the kernel throttles the cgroup, past memory.max it kills.
    A missing file means no memory controller at this level.
    """
    limits = []
    for name in ('memory.max', 'memory.high'):
        try:
            value = read_kernel_text(group / name).strip()
        except FileNotFoundError:
            continue
        if value != 'max':
            limits.append(kernel_number(value))
    return min(limits) if limits else None


def visible_headroom(group: Path, mount: Path) -> int | None:
    """The tightest headroom under the limits from `group` up to the mount point `mount`, if any."""
    if not group.is_dir():
        raise FileNotFoundError(group)
    headroom = None
    while True:
        limit = cgroup_limit(group)
        if limit is not None:
            left = limit - cgroup_usage(group)
            headroom = left if headroom is None else min(headroom, left)
        if group == mount or group.parent == group:
            return headroom
        group = group.parent


def cgroup_headroom() -> int | None:
    """Memory this process's cgroup v2 and its visible ancestors still allow, if any limits it.

    The limit at each level is the tighter of memory.max and memory.high.

    /proc/self/cgroup gives the membership relative to the cgroup namespace, and
    /proc/self/mountinfo which part of the hierarchy each cgroup2 mount shows and
    where; every mount that shows the membership is read, and the tightest
    limit wins. None when no cgroup limit applies (no procfs, or no cgroup v2
    membership). 0 when one may apply but cannot be read: a cgroup v1 memory
    controller, a membership no mount shows, a missing or unreadable cgroup
    directory or interface file, or a malformed number. A level without
    memory.max and memory.high has no memory controller and sets no limit.
    """
    try:
        try:
            lines = read_kernel_text('/proc/self/cgroup').splitlines()
        except FileNotFoundError:
            if not os.path.isdir('/proc/self'):
                return None  # no procfs (macOS, say): no cgroup to read
            raise
        fields = [line.split(':', 2) for line in lines]
        if any(len(field) == 3 and 'memory' in field[1].split(',') for field in fields):
            return 0  # a cgroup v1 memory controller, whose limits are not read here
        unified = [field[2] for field in fields if len(field) == 3 and field[0] == '0' and field[1] == '']
        if not unified:
            return None
        member = unified[0]
        views = []
        for line in read_kernel_text('/proc/self/mountinfo').splitlines():
            entry = line.split()
            if '-' not in entry:
                continue
            separator = entry.index('-')
            if separator < 5 or len(entry) <= separator + 1 or entry[separator + 1] != 'cgroup2':
                continue
            root, mount = unescape_mount_path(entry[3]).rstrip('/'), Path(unescape_mount_path(entry[4]))
            if member == root or member.startswith(root + '/'):
                views.append((mount / member[len(root):].lstrip('/'), mount))
        if not views:
            return 0
        headroom = None
        for group, mount in views:
            left = visible_headroom(group, mount)
            if left is not None:
                headroom = left if headroom is None else min(headroom, left)
        return headroom
    except (OSError, ValueError, UnicodeError, IndexError):
        return 0


def available_memory() -> int | None:
    """Bytes new processes can use: MemAvailable, capped by any cgroup limit; None if unknown."""
    try:
        available = None
        for line in read_kernel_text('/proc/meminfo').splitlines():
            if line.startswith('MemAvailable:'):
                available = kernel_number(line.split()[1]) * 1024
                break
    except (OSError, ValueError, IndexError):
        return None
    if available is None:
        return None
    headroom = cgroup_headroom()
    return available if headroom is None else max(0, min(available, headroom))


def worker_count(groups: int) -> int:
    """How many initial groups run at once: ATLAS_AUDIT_WORKERS, else what memory holds.

    Sized once, from the memory available when the audit starts, at BATCH_MEMORY
    per batch although a batch's own memory is a few hundred MB: that margin is
    what leaves room for other work on the machine.
    """
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


def lean_environment(root: Path) -> tuple[str, dict[str, str]]:
    """The Lean executable and the environment that `lake env` runs commands with in `root`.

    Resolved once per audit: Lake then loads, and if need be rewrites, its
    workspace configuration once, under a lock it does not wait for, and each
    batch's process is Lean itself, which a timeout or an abort stops.
    """
    with tempfile.TemporaryFile() as capture:
        result = subprocess.run(['lake', 'env', *ENVIRONMENT_COMMAND], cwd=root, stdout=capture,
                                stderr=subprocess.PIPE, timeout=BATCH_TIMEOUT)
        if result.returncode != 0:
            message = result.stderr.decode('utf-8', 'replace').rstrip()
            raise AuditFailure(message or f'lake env exited {result.returncode}')
        capture.seek(0)
        listing = capture.read()
    environment = {}
    for entry in listing.split(b'\0'):
        if entry:
            name, equals, value = entry.partition(b'=')
            if not equals or not name:
                raise AuditFailure('lake env gave a malformed environment')
            environment[os.fsdecode(name)] = os.fsdecode(value)
    lean = environment.get('LEAN')
    if not lean and environment.get('PATH'):
        lean = shutil.which('lean', path=environment['PATH'])
    if not lean:
        raise AuditFailure('lake env names no Lean executable')
    return lean, environment


def launch_lean(command: list[str], root: Path, environment: dict[str, str]) -> subprocess.Popen:
    return subprocess.Popen(command, cwd=root, env=environment, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)


def stop(process: subprocess.Popen) -> None:
    try:
        process.kill()
    except OSError:
        pass


class SkippedGroup(AuditFailure):
    """A group not admitted because an earlier group failed or the audit was cancelled."""


class Admission:
    """Decides when a Lean batch of an initial group starts, and stops batches no longer needed.

    Groups start in group order. Once a group fails, no batch of a later group
    starts and the running ones are stopped, while earlier groups keep running,
    so the first failing group is always found. After a cancellation no batch
    starts and every running one is stopped. How many batches run at once is
    the worker pool's size.
    """

    def __init__(self) -> None:
        self.condition = threading.Condition()
        self.next_group = 0
        self.first_failure: int | None = None
        self.cancelled = False
        self.running: dict[subprocess.Popen, int] = {}

    def blocked(self, index: int) -> bool:
        return self.cancelled or (self.first_failure is not None and index > self.first_failure)

    def launch(self, index: int, first: bool, start) -> subprocess.Popen:
        """Start a batch of group `index` with `start()` once allowed (`first`: the group's first batch).

        The process starts under the lock, so a failure or a cancellation
        recorded meanwhile either prevents it or sees it and stops it.
        """
        with self.condition:
            while True:
                if self.blocked(index):
                    raise SkippedGroup('an audit group was skipped without an earlier failure')
                if not first or index == self.next_group:
                    process = start()
                    self.running[process] = index
                    if first:
                        self.next_group += 1
                    self.condition.notify_all()
                    return process
                self.condition.wait(timeout=5)

    def finished(self, process: subprocess.Popen) -> None:
        with self.condition:
            self.running.pop(process, None)

    def fail(self, index: int) -> None:
        with self.condition:
            if self.first_failure is None or index < self.first_failure:
                self.first_failure = index
            for process, group in list(self.running.items()):
                if group > self.first_failure:
                    stop(process)
            self.condition.notify_all()

    def cancel(self) -> None:
        with self.condition:
            self.cancelled = True
            for process in list(self.running):
                stop(process)
            self.condition.notify_all()


def audit(root: Path, modules: list[str], checker: str, *, batch_size: int = BATCH_SIZE,
          workers: int | None = None) -> dict:
    """Each assigned module succeeds once, or the whole audit fails.

    Normal Lean imports initialize all environment extensions. Only an import
    name collision may split a group; policy and every other import failure
    remain failures. At most 2*N-G attempts are possible for N modules initially
    placed in G groups, and successful groups never share assigned modules.

    The initial groups are consecutive `batch_size` slices of `modules`, as in a
    sequential run. Each batch runs Lean in the environment of `lake env`,
    resolved once. With more than one worker (`workers`, default `worker_count`)
    the groups run in parallel, and their results are combined in group order:
    the checked modules, the counts and the progress lines are those of a
    sequential run, and the failure reported is the first failing group's. With
    one worker they run one after another in the calling thread, as before.
    """
    if not modules or len(set(modules)) != len(modules) or batch_size < 1:
        raise AuditFailure('invalid nonempty, unique audit inventory or batch bound')
    if workers is not None and workers < 1:
        raise AuditFailure('invalid audit worker count')
    initial = [modules[offset:offset + batch_size] for offset in range(0, len(modules), batch_size)]
    initial_groups = len(initial)
    count = worker_count(initial_groups) if workers is None else min(workers, initial_groups)
    lean, environment = lean_environment(root)
    admission = Admission()

    def check(index: int, batch: list[str], tally: dict, first: bool = False) -> None:
        tally['attempts'] += 1
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='atlas-axioms-',
                                         encoding='utf-8') as driver:
            driver.write(''.join(f'import {module}\n' for module in batch))
            driver.write(checker)
            driver.flush()
            process = admission.launch(index, first, lambda: launch_lean([lean, driver.name], root, environment))
            try:
                output, _ = process.communicate(timeout=BATCH_TIMEOUT)
            except BaseException:  # a timeout, or an interrupt in a sequential run
                stop(process)
                process.communicate()
                raise
            finally:
                admission.finished(process)
        if process.returncode == 0:
            tally['checked'].extend(batch)
            tally['groups'] += 1
            return
        if only_import_collision(output) and len(batch) > 1:
            tally['splits'] += 1
            middle = len(batch) // 2
            check(index, batch[:middle], tally)
            check(index, batch[middle:], tally)
            return
        raise AuditFailure(output.rstrip() or f'Lean audit exited {process.returncode}')

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
        futures = []
        with ThreadPoolExecutor(max_workers=count) as pool:
            try:
                for index, batch in enumerate(initial):
                    futures.append(pool.submit(run_group, index, batch))
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
