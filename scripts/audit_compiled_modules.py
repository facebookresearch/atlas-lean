#!/usr/bin/env python3
"""Audit every project module in bounded, initialized Lean environments."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import contextlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

ROOTS = ('CSLibExt', 'CSLibExtTest', 'MathlibExt', 'MathlibExtTest',
         'PhyslibExt', 'PhyslibExtTest', 'Domains', 'DomainsTest', 'WantedExt')
BATCH_SIZE = 1024
# Memory allowed per parallel batch. An initial group of 1,024 modules peaks at
# 5-8 GB resident, nearly all of it mapped .olean pages that parallel batches
# share; its own memory is a few hundred MB. 6 GiB keeps the 16 GB standard
# runner at two batches. ATLAS_AUDIT_WORKERS overrides the count; 1 runs the
# batches one by one, as before.
BATCH_MEMORY = 6 * 2**30
WORKERS_VARIABLE = 'ATLAS_AUDIT_WORKERS'
BATCH_TIMEOUT = 1200  # seconds for one Lean batch, and for Lake to give its environment
SETTLE_SECONDS = 5  # time for a new batch's memory to show in MemAvailable
# On Linux, `lake env env -0` lists the workspace environment, and each batch
# runs its Lean directly. GNU `env` links only libc, so Lake's library path
# cannot break it, and its output, which holds secrets, goes to a private file
# that no error message quotes. Elsewhere `env` may lack `-0` or drop variables
# (macOS strips DYLD_* from protected executables), so each batch runs through
# `lake env lean`, as before, in its own process group.
LIST_ENVIRONMENT = sys.platform.startswith('linux')
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


def read_kernel_bytes(path: str | Path) -> bytes:
    with open(path, 'rb') as handle:
        return handle.read()


def kernel_number(text: bytes) -> int:
    """A decimal number as the kernel writes it, in ASCII digits only."""
    text = text.strip()
    if not re.fullmatch(rb'[0-9]+', text):
        raise ValueError(f'not a kernel number: {text!r}')
    return int(text)


def unescape_mount_path(path: bytes) -> bytes:
    """Undo the octal escapes (`\040` for a space) of /proc/self/mountinfo paths."""
    return re.sub(rb'\\([0-7]{3})', lambda match: bytes([int(match.group(1), 8) & 0xFF]), path)


def cgroup_usage(group: Path) -> int:
    """A cgroup's memory use without its inactive file pages, which the kernel reclaims first."""
    current = kernel_number(read_kernel_bytes(group / 'memory.current'))
    inactive = 0
    try:
        for line in read_kernel_bytes(group / 'memory.stat').split(b'\n'):
            if line.startswith(b'inactive_file '):
                inactive = kernel_number(line.split(b' ')[1])
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
            value = read_kernel_bytes(group / name).strip()
        except FileNotFoundError:
            continue
        if value != b'max':
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
    where; both are read as bytes, one record per LF. Every mount that shows
    the membership is read, and the tightest limit wins. None when no cgroup
    limit applies (no procfs, or no cgroup v2 membership). 0 when one may apply
    but cannot be read: a cgroup v1 memory controller, an ambiguous or
    unresolvable membership, a membership no mount shows, a missing or
    unreadable cgroup directory, memory.max, memory.high or memory.current,
    or a malformed number. An unreadable memory.stat only counts no page as
    reclaimable. A level without memory.max and memory.high has no memory
    controller and sets no limit.
    """
    try:
        try:
            listing = read_kernel_bytes('/proc/self/cgroup')
        except FileNotFoundError:
            if not os.path.isdir('/proc/self'):
                return None  # no procfs (macOS, say): no cgroup to read
            raise
        fields = [line.split(b':', 2) for line in listing.split(b'\n') if line]
        if any(len(field) != 3 for field in fields):
            return 0
        if any(b'memory' in field[1].split(b',') for field in fields):
            return 0  # a cgroup v1 memory controller, whose limits are not read here
        unified = [field[2] for field in fields if field[0] == b'0' and field[1] == b'']
        if not unified:
            return None
        if len(unified) > 1 or not unified[0].startswith(b'/'):
            return 0
        member = unified[0].rstrip(b'/')
        if any(part in (b'.', b'..') for part in member.split(b'/')):
            return 0  # outside the namespace's root, which no mount can show
        views = []
        for line in read_kernel_bytes('/proc/self/mountinfo').split(b'\n'):
            entry = line.split(b' ')
            if b'-' not in entry:
                continue
            separator = entry.index(b'-')
            if separator < 5 or len(entry) <= separator + 1 or entry[separator + 1] != b'cgroup2':
                continue
            root, mount = unescape_mount_path(entry[3]).rstrip(b'/'), unescape_mount_path(entry[4])
            if member == root or member.startswith(root + b'/'):
                mount_point = Path(os.fsdecode(mount))
                relative = os.fsdecode(member[len(root):].lstrip(b'/'))
                views.append((mount_point / relative if relative else mount_point, mount_point))
        if not views:
            return 0
        headroom = None
        for group, mount in views:
            left = visible_headroom(group, mount)
            if left is not None:
                headroom = left if headroom is None else min(headroom, left)
        return headroom
    except (OSError, ValueError, IndexError):
        return 0


def available_memory() -> int | None:
    """Bytes new processes can use: MemAvailable, capped by any cgroup limit; None if unknown."""
    try:
        available = None
        for line in read_kernel_bytes('/proc/meminfo').split(b'\n'):
            if line.startswith(b'MemAvailable:'):
                available = kernel_number(line.split()[1]) * 1024
                break
    except (OSError, ValueError, IndexError):
        return None
    if available is None:
        return None
    headroom = cgroup_headroom()
    return available if headroom is None else max(0, min(available, headroom))


def requested_workers() -> int | None:
    """The ATLAS_AUDIT_WORKERS count, if set."""
    value = os.environ.get(WORKERS_VARIABLE, '').strip()
    if not value:
        return None
    if not re.fullmatch(r'[0-9]{1,4}', value, re.ASCII) or int(value) < 1:
        raise AuditFailure(f'{WORKERS_VARIABLE} must be an integer from 1 to 9999, not {value!r}')
    return int(value)


def worker_count(groups: int) -> int:
    """How many initial groups run at once: ATLAS_AUDIT_WORKERS, else what memory holds.

    Sized from the memory available when the audit starts, at BATCH_MEMORY per
    batch, and at most the usable cores. Admission then rechecks the memory
    before each batch it adds to running ones.
    """
    workers = requested_workers()
    if workers is None:
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
        result = subprocess.run(['lake', 'env', 'env', '-0'], cwd=root, stdout=capture,
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


def prepare_lake(root: Path) -> None:
    """Load Lake's workspace configuration once, before batches run `lake env lean` at once."""
    result = subprocess.run(['lake', 'env', 'true'], cwd=root, stdout=subprocess.DEVNULL,
                            stderr=subprocess.PIPE, timeout=BATCH_TIMEOUT)
    if result.returncode != 0:
        message = result.stderr.decode('utf-8', 'replace').rstrip()
        raise AuditFailure(message or f'lake env exited {result.returncode}')


def launch_lean(command: list[str], root: Path, environment: dict[str, str] | None) -> subprocess.Popen:
    """Start a batch. Through Lake, it gets its own process group, so that stopping it stops Lean."""
    return subprocess.Popen(command, cwd=root, env=environment, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, start_new_session=environment is None)


@contextlib.contextmanager
def termination_interrupts():
    """While the audit runs, SIGTERM and SIGHUP interrupt it as SIGINT does, so its batches are killed.

    Only in the main thread, which alone receives signals, and only for a signal
    still at its default action: one the caller ignores, as `nohup` does SIGHUP,
    stays ignored. The previous handlers come back when the audit ends.
    """
    saved = {}
    if threading.current_thread() is threading.main_thread():
        for name in ('SIGTERM', 'SIGHUP'):
            number = getattr(signal, name, None)
            if number is not None and signal.getsignal(number) is signal.SIG_DFL:
                saved[number] = signal.signal(number, signal.default_int_handler)
    try:
        yield
    finally:
        for number, handler in saved.items():
            signal.signal(number, handler)


class SkippedGroup(AuditFailure):
    """A group not started because an earlier group failed or the audit was cancelled."""


class Admission:
    """Decides when a Lean batch starts, and stops batches no longer needed.

    - Groups start in group order. Once a group fails, no batch of a later
      group starts and the running ones are stopped, while earlier groups keep
      running, so the first failing group is always found. After a
      cancellation no batch starts and every running one is stopped.
    - Processes start and are stopped under one lock, so a stop never misses
      a batch that has just started. On Linux they are signalled through a
      pidfd, which cannot reach a reused process ID.
    - With `gated`, a batch joins running ones only if a memory sample, taken
      without the lock, leaves BATCH_MEMORY for each running batch and for it;
      or leaves BATCH_MEMORY for it and was taken SETTLE_SECONDS after the
      latest batch started, so that batch's memory shows. An unknown reading
      adds nothing. A batch always starts when none runs.
    """

    def __init__(self, gated: bool) -> None:
        self.condition = threading.Condition()
        self.gated = gated
        self.next_group = 0
        self.first_failure: int | None = None
        self.cancelled = False
        self.running: dict[subprocess.Popen, tuple[int, int | None]] = {}  # group, pidfd
        self.latest_start = float('-inf')

    def blocked(self, index: int) -> bool:
        return self.cancelled or (self.first_failure is not None and index > self.first_failure)

    def allows(self, sample: tuple[int | None, float] | None) -> bool:
        if not self.running or not self.gated:
            return True
        if sample is None or sample[0] is None:
            return False
        memory, taken = sample
        if memory >= (len(self.running) + 1) * BATCH_MEMORY:
            return True
        return memory >= BATCH_MEMORY and taken - self.latest_start >= SETTLE_SECONDS

    def launch(self, index: int, first: bool, start) -> subprocess.Popen:
        """Start a batch of group `index` with `start()` once allowed (`first`: the group's first batch)."""
        sample = None
        while True:
            with self.condition:
                if self.blocked(index):
                    raise SkippedGroup('an audit group was skipped without an earlier failure')
                if first and index != self.next_group:
                    sample = None
                    self.condition.wait(timeout=5)
                    continue
                if self.allows(sample):
                    process = start()
                    pidfd = None
                    if hasattr(os, 'pidfd_open') and isinstance(process, subprocess.Popen):
                        try:
                            pidfd = os.pidfd_open(process.pid)
                        except OSError:
                            pidfd = None
                    self.running[process] = (index, pidfd)
                    self.latest_start = time.monotonic()
                    if first:
                        self.next_group += 1
                    self.condition.notify_all()
                    return process
                if sample is not None:
                    self.condition.wait(timeout=self.retry_after(sample))
            sample = (available_memory(), time.monotonic())

    def retry_after(self, sample: tuple[int | None, float]) -> float:
        """Seconds to wait before sampling again: until the latest batch settles, or one."""
        if sample[0] is not None and sample[0] >= BATCH_MEMORY:
            return max(0.01, min(1.0, self.latest_start + SETTLE_SECONDS - time.monotonic()))
        return 1.0

    def stop(self, process: subprocess.Popen) -> None:
        with self.condition:
            self.kill_batch(process)

    def kill_batch(self, process: subprocess.Popen) -> None:
        """SIGKILL a registered batch that has not been reaped. Call with the lock held.

        A batch started through Lake is killed with its process group, so its
        Lean dies too; one started directly, through its pidfd where there is one.
        """
        if process not in self.running or process.returncode is not None:
            return
        _, pidfd = self.running[process]
        try:
            if not LIST_ENVIRONMENT:
                if process.pid > 0:  # never killpg(0) or killpg(-1)
                    os.killpg(process.pid, signal.SIGKILL)
            elif pidfd is not None:
                signal.pidfd_send_signal(pidfd, signal.SIGKILL)
            else:
                process.kill()
        except OSError:
            pass

    def finished(self, process: subprocess.Popen, failed: int | None = None) -> None:
        """Unregister an ended batch; with `failed`, first record that its group failed."""
        with self.condition:
            if failed is not None:
                self.fail(failed)
            _, pidfd = self.running.pop(process, (None, None))
            if pidfd is not None:
                os.close(pidfd)
            self.condition.notify_all()

    def fail(self, index: int) -> None:
        with self.condition:
            if self.first_failure is None or index < self.first_failure:
                self.first_failure = index
            for process, (group, _) in list(self.running.items()):
                if group > self.first_failure:
                    self.kill_batch(process)
            self.condition.notify_all()

    def cancel(self) -> None:
        with self.condition:
            self.cancelled = True
            for process in list(self.running):
                self.kill_batch(process)
            self.condition.notify_all()


def audit(root: Path, modules: list[str], checker: str, *, batch_size: int = BATCH_SIZE,
          workers: int | None = None, memory_gate: bool | None = None) -> dict:
    """Each assigned module succeeds once, or the whole audit fails.

    Normal Lean imports initialize all environment extensions. Only an import
    name collision may split a group; policy and every other import failure
    remain failures. At most 2*N-G attempts are possible for N modules initially
    placed in G groups, and successful groups never share assigned modules.

    The initial groups are consecutive `batch_size` slices of `modules`, as in a
    sequential run. Worker threads run them, `workers` at a time (default
    `worker_count`), and their results are combined in group order: the
    checked modules, the counts and the progress lines are those of a
    sequential run, and the failure reported is the first failing group's.
    With one worker they run one after another. `memory_gate` (default: when
    the count was sized from memory) rechecks the memory before a batch joins
    running ones.
    """
    if not modules or len(set(modules)) != len(modules) or batch_size < 1:
        raise AuditFailure('invalid nonempty, unique audit inventory or batch bound')
    if workers is not None and workers < 1:
        raise AuditFailure('invalid audit worker count')
    initial = [modules[offset:offset + batch_size] for offset in range(0, len(modules), batch_size)]
    initial_groups = len(initial)
    sized = workers is None and requested_workers() is None
    count = worker_count(initial_groups) if workers is None else min(workers, initial_groups)
    if LIST_ENVIRONMENT:
        lean, environment = lean_environment(root)
    else:
        lean, environment = None, None
        if count > 1:
            prepare_lake(root)
    admission = Admission(sized if memory_gate is None else memory_gate)

    def check(index: int, batch: list[str], tally: dict, first: bool = False) -> None:
        tally['attempts'] += 1
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='atlas-axioms-',
                                         encoding='utf-8') as driver:
            driver.write(''.join(f'import {module}\n' for module in batch))
            driver.write(checker)
            driver.flush()
            command = [lean, driver.name] if lean else ['lake', 'env', 'lean', driver.name]
            process = admission.launch(index, first, lambda: launch_lean(command, root, environment))
            try:
                output, _ = process.communicate(timeout=BATCH_TIMEOUT)
            except BaseException:  # a timeout: record the failure and stop the batch at once,
                with admission.condition:  # then reap it and leave its pipe undrained
                    admission.fail(index)
                    admission.kill_batch(process)
                process.wait()
                if process.stdout:
                    process.stdout.close()
                admission.finished(process)
                raise
            # Classify under the admission lock (a reentrant one), so that no batch
            # starts between this batch's end and the record of its group's failure.
            with admission.condition:
                split = process.returncode != 0 and only_import_collision(output) and len(batch) > 1
                admission.finished(process, failed=index if process.returncode != 0 and not split else None)
        if process.returncode == 0:
            tally['checked'].extend(batch)
            tally['groups'] += 1
            return
        if split:
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
    # Only worker threads start Lean, under the admission lock, so an interrupt
    # here, in the coordinating thread, finds each batch either registered, and
    # stops it, or not started, and prevents it.
    futures = []
    with termination_interrupts(), ThreadPoolExecutor(max_workers=count) as pool:
        try:
            for index, batch in enumerate(initial):
                futures.append(pool.submit(run_group, index, batch))
            for future in futures:
                tally = future.result()
                checked.extend(tally['checked'])
                attempts += tally['attempts']
                splits += tally['splits']
                groups += tally['groups']
                print(f'compiled audit: {len(checked)}/{len(modules)} assigned modules checked', flush=True)
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
