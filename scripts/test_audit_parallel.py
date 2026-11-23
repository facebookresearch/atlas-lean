#!/usr/bin/env python3
"""Parallel execution of the compiled audit: same results as a sequential run.

The Lean batches are replaced by a fake `subprocess.run` that reads the driver
file, so these tests need no Lean build.
"""
from __future__ import annotations

import builtins
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_compiled_modules as audit  # noqa: E402

COLLISION = ('{driver}:1:0: error: import {module} failed, environment already contains '
             "'X.g' from {other}")
PLENTY = 64 * audit.BATCH_MEMORY


class FakeLean:
    """Collides when a batch holds both modules of a pair; fails on any module named Bad*.

    `hold` maps a module to an event its batch waits for; `seen` records each
    batch's first module, in launch order.
    """

    def __init__(self, pairs=(), delay=0.0, hold=None, interrupt=False):
        self.pairs = [tuple(pair) for pair in pairs]
        self.delay = delay
        self.hold = hold or {}
        self.interrupt = interrupt
        self.lock = threading.Lock()
        self.running = 0
        self.peak = 0
        self.calls = 0
        self.warmups = 0
        self.order = []

    def __call__(self, command, **kwargs):
        if command == ['lake', 'env', 'true']:
            with self.lock:
                self.warmups += 1
                self.order.append('warm-up')
            return subprocess.CompletedProcess(command, 0, '', None)
        driver = command[-1]
        batch = [line.split()[1] for line in Path(driver).read_text().splitlines()
                 if line.startswith('import ')]
        with self.lock:
            self.running += 1
            self.calls += 1
            self.peak = max(self.peak, self.running)
            self.order.append(batch[0])
        try:
            if self.interrupt:
                raise KeyboardInterrupt
            for module in batch:
                if module in self.hold:
                    self.hold[module].wait(10)
            time.sleep(self.delay)
            for first, second in self.pairs:
                if first in batch and second in batch:
                    return subprocess.CompletedProcess(
                        command, 1, COLLISION.format(driver=driver, module=second, other=first), None)
            bad = [module for module in batch if module.split('.')[-1].startswith('Bad')]
            if bad:
                return subprocess.CompletedProcess(command, 1, f'{driver}:3:0: error: policy {bad[0]}', None)
            return subprocess.CompletedProcess(command, 0, '', None)
        finally:
            with self.lock:
                self.running -= 1


def run_audit(modules, fake, memory=PLENTY, **kwargs):
    out = io.StringIO()
    with mock.patch.object(audit.subprocess, 'run', fake), \
            mock.patch.object(audit, 'available_memory', return_value=memory), \
            contextlib.redirect_stdout(out):
        result = audit.audit(Path('.'), modules, '-- checker\n', **kwargs)
    return result, out.getvalue().splitlines()


def names(count, width=3, bad=()):
    modules = [f'L.M{index:0{width}d}' for index in range(count)]
    for index, name in bad:
        modules[index] = name
    return modules


MODULES = names(40)
# One split each for the first two pairs; three nested splits for the adjacent third pair;
# the last pair is in two different groups and never collides.
PAIRS = [('L.M003', 'L.M005'), ('L.M011', 'L.M012'), ('L.M016', 'L.M017'), ('L.M030', 'L.M038')]


class ParallelAuditTests(unittest.TestCase):
    def test_parallel_run_matches_sequential_run(self):
        sequential_fake = FakeLean(PAIRS)
        sequential, sequential_lines = run_audit(MODULES, sequential_fake, batch_size=8, workers=1)
        fake = FakeLean(PAIRS, delay=0.05)
        parallel, parallel_lines = run_audit(MODULES, fake, batch_size=8, workers=4)
        self.assertGreater(fake.peak, 1, 'the batches did not run in parallel')
        self.assertEqual(sequential.pop('workers'), 1)
        self.assertEqual(parallel.pop('workers'), 4)
        self.assertEqual(parallel, sequential)
        self.assertEqual(parallel['checkedModules'], MODULES)
        self.assertEqual(parallel_lines, sequential_lines)
        self.assertEqual(sequential['importCollisionSplits'], 5)
        self.assertEqual(sequential['attempts'], 5 + 2 * 5)
        self.assertEqual((sequential_fake.warmups, fake.warmups), (0, 1))
        self.assertEqual(fake.order[0], 'warm-up')

    def test_a_later_group_does_not_start_before_an_earlier_one(self):
        release = threading.Event()
        real_start = audit.Admission.start

        def start(self, index, first, real_start=real_start):
            if index == 0 and first:
                release.wait(10)  # group 0's worker is slow to reach the gate
            return real_start(self, index, first)

        fake = FakeLean()
        result = {}

        def run():
            with mock.patch.object(audit.Admission, 'start', start):
                result['audit'], _ = run_audit(names(16, 2), fake, batch_size=8, workers=2)

        worker = threading.Thread(target=run)
        worker.start()
        time.sleep(0.3)
        self.assertEqual(fake.calls, 0, 'group 1 started before group 0')
        release.set()
        worker.join(10)
        self.assertEqual(sorted(fake.order[1:]), ['L.M00', 'L.M08'])
        self.assertEqual(result['audit']['checkedModules'], names(16, 2))

    def test_earlier_group_is_reported_when_a_later_one_fails_first(self):
        # Group 1 fails while group 0 still runs; group 0 then fails too, or succeeds.
        for first_module, expected in (('L.BadFirst', 'BadFirst'), ('L.M00', 'BadSecond')):
            modules = names(16, 2, bad=[(0, first_module), (8, 'L.BadSecond')])
            second_failed = threading.Event()
            real_fail = audit.Admission.fail

            def fail(self, index, real_fail=real_fail, event=second_failed):
                real_fail(self, index)
                if index == 1:
                    event.set()

            fake = FakeLean(hold={first_module: second_failed})
            with mock.patch.object(audit.Admission, 'fail', fail):
                with self.assertRaisesRegex(audit.AuditFailure, expected):
                    run_audit(modules, fake, batch_size=8, workers=2)
            self.assertTrue(second_failed.is_set())
            self.assertEqual(sorted(fake.order[1:]), sorted([first_module, 'L.BadSecond']))

    def test_groups_waiting_to_start_do_not_start_after_a_failure(self):
        modules = names(32, 2, bad=[(0, 'L.Bad')])
        fake = FakeLean(delay=0.2)
        # Memory for one batch: groups 1-3 wait while group 0 runs, then group 0 fails.
        with self.assertRaisesRegex(audit.AuditFailure, 'L.Bad'):
            run_audit(modules, fake, memory=audit.BATCH_MEMORY, batch_size=8, workers=4)
        self.assertEqual(fake.calls, 1)

    def test_memory_for_one_batch_runs_one_batch_at_a_time(self):
        for memory in (audit.BATCH_MEMORY, 2 * audit.BATCH_MEMORY - 1):
            fake = FakeLean(delay=0.05)
            result, _ = run_audit(MODULES, fake, memory=memory, batch_size=8, workers=4)
            self.assertEqual(fake.peak, 1)
            self.assertEqual(result['checkedModules'], MODULES)
        fake = FakeLean(delay=0.05)
        run_audit(MODULES, fake, memory=2 * audit.BATCH_MEMORY, batch_size=8, workers=4)
        self.assertEqual(fake.peak, 2)

    def test_failure_cancels_groups_not_started(self):
        modules = names(32, 2, bad=[(0, 'L.Bad')])
        fake = FakeLean(delay=0.1)
        with self.assertRaises(audit.AuditFailure):
            run_audit(modules, fake, batch_size=4, workers=1)
        self.assertEqual(fake.calls, 1)

    def test_one_worker_stops_at_an_interrupt(self):
        fake = FakeLean(PAIRS, interrupt=True)
        with self.assertRaises(KeyboardInterrupt):
            run_audit(MODULES, fake, batch_size=8, workers=1)
        self.assertEqual((fake.calls, fake.warmups), (1, 0))

    def test_an_exception_in_a_batch_stops_batches_waiting_to_start(self):
        class Stop(BaseException):
            pass

        fake = FakeLean()

        def interrupting_run(command, **kwargs):
            if command != ['lake', 'env', 'true'] and 'L.M000' in Path(command[-1]).read_text():
                time.sleep(0.1)
                raise Stop
            return fake(command, **kwargs)

        # Memory for one batch: the other groups wait while group 0 runs.
        with self.assertRaises(Stop):
            run_audit(MODULES, interrupting_run, memory=audit.BATCH_MEMORY, batch_size=8, workers=4)
        self.assertEqual(fake.calls, 0)

    def test_cancellation_stops_batches_waiting_to_start(self):
        class Stop(BaseException):
            pass

        fake = FakeLean(delay=0.2)
        real_print = builtins.print

        def failing_print(*args, **kwargs):
            # The coordinator fails as it reports group 0, as on an interrupt.
            raise Stop

        with mock.patch.object(builtins, 'print', failing_print):
            with self.assertRaises(Stop):
                run_audit(MODULES, fake, memory=audit.BATCH_MEMORY, batch_size=8, workers=4)
        real_print(end='')
        # Group 1 may have started as group 0 ended; groups 2-4 were waiting and never start.
        self.assertLessEqual(fake.calls, 2)
        self.assertTrue(set(fake.order) <= {'warm-up', 'L.M000', 'L.M008'}, fake.order)

    def test_override_of_one_runs_the_batches_one_by_one(self):
        fake = FakeLean(PAIRS, delay=0.02)
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: '1'}):
            result, _ = run_audit(MODULES, fake, batch_size=8)
        self.assertEqual((fake.peak, fake.warmups), (1, 0))
        self.assertEqual(result['workers'], 1)
        self.assertEqual(result['checkedModules'], MODULES)

    def test_worker_count_follows_memory_and_the_override(self):
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: ''}), \
                mock.patch.object(audit, 'available_memory', return_value=int(2.5 * audit.BATCH_MEMORY)), \
                mock.patch.object(audit.os, 'sched_getaffinity', return_value=set(range(64)), create=True):
            self.assertEqual(audit.worker_count(18), 2)
            self.assertEqual(audit.worker_count(1), 1)
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: ''}), \
                mock.patch.object(audit, 'available_memory', return_value=None):
            self.assertEqual(audit.worker_count(18), 1)
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: ''}), \
                mock.patch.object(audit, 'available_memory', return_value=100 * audit.BATCH_MEMORY), \
                mock.patch.object(audit.os, 'sched_getaffinity', return_value=set(range(4)), create=True):
            self.assertEqual(audit.worker_count(18), 4)
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: '3'}), \
                mock.patch.object(audit, 'available_memory', return_value=0):
            self.assertEqual(audit.worker_count(18), 3)
            self.assertEqual(audit.worker_count(2), 2)
        for value in ('0', '-1', 'two', '1.5', '\u00b2', '\u0663', '1' * 5000, '10000'):
            with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: value}):
                with self.assertRaises(audit.AuditFailure):
                    audit.worker_count(18)


class CgroupTests(unittest.TestCase):
    def proc(self, files):
        real_open = builtins.open

        def fake_open(path, *args, **kwargs):
            if str(path) in files:
                return io.StringIO(files[str(path)])
            if str(path).startswith('/proc/'):
                raise FileNotFoundError(path)
            return real_open(path, *args, **kwargs)

        return mock.patch('builtins.open', fake_open)

    def tree(self, folder, groups):
        gib = 2**30
        for relative, (limit, used, inactive) in groups.items():
            group = Path(folder, relative)
            group.mkdir(parents=True, exist_ok=True)
            (group / 'memory.max').write_text('max\n' if limit is None else f'{limit * gib}\n')
            (group / 'memory.current').write_text(f'{used * gib}\n')
            (group / 'memory.stat').write_text(f'anon 1\ninactive_file {inactive * gib}\n')

    def mountinfo(self, root, mount):
        return (f'24 1 0:22 / / rw - ext4 /dev/root rw\n'
                f'31 24 0:26 {root} {mount} rw,nosuid shared:9 - cgroup2 cgroup2 rw\n')

    def test_walks_the_visible_ancestors_and_takes_the_tightest(self):
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'': (64, 4, 0), 'user.slice': (16, 10, 4), 'user.slice/unit.service': (None, 9, 0)})
            files = {'/proc/self/cgroup': '0::/user.slice/unit.service\n',
                     '/proc/self/mountinfo': self.mountinfo('/', folder)}
            with self.proc(files):
                # user.slice: 16 GiB allowed, 10 used of which 4 inactive file pages, so 10 left.
                self.assertEqual(audit.cgroup_headroom(), 10 * 2**30)

    def test_resolves_the_membership_against_the_mount_root(self):
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'': (64, 4, 0), 'team-job': (8, 2, 0)})
            files = {'/proc/self/cgroup': '0::/slice/parent/team-job\n',
                     '/proc/self/mountinfo': self.mountinfo('/slice/parent', folder)}
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 6 * 2**30)

    def test_an_unreadable_cgroup_counts_as_no_headroom(self):
        with tempfile.TemporaryDirectory() as folder:
            cases = [
                {'/proc/self/cgroup': '0::/other/job\n',
                 '/proc/self/mountinfo': self.mountinfo('/slice/parent', folder)},
                {'/proc/self/cgroup': '0::/job\n', '/proc/self/mountinfo': '24 1 0:22 / / rw - ext4 /dev/root rw\n'},
                {'/proc/self/cgroup': '7:memory:/job\n0::/job\n',
                 '/proc/self/mountinfo': self.mountinfo('/', folder)},
            ]
            for files in cases:
                with self.proc(files):
                    self.assertEqual(audit.cgroup_headroom(), 0)
        with self.proc({}):
            self.assertIsNone(audit.cgroup_headroom())

    def test_available_memory_takes_the_tighter_limit(self):
        meminfo = {'/proc/meminfo': 'MemTotal: 16000000 kB\nMemAvailable: 14000000 kB\n'}
        with self.proc(meminfo), mock.patch.object(audit, 'cgroup_headroom', return_value=4 * 2**30):
            self.assertEqual(audit.available_memory(), 4 * 2**30)
        with self.proc(meminfo), mock.patch.object(audit, 'cgroup_headroom', return_value=None):
            self.assertEqual(audit.available_memory(), 14000000 * 1024)
        with self.proc({}):
            self.assertIsNone(audit.available_memory())


if __name__ == '__main__':
    unittest.main()
