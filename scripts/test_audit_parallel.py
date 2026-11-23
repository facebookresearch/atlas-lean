#!/usr/bin/env python3
"""Parallel execution of the compiled audit: same results as a sequential run.

Lake and Lean are replaced by a fake `subprocess.run` that answers the
environment probe and reads the driver file, so these tests need no Lean build.
"""
from __future__ import annotations

import builtins
import concurrent.futures
import contextlib
import io
import json
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
FAKE_LEAN = '/fake/toolchain/bin/lean'
PLENTY = 64 * audit.BATCH_MEMORY


class FakeLean:
    """Collides when a batch holds both modules of a pair; fails on any module named Bad*.

    `hold` maps a module to an event its batch waits for; `order` records each
    batch's first module, in launch order.
    """

    def __init__(self, pairs=(), delay=0.0, hold=None, interrupt=False, launched=None):
        self.pairs = [tuple(pair) for pair in pairs]
        self.delay = delay
        self.hold = hold or {}
        self.interrupt = interrupt
        self.launched = launched  # called with the number of batches launched so far
        self.lock = threading.Lock()
        self.running = 0
        self.peak = 0
        self.calls = 0
        self.probes = 0
        self.order = []

    def __call__(self, command, **kwargs):
        if command[:3] == ['lake', 'env', sys.executable]:
            with self.lock:
                self.probes += 1
            return subprocess.CompletedProcess(command, 0, json.dumps({'LEAN': FAKE_LEAN, 'PATH': ''}), '')
        assert command[0] == FAKE_LEAN and kwargs['env']['LEAN'] == FAKE_LEAN, command
        driver = command[-1]
        batch = [line.split()[1] for line in Path(driver).read_text().splitlines()
                 if line.startswith('import ')]
        with self.lock:
            self.running += 1
            self.calls += 1
            self.peak = max(self.peak, self.running)
            self.order.append(batch[0])
            calls = self.calls
        if self.launched:
            self.launched(calls)
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


def run_audit(modules, fake, **kwargs):
    out = io.StringIO()
    with mock.patch.object(audit.subprocess, 'run', fake), \
            mock.patch.object(audit, 'available_memory', return_value=PLENTY), \
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
        self.assertLessEqual(fake.peak, 4)
        self.assertEqual(sequential.pop('workers'), 1)
        self.assertEqual(parallel.pop('workers'), 4)
        self.assertEqual(parallel, sequential)
        self.assertEqual(parallel['checkedModules'], MODULES)
        self.assertEqual(parallel_lines, sequential_lines)
        self.assertEqual(sequential['importCollisionSplits'], 5)
        self.assertEqual(sequential['attempts'], 5 + 2 * 5)
        # Lake is asked for its environment once; every batch runs Lean itself.
        self.assertEqual((sequential_fake.probes, fake.probes), (1, 1))

    def test_a_later_group_is_not_admitted_before_an_earlier_one(self):
        release = threading.Event()
        real_admit = audit.Admission.admit

        def admit(self, index, first, real_admit=real_admit):
            if index == 0 and first:
                release.wait(10)  # group 0's worker is slow to reach admission
            return real_admit(self, index, first)

        fake = FakeLean()
        result = {}

        def run():
            with mock.patch.object(audit.Admission, 'admit', admit):
                result['audit'], _ = run_audit(names(16, 2), fake, batch_size=8, workers=2)

        worker = threading.Thread(target=run)
        worker.start()
        time.sleep(0.3)
        self.assertEqual(fake.calls, 0, 'group 1 was admitted before group 0')
        release.set()
        worker.join(10)
        self.assertEqual(sorted(fake.order), ['L.M00', 'L.M08'])
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
            self.assertEqual(sorted(fake.order), sorted([first_module, 'L.BadSecond']))

    def test_no_later_group_is_admitted_after_a_failure(self):
        # Groups 1-3 run while group 0 fails; groups 4-7 come after the failure.
        modules = names(64, 2, bad=[(0, 'L.Bad')])
        others, failed = threading.Event(), threading.Event()
        real_fail = audit.Admission.fail

        def fail(self, index, real_fail=real_fail):
            real_fail(self, index)
            failed.set()

        fake = FakeLean(hold={'L.Bad': others, 'L.M08': failed, 'L.M16': failed, 'L.M24': failed},
                        launched=lambda calls: calls == 4 and others.set())
        with mock.patch.object(audit.Admission, 'fail', fail):
            with self.assertRaisesRegex(audit.AuditFailure, 'L.Bad'):
                run_audit(modules, fake, batch_size=8, workers=4)
        self.assertEqual(sorted(fake.order), ['L.Bad', 'L.M08', 'L.M16', 'L.M24'])

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
        self.assertEqual(fake.calls, 1)

    def test_cancellation_admits_nothing_more(self):
        admission = audit.Admission()
        admission.admit(0, True)
        waiting = {}

        def wait_for_group_2():
            try:
                admission.admit(2, True)  # waits: group 1 has not been admitted
                waiting['result'] = 'admitted'
            except audit.SkippedGroup:
                waiting['result'] = 'skipped'

        thread = threading.Thread(target=wait_for_group_2)
        thread.start()
        time.sleep(0.1)
        self.assertNotIn('result', waiting)
        admission.cancel()
        thread.join(10)
        self.assertEqual(waiting['result'], 'skipped')
        with self.assertRaises(audit.SkippedGroup):
            admission.admit(1, True)
        with self.assertRaises(audit.SkippedGroup):
            admission.admit(0, False)

    def test_an_interrupt_while_submitting_cancels_the_queued_groups(self):
        # Groups 0 and 1 run and groups 2-3 wait in the queue when submitting group 4 is interrupted.
        running, release = threading.Event(), threading.Event()
        fake = FakeLean(hold={'L.M000': release, 'L.M008': release},
                        launched=lambda calls: calls == 2 and running.set())
        real_submit = concurrent.futures.ThreadPoolExecutor.submit
        real_cancel = audit.Admission.cancel
        submitted = []

        def submit(pool, *args, **kwargs):
            if len(submitted) == 4:
                running.wait(10)
                raise KeyboardInterrupt
            submitted.append(args[1])
            return real_submit(pool, *args, **kwargs)

        def cancel(self, real_cancel=real_cancel):
            real_cancel(self)
            release.set()  # the running batches end only once the audit is cancelled

        with mock.patch.object(concurrent.futures.ThreadPoolExecutor, 'submit', submit), \
                mock.patch.object(audit.Admission, 'cancel', cancel):
            with self.assertRaises(KeyboardInterrupt):
                run_audit(MODULES, fake, batch_size=8, workers=2)
        self.assertTrue(release.is_set())
        self.assertEqual(sorted(fake.order), ['L.M000', 'L.M008'])

    def test_a_timeout_stops_lean_itself(self):
        # Each batch's process is Lean, not a Lake wrapper, so the timeout ends it.
        with tempfile.TemporaryDirectory() as folder:
            marker = Path(folder, 'still-running')
            lean = Path(folder, 'lean')
            lean.write_text(f'#!/bin/sh\nsleep 2\ntouch {marker}\n')
            lean.chmod(0o755)
            real_run = subprocess.run

            def run(command, **kwargs):
                if command[:3] == ['lake', 'env', sys.executable]:
                    return subprocess.CompletedProcess(command, 0, json.dumps({'LEAN': str(lean)}), '')
                return real_run(command, **kwargs)

            with mock.patch.object(audit.subprocess, 'run', run), \
                    mock.patch.object(audit, 'BATCH_TIMEOUT', 0.5), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(subprocess.TimeoutExpired):
                    audit.audit(Path(folder), ['L.A', 'L.B'], '', batch_size=1, workers=1)
            time.sleep(2.5)
            self.assertFalse(marker.exists(), 'Lean kept running after the timeout')

    def test_override_of_one_runs_the_batches_one_by_one(self):
        fake = FakeLean(PAIRS, delay=0.02)
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: '1'}):
            result, _ = run_audit(MODULES, fake, batch_size=8)
        self.assertEqual(fake.peak, 1)
        self.assertEqual(result['workers'], 1)
        self.assertEqual(result['checkedModules'], MODULES)

    def test_lake_environment_failures_are_audit_failures(self):
        for answer in (subprocess.CompletedProcess([], 1, '', 'error: no workspace'),
                       subprocess.CompletedProcess([], 0, 'not json', ''),
                       subprocess.CompletedProcess([], 0, json.dumps({'PATH': ''}), '')):
            with mock.patch.object(audit.subprocess, 'run', return_value=answer), \
                    mock.patch.object(audit, 'available_memory', return_value=PLENTY):
                with self.assertRaises(audit.AuditFailure):
                    audit.audit(Path('.'), ['L.A'], '', workers=1)

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
    gib = 2**30

    def proc(self, files, procfs=True):
        """Serve these /proc files (text or bytes); any other /proc path is missing."""
        real_open = builtins.open

        def fake_open(path, *args, **kwargs):
            if str(path) in files:
                content = files[str(path)]
                if isinstance(content, bytes):
                    return io.TextIOWrapper(io.BytesIO(content), encoding=kwargs.get('encoding', 'utf-8'),
                                            errors=kwargs.get('errors', 'strict'))
                return io.StringIO(content)
            if str(path).startswith('/proc/'):
                raise FileNotFoundError(path)
            return real_open(path, *args, **kwargs)

        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch('builtins.open', fake_open))
        stack.enter_context(mock.patch.object(audit.os.path, 'isdir',
                                              side_effect=lambda path: procfs if path == '/proc/self'
                                              else os.path.exists(path)))
        return stack

    def tree(self, folder, groups):
        for relative, (limit, used, inactive) in groups.items():
            group = Path(folder, relative)
            group.mkdir(parents=True, exist_ok=True)
            (group / 'memory.max').write_text('max\n' if limit is None else f'{limit * self.gib}\n')
            (group / 'memory.current').write_text(f'{used * self.gib}\n')
            (group / 'memory.stat').write_text(f'anon 1\ninactive_file {inactive * self.gib}\n')

    def mount_line(self, number, root, mount):
        return f'{number} 24 0:{number} {root} {mount} rw,nosuid shared:9 - cgroup2 cgroup2 rw\n'

    def mountinfo(self, root, mount):
        return '24 1 0:22 / / rw - ext4 /dev/root rw\n' + self.mount_line(31, root, mount)

    def test_walks_the_visible_ancestors_and_takes_the_tightest(self):
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'': (64, 4, 0), 'user.slice': (16, 10, 4), 'user.slice/unit.service': (None, 9, 0)})
            files = {'/proc/self/cgroup': '0::/user.slice/unit.service\n',
                     '/proc/self/mountinfo': self.mountinfo('/', folder)}
            with self.proc(files):
                # user.slice: 16 GiB allowed, 10 used of which 4 inactive file pages, so 10 left.
                self.assertEqual(audit.cgroup_headroom(), 10 * self.gib)

    def test_resolves_the_membership_against_the_mount_root(self):
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'': (64, 4, 0), 'team-job': (8, 2, 0)})
            files = {'/proc/self/cgroup': '0::/slice/parent/team-job\n',
                     '/proc/self/mountinfo': self.mountinfo('/slice/parent', folder)}
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)

    def test_every_mount_that_shows_the_cgroup_counts(self):
        # A bind mount of the job's own cgroup, and a mount that also shows its limited parent.
        with tempfile.TemporaryDirectory() as job, tempfile.TemporaryDirectory() as parent:
            self.tree(job, {'': (None, 1, 0)})
            self.tree(parent, {'': (16, 10, 0), 'job': (None, 1, 0)})
            mounts = [self.mount_line(31, '/team/job', job), self.mount_line(32, '/team', parent)]
            for lines in (mounts, mounts[::-1]):
                files = {'/proc/self/cgroup': '0::/team/job\n',
                         '/proc/self/mountinfo': '24 1 0:22 / / rw - ext4 /dev/root rw\n' + ''.join(lines)}
                with self.proc(files):
                    self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)

    def test_unreadable_or_malformed_cgroup_data_count_as_no_headroom(self):
        def files(folder):
            return {'/proc/self/cgroup': '0::/job\n', '/proc/self/mountinfo': self.mountinfo('/', folder)}

        for damage in ('malformed', 'non-ascii', 'no-current', 'missing-group', 'unreadable', 'untraversable'):
            with self.subTest(damage=damage), tempfile.TemporaryDirectory() as folder:
                self.tree(folder, {'': (64, 4, 0), 'job': (8, 2, 0), 'job/inner': (None, 1, 0)})
                job = Path(folder, 'job')
                cgroup = '0::/job\n'
                if damage == 'malformed':
                    (job / 'memory.max').write_text('eight\n')
                elif damage == 'non-ascii':
                    (job / 'memory.max').write_bytes(b'\xd9\xa3\n')  # an Arabic-Indic digit
                elif damage == 'no-current':
                    (job / 'memory.current').unlink()
                elif damage == 'missing-group':
                    cgroup = '0::/gone\n'
                elif damage == 'unreadable':
                    real_read = audit.read_kernel_text

                    def read(path, real_read=real_read, job=job):
                        if Path(path) == job / 'memory.max':
                            raise PermissionError(path)
                        return real_read(path)
                elif damage == 'untraversable':
                    cgroup = '0::/job/inner\n'
                    real_is_dir = Path.is_dir

                    def is_dir(path, real_is_dir=real_is_dir, job=job):
                        if job in path.parents or path == job:
                            raise PermissionError(path)
                        return real_is_dir(path)
                served = {**files(folder), '/proc/self/cgroup': cgroup}
                with contextlib.ExitStack() as stack:
                    stack.enter_context(self.proc(served))
                    if damage == 'unreadable':
                        stack.enter_context(mock.patch.object(audit, 'read_kernel_text', read))
                    if damage == 'untraversable':
                        stack.enter_context(mock.patch.object(Path, 'is_dir', is_dir))
                    self.assertEqual(audit.cgroup_headroom(), 0)

    def test_undecodable_mountinfo_entries_are_skipped(self):
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'': (None, 1, 0), 'job': (8, 2, 0)})
            mountinfo = (b'24 1 0:22 / / rw - ext4 /dev/root rw\n'
                         b'25 24 0:23 / /media/caf\xe9 rw - vfat /dev/sdb1 rw\n'
                         + self.mount_line(31, '/', folder).encode())
            with self.proc({'/proc/self/cgroup': '0::/job\n', '/proc/self/mountinfo': mountinfo}):
                self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)

    def test_unreadable_cgroup_membership_cases(self):
        with tempfile.TemporaryDirectory() as folder:
            for files in (
                    {'/proc/self/cgroup': '0::/other/job\n', '/proc/self/mountinfo': self.mountinfo('/slice/parent', folder)},
                    {'/proc/self/cgroup': '0::/job\n', '/proc/self/mountinfo': '24 1 0:22 / / rw - ext4 /dev/root rw\n'},
                    {'/proc/self/cgroup': '7:memory:/job\n0::/job\n', '/proc/self/mountinfo': self.mountinfo('/', folder)}):
                with self.proc(files):
                    self.assertEqual(audit.cgroup_headroom(), 0)
        with self.proc({}, procfs=True):
            self.assertEqual(audit.cgroup_headroom(), 0)  # procfs, but no readable /proc/self/cgroup
        with self.proc({}, procfs=False):
            self.assertIsNone(audit.cgroup_headroom())  # no procfs at all
        with self.proc({'/proc/self/cgroup': '1:name=systemd:/job\n'}):
            self.assertIsNone(audit.cgroup_headroom())  # no cgroup v2 membership, no v1 memory controller

    def test_a_level_without_memory_files_sets_no_limit(self):
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'job': (8, 2, 0)})
            for name in ('memory.max', 'memory.current', 'memory.stat'):
                Path(folder, name).unlink(missing_ok=True)
            files = {'/proc/self/cgroup': '0::/job\n', '/proc/self/mountinfo': self.mountinfo('/', folder)}
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)

    def test_available_memory_takes_the_tighter_limit(self):
        meminfo = {'/proc/meminfo': 'MemTotal: 16000000 kB\nMemAvailable: 14000000 kB\n'}
        with self.proc(meminfo), mock.patch.object(audit, 'cgroup_headroom', return_value=4 * self.gib):
            self.assertEqual(audit.available_memory(), 4 * self.gib)
        with self.proc(meminfo), mock.patch.object(audit, 'cgroup_headroom', return_value=None):
            self.assertEqual(audit.available_memory(), 14000000 * 1024)
        with self.proc({}):
            self.assertIsNone(audit.available_memory())  # no /proc/meminfo


if __name__ == '__main__':
    unittest.main()
