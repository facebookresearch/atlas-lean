#!/usr/bin/env python3
"""Parallel execution of the compiled audit: same results as a sequential run.

The Lean batches are replaced by a fake `subprocess.run` that reads the driver
file, so these tests need no Lean build.
"""
from __future__ import annotations

import io
import contextlib
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


class FakeLean:
    """Collides when a batch holds both modules of a pair; fails on any module named Bad*."""

    def __init__(self, pairs=(), delay=0.0, delays=None):
        self.pairs = [tuple(pair) for pair in pairs]
        self.delay = delay
        self.delays = delays or {}
        self.lock = threading.Lock()
        self.running = 0
        self.peak = 0
        self.calls = 0

    def __call__(self, command, **kwargs):
        driver = command[-1]
        batch = [line.split()[1] for line in Path(driver).read_text().splitlines()
                 if line.startswith('import ')]
        with self.lock:
            self.running += 1
            self.calls += 1
            self.peak = max(self.peak, self.running)
        try:
            time.sleep(max([self.delay] + [self.delays.get(module, 0.0) for module in batch]))
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
    with mock.patch.object(audit.subprocess, 'run', fake), contextlib.redirect_stdout(out):
        result = audit.audit(Path('.'), modules, '-- checker\n', **kwargs)
    return result, out.getvalue().splitlines()


MODULES = [f'L.M{index:03d}' for index in range(40)]
# One split each for the first two pairs; three nested splits for the adjacent third pair;
# the last pair is in two different groups and never collides.
PAIRS = [('L.M003', 'L.M005'), ('L.M011', 'L.M012'), ('L.M016', 'L.M017'), ('L.M030', 'L.M038')]


class ParallelAuditTests(unittest.TestCase):
    def test_parallel_run_matches_sequential_run(self):
        sequential, sequential_lines = run_audit(MODULES, FakeLean(PAIRS), batch_size=8, workers=1)
        fake = FakeLean(PAIRS, delay=0.05)
        with mock.patch.object(audit, 'available_memory', return_value=64 * audit.BATCH_MEMORY):
            parallel, parallel_lines = run_audit(MODULES, fake, batch_size=8, workers=4)
        self.assertGreater(fake.peak, 1, 'the batches did not run in parallel')
        self.assertEqual(sequential.pop('workers'), 1)
        self.assertEqual(parallel.pop('workers'), 4)
        self.assertEqual(parallel, sequential)
        self.assertEqual(parallel['checkedModules'], MODULES)
        self.assertEqual(parallel_lines, sequential_lines)
        self.assertEqual(sequential['importCollisionSplits'], 5)
        self.assertEqual(sequential['attempts'], 5 + 2 * 5)

    def test_first_failing_group_is_reported(self):
        modules = [f'L.M{index:02d}' for index in range(24)]
        modules[2] = 'L.BadEarly'
        modules[20] = 'L.BadLate'
        fake = FakeLean(delays={'L.BadEarly': 0.3})
        with mock.patch.object(audit, 'available_memory', return_value=64 * audit.BATCH_MEMORY):
            with self.assertRaisesRegex(audit.AuditFailure, 'BadEarly'):
                run_audit(modules, fake, batch_size=8, workers=3)

    def test_failure_cancels_groups_not_started(self):
        modules = [f'L.M{index:02d}' for index in range(32)]
        modules[0] = 'L.Bad'
        fake = FakeLean(delay=0.1)
        with self.assertRaises(audit.AuditFailure):
            run_audit(modules, fake, batch_size=4, workers=1)
        self.assertEqual(fake.calls, 1)

    def test_memory_gate_runs_one_batch_when_memory_is_short(self):
        fake = FakeLean(delay=0.05)
        with mock.patch.object(audit, 'available_memory', return_value=audit.BATCH_MEMORY - 1):
            result, _ = run_audit(MODULES, fake, batch_size=8, workers=4)
        self.assertEqual(fake.peak, 1)
        self.assertEqual(result['checkedModules'], MODULES)

    def test_override_of_one_runs_the_batches_one_by_one(self):
        fake = FakeLean(PAIRS, delay=0.02)
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: '1'}), \
                mock.patch.object(audit, 'available_memory', return_value=64 * audit.BATCH_MEMORY):
            result, _ = run_audit(MODULES, fake, batch_size=8)
        self.assertEqual(fake.peak, 1)
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
        for value in ('0', '-1', 'two', '1.5'):
            with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: value}):
                with self.assertRaises(audit.AuditFailure):
                    audit.worker_count(18)

    def test_cgroup_headroom_reads_the_tightest_ancestor(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            leaf = root / 'user.slice' / 'unit.service'
            leaf.mkdir(parents=True)
            gib = 2**30
            (root / 'user.slice' / 'memory.max').write_text(f'{16 * gib}\n')
            (root / 'user.slice' / 'memory.current').write_text(f'{10 * gib}\n')
            (root / 'user.slice' / 'memory.stat').write_text(f'anon 1\ninactive_file {4 * gib}\n')
            (leaf / 'memory.max').write_text('max\n')
            (leaf / 'memory.current').write_text(f'{9 * gib}\n')
            membership = '0::/user.slice/unit.service\n'
            real_path = audit.Path

            def fake_path(*parts):
                if parts and parts[0] == '/sys/fs/cgroup':
                    return real_path(folder, *parts[1:])
                return real_path(*parts)

            with mock.patch('builtins.open', mock.mock_open(read_data=membership)), \
                    mock.patch.object(audit, 'Path', side_effect=fake_path):
                # 16 GiB allowed, 10 GiB used of which 4 GiB inactive file pages: 10 GiB left.
                self.assertEqual(audit.cgroup_headroom(), 10 * gib)

    def test_available_memory_takes_the_tighter_cgroup_limit(self):
        meminfo = 'MemTotal: 16000000 kB\nMemAvailable: 14000000 kB\n'
        with mock.patch('builtins.open', mock.mock_open(read_data=meminfo)), \
                mock.patch.object(audit, 'cgroup_headroom', return_value=4 * 2**30):
            self.assertEqual(audit.available_memory(), 4 * 2**30)
        with mock.patch('builtins.open', mock.mock_open(read_data=meminfo)), \
                mock.patch.object(audit, 'cgroup_headroom', return_value=None):
            self.assertEqual(audit.available_memory(), 14000000 * 1024)


if __name__ == '__main__':
    unittest.main()
