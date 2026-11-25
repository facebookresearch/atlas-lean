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
import os
from pathlib import Path
import signal
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
HOLD_LIMIT = 20  # seconds a fake batch waits for its event before failing the test
PLENTY = 64 * audit.BATCH_MEMORY


def pidfd_supported():
    try:
        os.close(os.pidfd_open(os.getpid()))
        return True
    except (AttributeError, OSError):
        return False


def listing(environment):
    """What `env -0` prints for this environment."""
    return b''.join(os.fsencode(name) + b'=' + os.fsencode(value) + b'\0' for name, value in environment.items())


class FakeProcess:
    """A batch's Lean process: runs the fake batch when its output is read; `kill` ends it."""

    pid = -1  # not a Popen: Admission opens no pidfd and signals it through kill()
    stdout = None

    def __init__(self, fake, command):
        self.fake, self.command = fake, command
        self.killed = threading.Event()
        self.returncode = None
        self.output = ''

    def communicate(self, timeout=None):
        if self.returncode is None:
            self.returncode, self.output = self.fake.run_batch(self.command, self.killed)
        return self.output, None

    def kill(self):
        self.killed.set()

    def wait(self):
        return self.returncode


class FakeLean:
    """Collides when a batch holds both modules of a pair; fails on any module named Bad*.

    `hold` maps a module to an event its batch waits for; `order` records each
    batch's first module, in launch order; `processes` the launched processes.
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
        self.started = []
        self.processes = {}

    def __call__(self, command, **kwargs):
        """subprocess.run: Lake's environment listing, or loading its configuration."""
        with self.lock:
            self.probes += 1
        if command == ['lake', 'env', 'true']:
            return subprocess.CompletedProcess(command, 0, None, b'')
        assert command == ['lake', 'env', 'env', '-0'], command
        kwargs['stdout'].write(listing({'LEAN': FAKE_LEAN, 'PATH': '', 'SECRET': 'hunter2'}))
        return subprocess.CompletedProcess(command, 0, None, b'')

    def launch(self, command, root, environment):
        if audit.LIST_ENVIRONMENT:
            assert command[0] == FAKE_LEAN and environment['LEAN'] == FAKE_LEAN, command
        else:
            assert command[:3] == ['lake', 'env', 'lean'] and environment is None, command
        batch = [line.split()[1] for line in Path(command[-1]).read_text().splitlines()
                 if line.startswith('import ')]
        process = FakeProcess(self, command)
        with self.lock:
            self.running += 1
            self.calls += 1
            self.peak = max(self.peak, self.running)
            self.order.append(batch[0])
            self.started.append(time.monotonic())
            self.processes[batch[0]] = process
            calls = self.calls
        if self.launched:
            self.launched(calls)
        return process

    def run_batch(self, command, killed):
        driver = command[-1]
        batch = [line.split()[1] for line in Path(driver).read_text().splitlines()
                 if line.startswith('import ')]
        try:
            if self.interrupt:
                raise KeyboardInterrupt
            for module in batch:
                if module in self.hold:
                    deadline = time.monotonic() + HOLD_LIMIT
                    while not self.hold[module].wait(0.01):
                        if killed.is_set():
                            return -9, ''
                        if time.monotonic() > deadline:  # fail rather than hang
                            return 99, f'{driver}:1:0: error: {module} was held for {HOLD_LIMIT} s'
            if killed.wait(self.delay):
                return -9, ''
            for first, second in self.pairs:
                if first in batch and second in batch:
                    return 1, COLLISION.format(driver=driver, module=second, other=first)
            bad = [module for module in batch if module.split('.')[-1].startswith('Bad')]
            if bad:
                return 1, f'{driver}:3:0: error: policy {bad[0]}'
            return 0, ''
        finally:
            with self.lock:
                self.running -= 1


def run_audit(modules, fake, **kwargs):
    out = io.StringIO()
    with mock.patch.object(audit.subprocess, 'run', fake), \
            mock.patch.object(audit, 'launch_lean', fake.launch), \
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
    def setUp(self):
        # The fakes stand for directly started Lean processes, which are killed through
        # `kill()`, on every platform. The Lake route is tested where named.
        listing = mock.patch.object(audit, 'LIST_ENVIRONMENT', True)
        listing.start()
        self.addCleanup(listing.stop)

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

    def test_a_later_group_does_not_start_before_an_earlier_one(self):
        release = threading.Event()
        real_launch = audit.Admission.launch

        def launch(self, index, first, start, real_launch=real_launch):
            if index == 0 and first:
                release.wait(10)  # group 0's worker is slow to reach admission
            return real_launch(self, index, first, start)

        fake = FakeLean()
        result = {}

        def run():
            with mock.patch.object(audit.Admission, 'launch', launch):
                result['audit'], _ = run_audit(names(16, 2), fake, batch_size=8, workers=2)

        worker = threading.Thread(target=run)
        worker.start()
        time.sleep(0.3)
        self.assertEqual(fake.calls, 0, 'group 1 started before group 0')
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

    def test_no_batch_starts_while_a_failed_batch_is_classified(self):
        # Group 0 fails while group 1 runs; group 1's worker is free while group 0's output is
        # classified, and must not start group 2 before the failure is recorded.
        classifying = threading.Event()
        real_classify = audit.only_import_collision

        def classify(output, real_classify=real_classify):
            if 'L.Bad' in output:
                classifying.set()
                time.sleep(0.5)
            return real_classify(output)

        both = threading.Event()
        fake = FakeLean(hold={'L.Bad': both, 'L.M08': classifying}, launched=lambda calls: calls == 2 and both.set())
        with mock.patch.object(audit, 'only_import_collision', classify):
            with self.assertRaisesRegex(audit.AuditFailure, 'L.Bad'):
                run_audit(names(32, 2, bad=[(0, 'L.Bad')]), fake, batch_size=8, workers=2)
        self.assertEqual(sorted(fake.order), ['L.Bad', 'L.M08'])

    def test_failure_cancels_groups_not_started(self):
        modules = names(32, 2, bad=[(0, 'L.Bad')])
        fake = FakeLean(delay=0.1)
        with self.assertRaises(audit.AuditFailure):
            run_audit(modules, fake, batch_size=4, workers=1)
        self.assertEqual(fake.calls, 1)

    def test_one_worker_stops_at_an_interrupt(self):
        # SIGINT reaches the coordinating thread while the only batch runs; that batch is killed.
        previous = signal.signal(signal.SIGINT, signal.default_int_handler)  # even if started ignored
        self.addCleanup(signal.signal, signal.SIGINT, previous)
        if hasattr(signal, 'pthread_sigmask'):  # or blocked
            mask = signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGINT})
            self.addCleanup(signal.pthread_sigmask, signal.SIG_SETMASK, mask)
        never = threading.Event()
        fake = FakeLean(hold={'L.M000': never},
                        launched=lambda calls: threading.Timer(0.2, os.kill, (os.getpid(), signal.SIGINT)).start())
        began = time.monotonic()
        with self.assertRaises(KeyboardInterrupt):
            run_audit(MODULES, fake, batch_size=8, workers=1)
        self.assertLess(time.monotonic() - began, 5)
        self.assertEqual(fake.order, ['L.M000'])
        self.assertTrue(fake.processes['L.M000'].killed.is_set())

    def test_cancellation_starts_nothing_more_and_stops_what_runs(self):
        admission = audit.Admission(gated=False)
        first = FakeProcess(None, [])
        self.assertIs(admission.launch(0, True, lambda: first), first)
        waiting = {}

        def wait_for_group_2():
            try:
                admission.launch(2, True, lambda: FakeProcess(None, []))  # waits: group 1 has not started
                waiting['result'] = 'started'
            except audit.SkippedGroup:
                waiting['result'] = 'skipped'

        thread = threading.Thread(target=wait_for_group_2)
        thread.start()
        time.sleep(0.1)
        self.assertNotIn('result', waiting)
        admission.cancel()
        thread.join(10)
        self.assertEqual(waiting['result'], 'skipped')
        self.assertTrue(first.killed.is_set())
        for index, first_batch in ((1, True), (0, False)):
            with self.assertRaises(audit.SkippedGroup):
                admission.launch(index, first_batch, lambda: FakeProcess(None, []))

    def test_a_failure_stops_the_later_groups_running_batches(self):
        # Group 1 fails while group 2 runs (and would run for ever); group 0 runs to its end.
        modules = names(24, 2, bad=[(8, 'L.Bad')])
        never, started = threading.Event(), threading.Event()
        fake = FakeLean(hold={'L.Bad': started, 'L.M16': never}, launched=lambda calls: calls == 3 and started.set())
        began = time.monotonic()
        with self.assertRaisesRegex(audit.AuditFailure, 'L.Bad'):
            run_audit(modules, fake, batch_size=8, workers=3)
        self.assertLess(time.monotonic() - began, 5)
        self.assertTrue(fake.processes['L.M16'].killed.is_set())
        self.assertFalse(fake.processes['L.M00'].killed.is_set())

    def test_an_interrupt_while_submitting_cancels_the_queued_groups(self):
        # Groups 0 and 1 run and groups 2-3 wait in the queue when submitting group 4 is interrupted.
        running, never = threading.Event(), threading.Event()
        fake = FakeLean(hold={'L.M000': never, 'L.M008': never},
                        launched=lambda calls: calls == 2 and running.set())
        real_submit = concurrent.futures.ThreadPoolExecutor.submit
        submitted = []

        def submit(pool, *args, **kwargs):
            if len(submitted) == 4:
                running.wait(10)
                raise KeyboardInterrupt
            submitted.append(args[1])
            return real_submit(pool, *args, **kwargs)

        with mock.patch.object(concurrent.futures.ThreadPoolExecutor, 'submit', submit):
            with self.assertRaises(KeyboardInterrupt):
                run_audit(MODULES, fake, batch_size=8, workers=2)
        self.assertEqual(sorted(fake.order), ['L.M000', 'L.M008'])
        self.assertTrue(all(process.killed.is_set() for process in fake.processes.values()))

    def test_a_timeout_stops_lean_itself(self):
        # Each batch's process is Lean, not a Lake wrapper, so the timeout ends it.
        with tempfile.TemporaryDirectory() as folder:
            marker = Path(folder, 'still-running')
            lean = Path(folder, 'lean')
            lean.write_text('#!/bin/sh\nsleep 2\ntouch still-running\n')  # runs in `folder`
            lean.chmod(0o755)
            real_run = subprocess.run

            def run(command, **kwargs):
                if command == ['lake', 'env', 'env', '-0']:
                    kwargs['stdout'].write(listing({**os.environ, 'LEAN': str(lean)}))  # as Lake lists it
                    return subprocess.CompletedProcess(command, 0, None, b'')
                return real_run(command, **kwargs)

            began = time.monotonic()
            with mock.patch.object(audit.subprocess, 'run', run), \
                    mock.patch.object(audit, 'BATCH_TIMEOUT', 0.5), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(subprocess.TimeoutExpired):
                    audit.audit(Path(folder), ['L.A', 'L.B'], '', batch_size=1, workers=1)
            # The shell's `sleep` still holds the output pipe: the audit does not wait for it.
            self.assertLess(time.monotonic() - began, 1.5)
            time.sleep(2.5)
            self.assertFalse(marker.exists(), 'Lean kept running after the timeout')

    def test_no_batch_starts_while_a_timed_out_batch_is_reaped(self):
        # Group 0 times out while group 1 runs; while group 0 is reaped, group 1's free worker
        # must not start group 2.
        reaping = threading.Event()

        both = threading.Event()

        class SlowReap(FakeProcess):
            def communicate(self, timeout=None):
                if self.command and 'L.Bad' in Path(self.command[-1]).read_text():
                    both.wait(10)  # group 1 runs too
                    raise subprocess.TimeoutExpired(self.command, timeout)
                return super().communicate(timeout)

            def wait(self):
                reaping.set()
                time.sleep(0.5)
                return self.returncode

        fake = FakeLean(hold={'L.M08': reaping}, launched=lambda calls: calls == 2 and both.set())
        real_launch = fake.launch

        def launch(command, root, environment):
            process = real_launch(command, root, environment)
            slow = SlowReap(fake, command)
            fake.processes[next(name for name, value in fake.processes.items() if value is process)] = slow
            return slow

        fake.launch = launch
        with self.assertRaises(subprocess.TimeoutExpired):
            run_audit(names(32, 2, bad=[(0, 'L.Bad')]), fake, batch_size=8, workers=2)
        self.assertEqual(sorted(fake.order), ['L.Bad', 'L.M08'])

    def test_a_real_batch_is_killed_through_its_pidfd_or_kill(self):
        admission = audit.Admission(gated=False)
        process = admission.launch(0, True, lambda: subprocess.Popen(['sleep', '30']))
        pidfd = admission.running[process][1]
        if pidfd_supported():
            self.assertIsNotNone(pidfd)
        began = time.monotonic()
        admission.cancel()
        self.assertEqual(process.wait(5), -signal.SIGKILL)
        self.assertLess(time.monotonic() - began, 5)
        admission.finished(process)
        self.assertNotIn(process, admission.running)
        if pidfd is not None:
            with self.assertRaises(OSError):
                os.fstat(pidfd)  # closed
        admission.stop(process)  # unregistered: nothing to signal

    def test_without_an_environment_listing_batches_run_through_lake(self):
        fake = FakeLean(PAIRS, delay=0.02)
        with mock.patch.object(audit, 'LIST_ENVIRONMENT', False):
            result, _ = run_audit(MODULES, fake, batch_size=8, workers=3)
            sequential, _ = run_audit(MODULES, FakeLean(PAIRS), batch_size=8, workers=1)
        self.assertEqual(result['checkedModules'], MODULES)
        self.assertEqual({k: v for k, v in result.items() if k != 'workers'},
                         {k: v for k, v in sequential.items() if k != 'workers'})
        self.assertEqual(fake.probes, 1)  # `lake env true`, once, before the batches run at once

    def test_through_lake_a_batch_is_killed_with_its_process_group(self):
        with tempfile.TemporaryDirectory() as folder:
            marker = Path(folder, 'child-survived')
            admission = audit.Admission(gated=False)
            script = 'sleep 1 && touch child-survived & wait'  # runs in `folder`
            with mock.patch.object(audit, 'LIST_ENVIRONMENT', False):
                process = admission.launch(0, True, lambda: audit.launch_lean(['sh', '-c', script], Path(folder), None))
                time.sleep(0.2)
                admission.cancel()
                process.wait(5)
                process.stdout.close()
                admission.finished(process)
            time.sleep(1.5)
            self.assertFalse(marker.exists(), "the batch's child outlived it")


    def test_termination_signals_interrupt_the_audit(self):
        saved = {number: signal.getsignal(number) for number in (signal.SIGTERM, signal.SIGHUP)}
        for number, handler in saved.items():
            self.addCleanup(signal.signal, number, handler)
        signal.signal(signal.SIGTERM, signal.SIG_DFL)
        signal.signal(signal.SIGHUP, signal.SIG_IGN)  # as under nohup
        if hasattr(signal, 'pthread_sigmask'):  # even if the suite started with SIGTERM blocked
            mask = signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGTERM})
            self.addCleanup(signal.pthread_sigmask, signal.SIG_SETMASK, mask)
        seen = {}
        never = threading.Event()

        def launched(calls):
            seen['SIGTERM'] = signal.getsignal(signal.SIGTERM)
            seen['SIGHUP'] = signal.getsignal(signal.SIGHUP)
            threading.Timer(0.2, os.kill, (os.getpid(), signal.SIGTERM)).start()

        fake = FakeLean(hold={'L.M000': never}, launched=launched)
        with self.assertRaises(KeyboardInterrupt):
            run_audit(MODULES, fake, batch_size=8, workers=1)
        self.assertIs(seen['SIGTERM'], signal.default_int_handler)
        self.assertIs(seen['SIGHUP'], signal.SIG_IGN)
        self.assertTrue(fake.processes['L.M000'].killed.is_set())
        # The handlers come back after the audit, and importing the module changes none.
        self.assertIs(signal.getsignal(signal.SIGTERM), signal.SIG_DFL)
        self.assertIs(signal.getsignal(signal.SIGHUP), signal.SIG_IGN)

    def test_override_of_one_runs_the_batches_one_by_one(self):
        fake = FakeLean(PAIRS, delay=0.02)
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: '1'}):
            result, _ = run_audit(MODULES, fake, batch_size=8)
        self.assertEqual(fake.peak, 1)
        self.assertEqual(result['workers'], 1)
        self.assertEqual(result['checkedModules'], MODULES)

    def test_lake_environment_failures_are_audit_failures(self):
        def probe(status, content=b'', errors=b''):
            def run(command, **kwargs):
                kwargs['stdout'].write(content)
                return subprocess.CompletedProcess(command, status, None, errors)
            return run

        secret = listing({'LEAN': FAKE_LEAN, 'SECRET': 'hunter2'})
        for run in (probe(1, secret, b'error: no workspace'), probe(0), probe(0, b'hunter2\0' + secret),
                    probe(0, listing({'PATH': '', 'SECRET': 'hunter2'})),
                    probe(0, listing({'PATH': '/nowhere', 'SECRET': 'hunter2'}))):
            with mock.patch.object(audit.subprocess, 'run', run), \
                    mock.patch.object(audit, 'available_memory', return_value=PLENTY):
                with self.assertRaises(audit.AuditFailure) as caught:
                    audit.audit(Path('.'), ['L.A'], '', workers=1)
            self.assertNotIn('hunter2', str(caught.exception))

    def test_the_environment_round_trips_undecodable_bytes(self):
        content = b'LEAN=/fake/lean\0ODD=caf\xe9\0MULTI=a\nb=c\0'
        with mock.patch.object(audit.subprocess, 'run',
                               lambda command, **kwargs: kwargs['stdout'].write(content)
                               and subprocess.CompletedProcess(command, 0, None, b'')):
            lean, environment = audit.lean_environment(Path('.'))
        self.assertEqual(lean, '/fake/lean')
        self.assertEqual(os.fsencode(environment['ODD']), b'caf\xe9')
        self.assertEqual(environment['MULTI'], 'a\nb=c')

    def test_the_environment_never_reaches_the_output(self):
        fake = FakeLean(pairs=[('L.M000', 'L.M001')])
        out = io.StringIO()
        with contextlib.redirect_stderr(out):
            _, lines = run_audit(names(16), fake, batch_size=8, workers=2)
        self.assertNotIn('hunter2', '\n'.join(lines) + out.getvalue())

    def gated_run(self, memory, workers=3, settle=0.3, hold=0.6, **kwargs):
        fake = FakeLean(delay=hold)
        out = io.StringIO()
        with mock.patch.object(audit.subprocess, 'run', fake), \
                mock.patch.object(audit, 'launch_lean', fake.launch), \
                mock.patch.object(audit, 'available_memory', side_effect=memory), \
                mock.patch.object(audit, 'SETTLE_SECONDS', settle), contextlib.redirect_stdout(out):
            result = audit.audit(Path('.'), names(24), '-- checker\n', batch_size=8, workers=workers,
                                 memory_gate=True, **kwargs)
        self.assertEqual(result['checkedModules'], names(24))
        return fake

    def test_the_gate_admits_at_once_with_room_for_every_running_batch(self):
        fake = self.gated_run(lambda: 10 * audit.BATCH_MEMORY)
        self.assertEqual(fake.peak, 3)
        self.assertLess(max(fake.started) - min(fake.started), 0.3)

    def test_the_gate_waits_for_the_latest_batch_to_settle_when_memory_is_tight(self):
        fake = self.gated_run(lambda: int(1.5 * audit.BATCH_MEMORY))
        gaps = [later - earlier for earlier, later in zip(fake.started, fake.started[1:])]
        self.assertTrue(all(gap >= 0.3 for gap in gaps), gaps)
        self.assertGreater(fake.peak, 1)

    def test_the_gate_adds_no_batch_without_memory_or_a_reading(self):
        for reading in (lambda: audit.BATCH_MEMORY - 1, lambda: None):
            fake = self.gated_run(reading, hold=0.1)
            self.assertEqual(fake.peak, 1)

    def test_the_gate_is_off_for_an_explicit_count(self):
        all_started = threading.Event()
        fake = FakeLean(hold={'L.M000': all_started, 'L.M008': all_started},
                        launched=lambda calls: calls == 3 and all_started.set())
        with mock.patch.dict(os.environ, {audit.WORKERS_VARIABLE: '3'}), \
                mock.patch.object(audit.subprocess, 'run', fake), mock.patch.object(audit, 'launch_lean', fake.launch), \
                mock.patch.object(audit, 'available_memory', return_value=0), contextlib.redirect_stdout(io.StringIO()):
            result = audit.audit(Path('.'), names(24), '-- checker\n', batch_size=8)
        self.assertEqual((result['workers'], fake.peak), (3, 3))

    def test_a_slow_memory_sample_does_not_delay_recording_a_failure(self):
        # Group 1 samples memory while group 0 runs; group 0 fails during that sample.
        sampling, recorded = threading.Event(), threading.Event()
        real_fail = audit.Admission.fail

        def fail(self, index, real_fail=real_fail):
            real_fail(self, index)
            recorded.set()

        def slow_sample():
            sampling.set()
            recorded.wait(10)  # with the sample under the lock, fail() would wait here
            return 10 * audit.BATCH_MEMORY

        fake = FakeLean(hold={'L.Bad': sampling})
        with mock.patch.object(audit.Admission, 'fail', fail):
            with self.assertRaisesRegex(audit.AuditFailure, 'L.Bad'):
                out = io.StringIO()
                with mock.patch.object(audit.subprocess, 'run', fake), \
                        mock.patch.object(audit, 'launch_lean', fake.launch), \
                        mock.patch.object(audit, 'available_memory', slow_sample), contextlib.redirect_stdout(out):
                    audit.audit(Path('.'), names(16, 2, bad=[(0, 'L.Bad')]), '', batch_size=8, workers=2,
                                memory_gate=True)
        self.assertTrue(recorded.is_set())
        self.assertEqual(fake.order, ['L.Bad'])

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

        def fake_open(path, mode='r', *args, **kwargs):
            if str(path) in files:
                content = files[str(path)]
                if isinstance(content, str):
                    content = content.encode('utf-8', 'surrogateescape')
                return io.BytesIO(content) if 'b' in mode else io.StringIO(content.decode('utf-8', 'replace'))
            if str(path).startswith('/proc/'):
                raise FileNotFoundError(path)
            return real_open(path, mode, *args, **kwargs)

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
            (group / 'memory.high').write_text('max\n')
            (group / 'memory.current').write_text(f'{used * self.gib}\n')
            (group / 'memory.stat').write_text(f'anon 1\ninactive_file {inactive * self.gib}\n')

    @staticmethod
    def escape(path):
        """A path as /proc/self/mountinfo writes it."""
        return ''.join(f'\\{ord(c):03o}' if c in ' \t\n\\' else c for c in str(path))

    def mount_line(self, number, root, mount):
        return (f'{number} 24 0:{number} {self.escape(root)} {self.escape(mount)} rw,nosuid shared:9 '
                '- cgroup2 cgroup2 rw\n')

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

    def test_memory_high_counts_when_tighter(self):
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'': (None, 1, 0), 'job': (16, 2, 0)})
            Path(folder, 'job', 'memory.high').write_text(f'{8 * self.gib}\n')
            files = {'/proc/self/cgroup': '0::/job\n', '/proc/self/mountinfo': self.mountinfo('/', folder)}
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)
            Path(folder, 'job', 'memory.high').write_text(f'{32 * self.gib}\n')
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 14 * self.gib)

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
                    real_read = audit.read_kernel_bytes

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
                        stack.enter_context(mock.patch.object(audit, 'read_kernel_bytes', read))
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
            for name in ('memory.max', 'memory.high', 'memory.current', 'memory.stat'):
                Path(folder, name).unlink(missing_ok=True)
            files = {'/proc/self/cgroup': '0::/job\n', '/proc/self/mountinfo': self.mountinfo('/', folder)}
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)

    def test_a_mount_point_with_a_space(self):
        with tempfile.TemporaryDirectory() as parent:
            folder = Path(parent, 'cgroup mount')
            self.tree(folder, {'': (None, 1, 0), 'my job': (8, 2, 0)})
            files = {'/proc/self/cgroup': '0::/my job\n', '/proc/self/mountinfo': self.mountinfo('/', folder)}
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)

    def test_records_split_only_at_line_feeds(self):
        # U+2028 is a line break to str.splitlines(), not to the kernel.
        with tempfile.TemporaryDirectory() as folder:
            self.tree(folder, {'': (None, 1, 0), 'job': (None, 1, 0), 'job\u2028small': (8, 2, 0)})
            files = {'/proc/self/cgroup': '0::/job\u2028small\n', '/proc/self/mountinfo': self.mountinfo('/', folder)}
            with self.proc(files):
                self.assertEqual(audit.cgroup_headroom(), 6 * self.gib)

    def test_ambiguous_or_escaping_memberships_count_as_no_headroom(self):
        with tempfile.TemporaryDirectory() as parent:
            view = Path(parent, 'view')
            self.tree(view, {'': (None, 1, 0), 'job': (8, 2, 0)})
            self.tree(parent, {'outside': (None, 1, 0)})
            for cgroup in ('0::/../outside\n', '0::/job/../..\n', '0::/job\n0::/other\n', '0::job\n',
                           '0::/job\nnonsense\n'):
                with self.subTest(cgroup=cgroup), self.proc({'/proc/self/cgroup': cgroup,
                                                             '/proc/self/mountinfo': self.mountinfo('/', view)}):
                    self.assertEqual(audit.cgroup_headroom(), 0)

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
