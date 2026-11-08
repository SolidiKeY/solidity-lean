"""Guard the separate v2 pin and observable runner refusal paths; no v1 proof claim."""
import importlib.util
import json
import os
from pathlib import Path
import runpy
import signal
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT/'scripts/h62/item4/generic-v08'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('width_v2', SCRIPTS/'reproduce-width-v2.py')
v2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v2)


class Route(unittest.TestCase):
    def test_pin_rejects_v1_and_wrong_commit(self):
        exact = 'Lean (version 4.24.0, commit ' + v2.COMMIT + ', Release)'
        self.assertTrue(v2.version_matches(exact))
        self.assertFalse(v2.version_matches(exact.replace('4.24.0', '4.35.0')))
        self.assertFalse(v2.version_matches(exact.replace(v2.COMMIT, '0'*40)))

    def test_receipts_cannot_overwrite_or_enter_checkout(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)/'repo'
            repo.mkdir()
            for output in (repo, repo/'receipts', Path(folder)):
                with self.assertRaises(ValueError):
                    v2.checked_output(repo, output)
            self.assertEqual(v2.checked_output(repo, Path(folder)/'fresh'), Path(folder)/'fresh')

    def test_import_order_cycle_and_missing_refusal(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = Path(folder)
            (repo/'Solidity').mkdir()
            (repo/'Solidity/A.lean').write_text('import Solidity.B\n')
            (repo/'Solidity/B.lean').write_text('def b := 0\n')
            self.assertEqual(v2.dependency_order(repo, 'Solidity.A'), ['Solidity.B', 'Solidity.A'])
            (repo/'Solidity/B.lean').write_text('import Solidity.A\n')
            with self.assertRaisesRegex(ValueError, 'cyclic'):
                v2.dependency_order(repo, 'Solidity.A')
            (repo/'Solidity/B.lean').unlink()
            with self.assertRaisesRegex(ValueError, 'missing'):
                v2.dependency_order(repo, 'Solidity.A')

    def test_commands_enforce_existing_bounds(self):
        cmd = v2.bounded_command(Path('/pin/bin/lean'), Path('/offgit/record'), 17, ['x.lean'], lease_fd=3)
        self.assertIn('--aggregate', cmd)
        self.assertEqual(cmd[-3:], ['-j1', '--tstack=131072', 'x.lean'])
        self.assertIn('/pin/bin/lean', cmd)
        for seconds in (0, 301):
            with self.assertRaises(ValueError):
                v2.bounded_command(Path('/pin/bin/lean'), Path('/offgit/record'), seconds, [], lease_fd=3)

    def test_shared_deadline_blocks_late_success(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            repo = root/'repo'
            paths = ['lean-toolchain', v2.TARGET, 'Solidity/Source/Types.lean',
                     'scripts/h62/item4/generic-v08/census.py',
                     'scripts/h62/item4/generic-v08/bounded.py',
                     'scripts/h62/item4/generic-v08/width_resources.py',
                     'scripts/h62/item4/generic-v08/width_scope.py',
                     'scripts/h62/item4/generic-v08/reproduce-width-v2.py',
                     'scripts/h62/item4/generic-v08/check-width-v2.sh']
            for name in paths:
                path = repo/name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('leanprover/lean4:v4.24.0' if name == 'lean-toolchain' else '')
            tool = root/'tool'
            (tool/'bin').mkdir(parents=True)
            (tool/'bin/lean').write_text('')
            output = root/'fresh'
            version = 'Lean (version 4.24.0, commit ' + v2.COMMIT + ', Release)'
            with patch.object(v2, 'require_scope', return_value={'memory_max_bytes': 12*1024**3, 'memory_swap_max_bytes': 0, 'host_reserve_bytes': 12*1024**3}), patch.object(v2, 'ROOT', repo), patch.object(v2.subprocess, 'check_output', return_value=version), patch.object(v2, 'run_monitor', return_value=Mock(returncode=0)) as run, patch.object(v2.fcntl, 'flock'), patch.object(v2.time, 'monotonic', side_effect=[0, 1, 301]):
                result = v2.main(['--toolchain', str(tool), '--output', str(output)])
            self.assertEqual(result, 1)
            self.assertEqual(run.call_count, 1)
            self.assertEqual(len(run.call_args.kwargs['pass_fds']), 1)
            self.assertFalse((output/'summary.json').exists())
            self.assertIn('deadline', (output/'STOP.txt').read_text())
            self.assertEqual(json.loads((output/'inputs-before.json').read_text()),
                             json.loads((output/'inputs-after.json').read_text()))



class Refusal(unittest.TestCase):
    def exercise(self, swap=0, reserve=16*1024**3, rows=None, seconds=300,
                 measurement_error=None, aggregate=True, finished=False, interrupt_signal=False, owned_status_error=None, scope_max=None):
        rows = rows or {}
        original_read = Path.read_text
        original_glob = Path.glob
        original_iterdir = Path.iterdir
        def read(path, *args, **kwargs):
            value = str(path)
            if value == '/proc/meminfo':
                return f'MemAvailable: {reserve//1024} kB\nSwapTotal: {swap} kB\n'
            if value == '/proc/self/cgroup':
                return '0::/\n'
            if value == '/sys/fs/cgroup/memory.max':
                return str(scope_max if scope_max is not None else (12 if aggregate else 16)*1024**3)
            if value in ('/sys/fs/cgroup/memory.swap.max','/sys/fs/cgroup/memory.swap.current'):
                return '0'
            if value == '/sys/fs/cgroup/memory.current':
                return '0'
            if value == f'/proc/{os.getpid()}/status':
                if measurement_error is not None:
                    raise measurement_error('measurement failed')
                if interrupt_signal:
                    signal.getsignal(signal.SIGTERM)(signal.SIGTERM, None)
            if value in rows:
                if owned_status_error is not None and value == f'/proc/{owned_status_error}/status':
                    raise PermissionError('live owned status unreadable')
                return rows[value]
            if value.startswith('/proc/') and value.endswith('/stat'):
                key = '/'.join(value.split('/')[:-1])+'/status'
                if key not in rows:
                    raise FileNotFoundError(value)
                fields = dict(x.split(':', 1) for x in rows[key].splitlines() if ':' in x)
                return value.split('/')[2]+' (lean) S '+fields['PPid'].strip()
            if value.startswith('/proc/321/') and value.endswith('/status'):
                raise FileNotFoundError(value)
            if '/task/' in value and value.endswith('/children'):
                parent = int(value.split('/')[2])
                return ' '.join(p.split('/')[2] for p, data in rows.items()
                    if int(dict(x.split(':', 1) for x in data.splitlines() if ':' in x)['PPid']) == parent)
            return original_read(path, *args, **kwargs)
        def glob(path, pattern):
            return iter(Path(p) for p in rows) if str(path) == '/proc' else original_glob(path, pattern)
        def iterdir(path):
            value = str(path)
            if value == '/proc':
                return iter(Path('/proc')/p.split('/')[2] for p in rows)
            if value.startswith('/proc/') and value.endswith('/task'):
                pid = value.split('/')[2]
                return iter([path/pid])
            return original_iterdir(path)
        def liveness(pid, _signal):
            if f'/proc/{pid}/status' not in rows:
                raise ProcessLookupError(pid)
        with tempfile.TemporaryDirectory() as folder:
            record = Path(folder)/'record.json'
            proc = Mock(pid=321, returncode=0 if finished else -15)
            proc.poll.return_value = 0 if finished else None
            proc.wait.return_value = proc.returncode
            with patch.object(sys, 'argv', ['bounded', '--record', str(record), '--seconds', str(seconds), *(['--aggregate'] if aggregate else []), '--', 'lean', '-j1', 'x.lean']), patch.object(Path, 'read_text', read), patch.object(Path, 'glob', glob), patch.object(Path, 'iterdir', iterdir), patch('os.kill', side_effect=liveness), patch('subprocess.Popen', return_value=proc) as spawn, patch('os.killpg', side_effect=ProcessLookupError if finished else None) as kill:
                with self.assertRaises(SystemExit):
                    runpy.run_path(str(SCRIPTS/'bounded.py'), run_name='__main__')
                result = json.loads(record.read_text()) if record.exists() else None
                return result, spawn.called, kill.call_args_list

    def test_swap_and_low_reserve_refuse_before_spawn(self):
        for options in ({'swap': 1024}, {'reserve': 3*1024**3}):
            result, spawned, _ = self.exercise(**options)
            self.assertIsNone(result)
            self.assertFalse(spawned)

    def test_unisolated_v2_scope_refuses_before_spawn(self):
        for maximum in (16*1024**3, 'max'):
            result, spawned, _ = self.exercise(scope_max=maximum)
            self.assertIsNone(result)
            self.assertFalse(spawned)

    def test_aggregate_stop_is_observable(self):
        row = f'Name: lean\nPPid: 1\nVmRSS: {12*1024**2+1} kB\n'
        result, spawned, kills = self.exercise(rows={'/proc/321/status': row})
        self.assertTrue(spawned)
        self.assertEqual(result['stop'], 'aggregate-rss')
        self.assertGreater(result['peak_sampled_aggregate_rss'], 12*1024**3)
        self.assertTrue(any(c.args == (321, signal.SIGTERM) for c in kills))

    def test_timeout_stop_is_observable(self):
        result, spawned, kills = self.exercise(seconds=0)
        self.assertTrue(spawned)
        self.assertEqual(result['stop'], 'timeout')
        self.assertTrue(any(c.args == (321, signal.SIGTERM) for c in kills))

    def test_measurement_errors_cleanup_and_record(self):
        for error in (OSError, KeyboardInterrupt):
            result, spawned, kills = self.exercise(measurement_error=error)
            self.assertTrue(spawned)
            self.assertEqual(result['stop'], 'monitor-error')
            self.assertIn(error.__name__, result['monitor_error'])
            self.assertTrue(any(c.args == (321, signal.SIGTERM) for c in kills))

    def test_live_owned_status_failure_cleans_worker(self):
        rows = {'/proc/321/status': 'Name: lean\nPPid: 1\nVmRSS: 1 kB\n',
                '/proc/322/status': 'Name: lean\nPPid: 321\nVmRSS: 1 kB\n'}
        for pid in (321, 322):
            result, _, kills = self.exercise(rows=rows, owned_status_error=pid)
            self.assertEqual(result['stop'], 'monitor-error')
            self.assertIn('MeasurementError', result['monitor_error'])
            self.assertNotEqual(result['exit'], 0)
            self.assertTrue(any(c.args == (321, signal.SIGTERM) for c in kills))

    def test_monitor_signal_cleans_process_group(self):
        result, _, kills = self.exercise(interrupt_signal=True)
        self.assertEqual(result['stop'], 'monitor-error')
        self.assertIn('signal', result['monitor_error'])
        self.assertTrue(any(c.args == (321, signal.SIGTERM) for c in kills))

    def test_late_completion_cannot_pass(self):
        result, _, _ = self.exercise(seconds=0, finished=True)
        self.assertEqual(result['exit'], 0)
        self.assertEqual(result['stop'], 'timeout')

    def test_legacy_default_record_remains_unextended(self):
        result, _, _ = self.exercise(aggregate=False, finished=True)
        self.assertEqual(result['exit'], 0)
        self.assertIsNone(result['stop'])
        self.assertNotIn('peak_sampled_aggregate_rss', result)
        self.assertNotIn('monitor_error', result)

    def test_parallel_lean_stop_is_observable(self):
        rows = {'/proc/321/status': 'Name: lean\nPPid: 1\nVmRSS: 1 kB\n',
                '/proc/322/status': 'Name: lean\nPPid: 321\nVmRSS: 1 kB\n'}
        result, _, _ = self.exercise(rows=rows)
        self.assertEqual(result['stop'], 'parallel-lean')
        self.assertEqual(result['max_lean_processes'], 2)


if __name__ == '__main__':
    unittest.main()
