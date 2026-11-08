"""Synthetic controller tests; these never claim real scope admission or Lean success."""
import importlib.util
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT/'scripts/h62/item4/generic-v08'
sys.path.insert(0, str(SCRIPTS))
from width_scope import require_hard_scope as require_scope, require_scope as cloud_scope, ScopeError, CAP, HOST_RESERVE
spec = importlib.util.spec_from_file_location('v2_scope_driver', SCRIPTS/'reproduce-width-v2.py')
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


class Scope(unittest.TestCase):
    def fixture(self, folder):
        root = Path(folder)
        proc, cgroup = root/'proc', root/'cgroup'
        (proc/'self').mkdir(parents=True)
        (proc/'self/cgroup').write_text('0::/proof.scope\n')
        (proc/'meminfo').write_text(f'MemAvailable: {18*1024**2} kB\nSwapTotal: 0 kB\n')
        scope = cgroup/'proof.scope'
        scope.mkdir(parents=True)
        for name, value in {'memory.max': CAP, 'memory.current': 1024,
                            'memory.swap.max': 0, 'memory.swap.current': 0}.items():
            (scope/name).write_text(str(value))
        return proc, cgroup, scope

    def test_verified_kernel_caps_and_host_reserve(self):
        with tempfile.TemporaryDirectory() as folder:
            proc, cg, _ = self.fixture(folder)
            observation = require_scope(proc, cg)
            self.assertEqual(observation['memory_max_bytes'], CAP)
            self.assertEqual(observation['memory_swap_max_bytes'], 0)
            self.assertEqual(observation['host_reserve_bytes'], HOST_RESERVE)
            # Host reserve is not incorrectly required as free space inside the12GiB scope.
            self.assertLess(CAP-observation['memory_current_bytes'], HOST_RESERVE)

    def test_unlimited_or_unequal_memory_scope_refuses(self):
        for value in ('max', str(16*1024**3), str(8*1024**3)):
            with tempfile.TemporaryDirectory() as folder:
                proc, cg, scope = self.fixture(folder)
                (scope/'memory.max').write_text(value)
                with self.assertRaisesRegex(ScopeError, 'MemoryMax'):
                    require_scope(proc, cg)

    def test_nonzero_or_unlimited_swap_refuses(self):
        for value in ('max', '1'):
            with tempfile.TemporaryDirectory() as folder:
                proc, cg, scope = self.fixture(folder)
                (scope/'memory.swap.max').write_text(value)
                with self.assertRaisesRegex(ScopeError, 'MemorySwapMax'):
                    require_scope(proc, cg)

    def test_existing_swap_usage_refuses(self):
        with tempfile.TemporaryDirectory() as folder:
            proc, cg, scope = self.fixture(folder)
            (scope/'memory.swap.current').write_text('1')
            with self.assertRaises(ScopeError): require_scope(proc, cg)

    def test_missing_scope_observation_refuses(self):
        with tempfile.TemporaryDirectory() as folder:
            proc, cg, scope = self.fixture(folder)
            (scope/'memory.max').unlink()
            with self.assertRaisesRegex(ScopeError, 'unavailable'): require_scope(proc, cg)

    def test_twelve_gib_host_reserve_is_required(self):
        with tempfile.TemporaryDirectory() as folder:
            proc, cg, _ = self.fixture(folder)
            (proc/'meminfo').write_text(f'MemAvailable: {11*1024**2} kB\n')
            with self.assertRaisesRegex(ScopeError, 'host reserve'): require_scope(proc, cg)
            (proc/'meminfo').write_text(f'MemAvailable: {12*1024**2} kB\n')
            self.assertEqual(require_scope(proc, cg)['host_available_bytes'], HOST_RESERVE)

    def test_membership_traversal_refuses(self):
        with tempfile.TemporaryDirectory() as folder:
            proc, cg, _ = self.fixture(folder)
            (proc/'self/cgroup').write_text('0::/../escape\n')
            with self.assertRaises(ScopeError): require_scope(proc, cg)

    def test_driver_refuses_before_any_lean_invocation(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder)/'fresh'
            with patch.object(driver, 'require_scope', side_effect=ScopeError('no hard scope')), patch.object(driver.subprocess, 'check_output') as lean:
                with self.assertRaises(SystemExit):
                    driver.main(['--toolchain', '/unvalidated', '--output', str(output)])
            lean.assert_not_called()
            self.assertFalse(output.exists())


class CloudAdmission(unittest.TestCase):
    def test_h232_no_systemd_or_cgroup_required(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root/'meminfo').write_text('MemAvailable: 18874368 kB\nSwapTotal: 0 kB\n')
            observation = cloud_scope(root, root/'absent')
            self.assertFalse(observation['hard_scope'])
            self.assertEqual(observation['limitation'], 'no systemd scope on the cloud VM (H232)')

    def test_h232_measurement_and_swap_fail_closed(self):
        for content in ('MemAvailable: 18874368 kB\nSwapTotal: 1 kB\n', 'bad'):
            with tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                (root/'meminfo').write_text(content)
                with self.assertRaises(ScopeError): cloud_scope(root)


if __name__ == '__main__':
    unittest.main()
