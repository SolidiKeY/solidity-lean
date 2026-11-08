"""Guard stale compiled-import substitution and unplanned cache fallback."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('fresh_native_controls', Path(__file__).with_name('rebuild_native_closure.py'))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

class FreshNativeControls(unittest.TestCase):
    def test_replaced_object_before_child_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp)
            obj = lib / 'A.olean'
            obj.write_bytes(b'compiled-A')
            expected = {str(obj): m.s.frame.sha(obj)}
            obj.write_bytes(b'substituted-A')
            with self.assertRaisesRegex(ValueError, 'differs from compiled'):
                m.direct_objects(['A'], lib, {'A'}, expected)

    def test_changed_object_during_child_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp)
            obj = lib / 'A.olean'
            obj.write_bytes(b'compiled-A')
            expected = {str(obj): m.s.frame.sha(obj)}
            used = m.direct_objects(['A'], lib, {'A'}, expected)
            obj.write_bytes(b'replaced-during-child')
            with self.assertRaisesRegex(ValueError, 'changed'):
                m.m.check.verify_hashes(used)

    def test_missing_or_unplanned_project_import_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp)
            with self.assertRaisesRegex(ValueError, 'missing staged'):
                m.direct_objects(['Solidity.A'], lib, {'Solidity.A'}, {})
            # An object outside the admitted plan cannot be promoted by presence.
            (lib / 'Extra.olean').write_bytes(b'foreign')
            for name in ['Extra', 'Solidity.Unplanned']:
                with self.assertRaisesRegex(ValueError, 'unplanned non-SDK'):
                    m.direct_objects([name], lib, set(), {})

    def test_only_explicit_sdk_families_are_trusted(self):
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp)
            self.assertEqual(m.direct_objects(['Init', 'Lean.Meta', 'Std.Data'], lib, set(), {}), {})
            with self.assertRaisesRegex(ValueError, 'unplanned'):
                m.direct_objects(['Mathlib'], lib, set(), {})

    def test_both_sibling_orders_are_present(self):
        first, second = m.sibling_probes()
        self.assertEqual(first, tuple(reversed(second)))
        self.assertEqual(set(first), {'Solidity.Evm.MachineV2', 'Solidity.Evm.Signed'})

if __name__ == '__main__':
    unittest.main()
