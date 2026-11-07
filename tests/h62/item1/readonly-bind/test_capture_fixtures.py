"""Guard held-workload admission, redirected roots and lost refusal artifacts."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location('capture_fixture_check',
    ROOT/'scripts/h62/item1/readonly-bind/check_capture_fixtures.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class ClosureRefusals(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def module(self, name, text):
        path = self.root/(name.replace('.', '/')+'.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_dependency_order_and_pins(self):
        self.module('Solidity.A', 'import Solidity.B\nimport Init\n')
        self.module('Solidity.B', '/- import '+m.HELD+' -/\n')
        order, pins = m.closure(self.root, ['Solidity.A'], {})
        self.assertEqual(order, ['Solidity/B.lean','Solidity/A.lean'])
        self.assertEqual(pins['Solidity/B.lean']['imports'], [])
        self.assertEqual(pins['Solidity/A.lean']['source_sha256'],
                         m.check.sha(self.root/'Solidity/A.lean'))

    def test_held_refused_before_missing_file_read(self):
        self.module('Solidity.A', 'import '+m.HELD+'\n')
        with self.assertRaisesRegex(ValueError, 'historically held'):
            m.closure(self.root, ['Solidity.A'], {})

    def test_cycle_missing_and_foreign(self):
        self.module('Solidity.A','import Solidity.B\n')
        self.module('Solidity.B','import Solidity.A\n')
        with self.assertRaisesRegex(ValueError, 'cyclic'):
            m.closure(self.root,['Solidity.A'],{})
        self.module('Solidity.A','import Solidity.Missing\n')
        with self.assertRaises(OSError):m.closure(self.root,['Solidity.A'],{})
        self.module('Solidity.A','import Foreign.Theory\n')
        with self.assertRaisesRegex(ValueError,'foreign'):
            m.closure(self.root,['Solidity.A'],{})

    def test_unsupported_import_refused(self):
        for text in ['import\n','import "Solidity.A"\n','import Solidity.A, Solidity.B\n']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                m.imports(text)

    def test_root_overrides_removed(self):
        ambient={'PATH':'retained', 'LEAN_SYSROOT':'wrong-root',
                 'LEAN_PATH':'shared-cache', 'LEAN_SRC_PATH':'wrong-source',
                 'LEAN_NUM_THREADS':'99','ELAN_TOOLCHAIN':'wrong-toolchain'}
        env=m.isolated_environment(ambient, self.root/'private')
        self.assertEqual(env['PATH'],'retained')
        self.assertEqual(env['LEAN_PATH'],str(self.root/'private'))
        self.assertEqual(env['LEAN_SYSROOT'],str(m.check.LEAN.resolve().parent.parent))
        self.assertEqual(env['LEAN_NUM_THREADS'],'1')
        self.assertNotIn('ELAN_TOOLCHAIN',env)
        self.assertNotIn('LEAN_SRC_PATH',env)

    def test_object_restored_after_control_and_failure(self):
        path=self.root/'private.olean';path.write_bytes(b'original object')
        def absent():
            self.assertFalse(path.exists())
            return 'refused'
        self.assertEqual(m.without_object(path,absent),'refused')
        self.assertEqual(path.read_bytes(),b'original object')
        def broken():
            self.assertFalse(path.exists())
            raise RuntimeError('test interruption')
        with self.assertRaises(RuntimeError):m.without_object(path,broken)
        self.assertEqual(path.read_bytes(),b'original object')

    def test_current_profile_inventory(self):
        order, pins=m.closure(ROOT,m.TARGETS,m.EXTRAS)
        self.assertNotIn(m.HELD.replace('.','/')+'.lean',order)
        self.assertEqual(set(order)|set(m.EXTRAS),set(pins))
        self.assertEqual(len(set(m.expected_theorems(ROOT))),38)


if __name__=='__main__':unittest.main()
