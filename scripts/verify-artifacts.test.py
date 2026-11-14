import pathlib
import tempfile
import unittest
from verify_artifacts import runtime_aliases

class RuntimeAliases(unittest.TestCase):
    def test_exact_aliases_and_refusals(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = pathlib.Path(scratch)
            compiled, runtime, frozen = {}, {}, {}
            for i, module in enumerate(['Dependency', 'Root']):
                old, new = root / f'old{i}.olean', root / f'new{i}.olean'
                old.write_bytes(module.encode()); new.write_bytes(old.read_bytes())
                compiled[module], runtime[module] = [str(old)], [str(new)]
                frozen[str(old)] = old.read_bytes()
            self.assertEqual(len(runtime_aliases(compiled, runtime, frozen)), 2)
            for module in compiled:
                path = pathlib.Path(runtime[module][0]); original = path.read_bytes()
                path.write_bytes(b'different artifact')
                with self.assertRaisesRegex(ValueError, 'contents differ'):
                    runtime_aliases(compiled, runtime, frozen)
                path.write_bytes(original)
            with self.assertRaisesRegex(ValueError, 'closure differs'):
                runtime_aliases(compiled, {'Root': runtime['Root']}, frozen)
            wrong_role = root / 'new.ir'; wrong_role.write_bytes(b'Dependency')
            with self.assertRaisesRegex(ValueError, 'roles differ'):
                runtime_aliases(compiled, {**runtime, 'Dependency': [str(wrong_role)]}, frozen)
            with self.assertRaisesRegex(ValueError, 'ambiguous'):
                runtime_aliases(compiled, {**runtime, 'Root': runtime['Root'] * 2}, frozen)

if __name__ == '__main__':
    unittest.main()
