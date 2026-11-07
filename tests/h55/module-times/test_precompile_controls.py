"""Guard regression: historical native failure or partial inventory counts as a pass."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

path = Path(__file__).resolve().parents[3] / 'scripts/h55/module-times/precompile_controls.py'
spec = importlib.util.spec_from_file_location('precompile_controls', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class PrecompileControls(unittest.TestCase):
    def test_driver_scope_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                relative = module.PREFIX + name + '.lean'
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'path': relative, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
            result = {r['candidate']['path']: r for r in module.classify(root, {'rows': rows})}
            probe = result[module.PREFIX + 'NativeModexpProbe.lean']
            self.assertIn('historical failure', probe['role'])
            self.assertIn('not in verify.py', probe['driver'])
            boundary = result[module.PREFIX + 'BoundaryVectors.lean']
            self.assertIn('successful exit', boundary['expected_outcome'])
            self.assertIn('not cryptographic', boundary['role'])
            self.assertIn('despite printed marker, exit 1', boundary['role'])
            self.assertIn('stops Lean MCP', boundary['effects'])
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows + rows[:1]})
            (root / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows})

if __name__ == '__main__':
    unittest.main()
