"""Guard regression: generic controls imply current parser fixture acceptance."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('generic_frontend_controls', root/'scripts/h55/module-times/generic_frontend_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class GenericFrontendControls(unittest.TestCase):
    def test_scope_roster_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                path = module.PREFIX + name + '.lean'
                source = base / path
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'candidate': {'path':path, 'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}, 'status':'no-supplied-current-reference'})
            result = {r['candidate']['path']:r for r in module.classify(base, rows)}
            get = lambda name: result[module.PREFIX + name + '.lean']
            self.assertIn('not actual parser-table validation', get('Core')['role'])
            self.assertIn('not included', get('FixtureTable')['driver'])
            self.assertIn('not full parser', get('CoreControls')['expected_outcome'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            (base / rows[0]['candidate']['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
