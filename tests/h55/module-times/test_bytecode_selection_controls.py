"""Guard regression: premise-domain or local decoder fixtures imply full adequacy."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('bytecode_selection_controls', root/'scripts/h55/module-times/bytecode_selection_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class BytecodeSelectionControls(unittest.TestCase):
    def test_scope_state_and_source_binding(self):
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
            self.assertIn('not proof of original conclusion', get('HypothesisDomains')['role'])
            self.assertIn('not external Bridge agreement', get('RuntimePremiseWitness')['role'])
            self.assertIn('intentional reject-push impossibility', get('Witnesses')['role'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            with self.assertRaises(ValueError):
                module.classify(base, [{**rows[0], 'status':'referenced-static-only'}])
            (base / rows[0]['candidate']['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
