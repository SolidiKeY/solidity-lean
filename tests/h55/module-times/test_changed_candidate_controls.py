"""Guard regression: changed source or wrong drift state silently keeps a reference."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('changed_candidate_controls', root/'scripts/h55/module-times/changed_candidate_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class ChangedCandidateControls(unittest.TestCase):
    def test_scope_state_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                source = base / name
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'candidate': {'path': name, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()}, 'state':'changed-candidate-review'})
            result = module.classify(base, rows)
            self.assertIn('no concrete hash injectivity', result[0]['role'])
            self.assertIn('guarded rejections are expected-success', result[1]['role'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            with self.assertRaises(ValueError):
                module.classify(base, [{**rows[0], 'state':'referenced-static-only'}])
            (base / rows[0]['candidate']['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
