"""Guard regression: #eval writes and native observations are silently accepted as proofs."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

path = Path(__file__).resolve().parents[3] / 'scripts/h55/module-times/root_controls.py'
spec = importlib.util.spec_from_file_location('root_controls', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class RootControls(unittest.TestCase):
    def test_distinct_effects_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            rows = []
            for name in module.CONTROLS:
                source = root / name
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'path': name, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
            result = module.classify(root, {'rows': rows})
            self.assertIn('not PaddingCorrect proof', result[0]['context'])
            self.assertIn('not corpus or testsuite', result[1]['context'])
            self.assertIn('writes .cache/parse-corpus/results.tsv', result[2]['effects'])
            self.assertIn('intentional negative vector', result[3]['outcome'])
            self.assertIn('external checker is separate', result[3]['outcome'])
            self.assertTrue(all('not-execution-acceptance' in r['status'] for r in result))
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows + rows[:1]})
            (root / rows[2]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(root, {'rows': rows})

if __name__ == '__main__':
    unittest.main()
