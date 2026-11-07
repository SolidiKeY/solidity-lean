"""Guard regression: refutations or proof-bearing records count as compiler witnesses."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('compiler_transport_controls', root / 'scripts/h55/module-times/compiler_transport_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class CompilerTransportControls(unittest.TestCase):
    def test_witness_scope_effects_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve()
            rows = []
            for name in module.ROLES:
                relative = module.PREFIX + name + '.lean'
                source = base / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'path': relative, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
            result = {r['candidate']['path']: r for r in module.classify(base, rows)}
            get = lambda name: result[module.PREFIX + name + '.lean']
            self.assertIn('not inhabited joint witnesses', get('H69')['role'])
            self.assertIn('not proof of global inhabitation', get('CarrierInventory')['role'])
            self.assertIn('caller-selected JSON', get('Reflect')['effects'])
            self.assertIn('900s', get('Audit')['expected_outcome'])
            self.assertIn('RLIMIT_AS is not an RSS cap', get('Audit')['expected_outcome'])
            self.assertIn('h69_validate.py', get('H69')['driver'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            (base / rows[0]['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
