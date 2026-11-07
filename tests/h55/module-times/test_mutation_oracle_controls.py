"""Guard regression: production-control failure or sound survivor counts as a kill."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('mutation_oracle_controls', root/'scripts/h55/module-times/mutation_oracle_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class MutationOracleControls(unittest.TestCase):
    def test_phase_scope_and_source_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve()
            rows = []
            for name in ('BoundsZeroOnProduction','LengthReevalSound','CallbackTacletFailureKill','IfElseBaseline'):
                path = module.PREFIX + name + '.lean'
                source = base / path
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('fixture')
                rows.append({'candidate': {'path':path, 'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}, 'status':'no-supplied-current-reference'})
            result = {r['candidate']['path']:r for r in module.classify(base, rows)}
            get = lambda name: result[module.PREFIX + name + '.lean']
            self.assertIn('not a mutant kill', get('BoundsZeroOnProduction')['role'])
            self.assertIn('sound-survivor', get('LengthReevalSound')['role'])
            self.assertIn('send-flag-true-to-false.1 was witness-failed', get('CallbackTacletFailureKill')['expected_outcome'])
            self.assertIn('callback-table.failed-send-flag-true was killed', get('CallbackTacletFailureKill')['expected_outcome'])
            with self.assertRaises(ValueError):
                module.classify(base, rows + rows[:1])
            (base / rows[0]['candidate']['path']).write_text('changed')
            with self.assertRaises(ValueError):
                module.classify(base, rows)

if __name__ == '__main__':
    unittest.main()
