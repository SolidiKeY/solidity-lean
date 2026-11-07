"""Guard regression: later refutation inputs silently disappear from the census."""
import importlib.util
from pathlib import Path
import sys
import unittest

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root/'scripts/h55/module-times'))
spec = importlib.util.spec_from_file_location('evm_compiler_later_controls', root/'scripts/h55/module-times/evm_compiler_later_controls.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class EvmCompilerLaterControls(unittest.TestCase):
    def test_exact_roster_and_other_paths(self):
        rows = [{'path':module.PREFIX+n+'.lean','resolution':'file-check-review','sha256':'1'*64} for n in module.ROLES]
        rows.append({'path':module.PREFIX+'Older.lean','resolution':'file-check-review'})
        out, other = module.classify(rows)
        self.assertEqual(6, len(out))
        self.assertEqual([module.PREFIX+'Older.lean'], other)
        self.assertIn('not positive joint witnesses', next(x for x in out if x['candidate']['path'].endswith('RefutationAudit.lean'))['role'])
        self.assertIn('not a Lean runner', out[0]['driver'])
        with self.assertRaises(ValueError):
            module.classify(rows[:-2])
        with self.assertRaises(ValueError):
            module.classify(rows + rows[:1])

if __name__ == '__main__':
    unittest.main()
