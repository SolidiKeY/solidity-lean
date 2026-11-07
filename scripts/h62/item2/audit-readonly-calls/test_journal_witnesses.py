"""Guard missing journal cases and substituted original interface inventories."""
import importlib.util
from pathlib import Path
import subprocess
import unittest
spec=importlib.util.spec_from_file_location('journal_controls',Path(__file__).with_name('check_journal_witnesses.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.gate
class JournalControls(unittest.TestCase):
    def test_exact_inventory(self):
        raw=(g.ROOT/g.SOURCE).read_bytes()
        self.assertEqual(len(g.inventory(raw)),8)
        self.assertEqual(len(set(g.INTERFACES)),3)
        for bad in [b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_original_joint_premises(self):
        file='Solidity/Lowering/Readonly/StaticJournal.lean'
        raw=subprocess.check_output(['git','show',g.original.BASE+':'+file],cwd=g.ROOT)
        rows={r['source_name']:r for r in g.original.export.census.declarations_text(file,raw.decode())}
        self.assertEqual(g.INTERFACES,[g.TARGET+'.'+n for n in ['transfer_history','History.storage','credit_history']])
        self.assertIn('execution : state.transfer src dst v = some final',rows[g.INTERFACES[0]]['signature'])
        self.assertIn('static : mode = true',rows[g.INTERFACES[1]]['signature'])
if __name__=='__main__':unittest.main()
