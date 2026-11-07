#!/usr/bin/env python3
"""Negative controls for the source census, not Lean proof substitutes."""
import re, shutil, sys, tempfile, unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"scripts/h62/item6/migrate-counterexamples"))
import census
class CensusControls(unittest.TestCase):
    def test_comment_and_string_imports_are_ignored(self):
        text='import Real.One\n/-\nimport False.One\n/- import False.Two -/\n-/\n-- import False.Three\ndef x := "import False.Four"\nimport Real.Two\n'
        self.assertEqual(re.findall(r"^import +([^\n]+)",census.code_only(text),re.M),["Real.One","Real.Two"])
        self.assertEqual(census.code_only(text).count("\n"),text.count("\n"))
    def test_complete_pinned_inventory(self):
        x=census.inspect()
        self.assertEqual(len(x['files']),4)
        self.assertEqual(sum(len(f['declarations']) for f in x['files']),29)
        self.assertEqual(sum(bool(d['name']) for f in x['files'] for d in f['declarations']),18)
        self.assertTrue(all(f['unchanged'] and not f['trust_tokens'] and not f['resource_options'] for f in x['files']))
        self.assertTrue(all(deps is not None or m.startswith(('Lean.','Init.','Std.')) for m,deps in x['import_graph'].items()))
    def test_statement_mutation_breaks_frozen_source_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for p in census.SCOPE:
                dst=root/p.relative_to(ROOT);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
            p=root/'Solidity/Counterexamples/DeleteFamilyGenericOverlap.lean'
            original=p.read_text();changed=original.replace(': False := by',': True := by',1)
            self.assertNotEqual(original,changed);p.write_text(changed)
            record=next(f for f in census.inspect(root)['files'] if f['path']==p.relative_to(root).as_posix())
            self.assertFalse(record['unchanged']);self.assertNotEqual(record['sha256'],record['base_sha256'])
if __name__=='__main__': unittest.main()
