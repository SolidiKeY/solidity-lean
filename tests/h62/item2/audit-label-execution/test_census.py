"""Scanner regressions for false frozen-statement coverage claims (no Lean)."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('census', ROOT/'scripts/h62/item2/audit-label-execution/census.py')
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)

class CensusTests(unittest.TestCase):
    def test_nested_comments_and_strings_preserve_offsets(self):
        source = '/- theorem false := /- nested -/ end -/\n"theorem fake :="\nnamespace N\ntheorem actual (n : Nat := 0) : n = n := by rfl\nend N\n'
        masked = census.mask(source)
        self.assertEqual(len(masked),len(source))
        rows = census.declarations(source,'Fixture.lean')
        self.assertEqual([r['name'] for r in rows],['N.actual'])
        self.assertTrue(rows[0]['signature'].endswith('n = n'))

    def test_result_lets_and_binder_defaults_are_not_proof_delimiters(self):
        source = 'namespace A\nsection\ntheorem t (n : Nat := 1) :\n let x := n; let y := x + 1; y = n + 1 := by rfl\nend\nend A\n'
        rows = census.declarations(source,'Fixture.lean')
        self.assertEqual(rows[0]['name'],'A.t')
        self.assertEqual(rows[0]['signature'],'theorem t (n : Nat := 1) :\n let x := n; let y := x + 1; y = n + 1')

    def test_brace_expansion_retains_empty_alternative(self):
        self.assertEqual(census.expand_braces('A/{B,C}{,Controls}.lean'),
                         ['A/B.lean','A/BControls.lean','A/C.lean','A/CControls.lean'])

    def test_frozen_blob_guard_rejects_local_mutation(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td); (root/'a.lean').write_bytes(b'modified')
            with patch.object(census.subprocess,'check_output',return_value=b'frozen'):
                with self.assertRaisesRegex(ValueError,'differs from worktree'):
                    census.frozen_bytes(root,'a.lean')
                (root/'a.lean').write_bytes(b'frozen')
                self.assertEqual(census.frozen_bytes(root,'a.lean'),b'frozen')

    def test_ambiguous_owners_are_retained(self):
        registry={'items':[{'id':n,'owner':n,'group':'h30-file-ownership','writeScope':'Solidity/A/**'} for n in ['one','two']]}
        self.assertEqual(len(census.owners('Solidity/A/B.lean',registry)),2)

    def test_frozen_real_map_completeness(self):
        paths=census.modules(ROOT)
        self.assertEqual(len(paths),147)
        rows=[r for p in paths for r in census.declarations(census.frozen_bytes(ROOT,p).decode(),p)]
        self.assertEqual(len(rows),656)
        self.assertEqual(len({(r['path'],r['name']) for r in rows}),656)
        # All eight real result-type let regressions now include the result after :=.
        affected=['bare_code_handled','loop_exit_step','source_body_fields','allocation_roundtrip','source_target_clipped_hash']
        for row in rows:
            if row['source_name'] in affected or row['path'].endswith(('ConditionalSequenceCompiler.lean','ConditionalSourceCompiler.lean','Lowering/G19/ConditionalSequence.lean')) and row['source_name']=='correct':
                self.assertIn(':=',row['signature'])
                self.assertFalse(row['signature'].endswith('Bool'))

if __name__ == '__main__': unittest.main()
