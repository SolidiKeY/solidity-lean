"""Guard unmatched statement/context baselines being used as migration timing."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_dispatch_consumers as check


class ConsumerHeaderControls(unittest.TestCase):
    def test_empty_migrated_scope_refused_before_output_or_lean(self):
        with patch.object(check.audit, 'MIGRATED', []):
            with self.assertRaisesRegex(ValueError, 'empty migrated consumer scope'):
                check.main()

    def run_case(self,before,after):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for label,text in [('before',before),('after',after)]:
                (root/label).mkdir();(root/label/'Consumer.lean').write_text(text)
            return check.check_headers(root/'before',root/'after',['Consumer.lean'])

    def test_import_and_proof_changes_preserve_headers(self):
        self.assertEqual(self.run_case('import Old\nnamespace N\ntheorem t (n : Nat) : n = n := by rfl\nend N\n',
                                       'import New\nnamespace N\ntheorem t (n : Nat) : n = n := Eq.refl n\nend N\n'),{'Consumer.lean':1})

    def test_changed_premise_or_variable_context_refused(self):
        baseline='namespace N\nvariable (n : Nat)\ntheorem t : n = n := rfl\nend N\n'
        for changed in [baseline.replace('n : Nat','n : Int'),baseline.replace('theorem t :','theorem t (h : False) :')]:
            with self.assertRaisesRegex(ValueError,'statement/context drift'):self.run_case(baseline,changed)

    def test_removed_or_added_declaration_refused(self):
        a='theorem t : True := True.intro\n'
        with self.assertRaisesRegex(ValueError,'statement/context drift'):self.run_case(a,'')
        with self.assertRaisesRegex(ValueError,'statement/context drift'):self.run_case(a,a+'theorem u : True := True.intro\n')

    def test_duplicate_declaration_refused(self):
        a='theorem t : True := True.intro\n'
        with self.assertRaisesRegex(ValueError,'duplicate'):self.run_case(a,a+a)


if __name__=='__main__':unittest.main()
