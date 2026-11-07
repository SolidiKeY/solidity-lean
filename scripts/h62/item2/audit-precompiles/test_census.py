#!/usr/bin/env python3
"""Safety regressions for the source census; no Lean or original-file writes."""
import unittest
from unittest.mock import patch
import census
class CensusTests(unittest.TestCase):
 def test_nested_comments_and_strings(self):
  source='\n/- theorem fake : True := by trivial /- nested -/ -/\nnamespace A\ndef s := "theorem hidden : False := by x"\ntheorem real : True := by trivial\nend A\n'
  ds=list(census.declarations(source))
  self.assertEqual([d['name'] for d in ds],['A.real'])
  self.assertEqual(ds[0]['signature'],'theorem real : True')
 def test_mutual_end_preserves_namespace(self):
  ds=list(census.declarations('namespace A\nmutual\ndef x := 1\nend\n/-- docs -/\ntheorem t : True := by trivial\nend A\n'))
  self.assertEqual(ds[0]['name'],'A.t')
  self.assertEqual(ds[0]['line'],6)
 def test_private_name_is_not_claimed_elaborated(self):
  d=list(census.declarations('namespace A\nprivate theorem t : True := by trivial\nend A\n'))[0]
  self.assertEqual(d['constant_name_status'],'private-mangled-name-pending')
 def test_variables_are_history_not_premises(self):
  ds=list(census.declarations('namespace A\nvariable {n : Nat}\nend A\ntheorem t : True := by trivial\n'))
  self.assertNotIn('ambient_variables',ds[0])
  self.assertEqual(ds[0]['preceding_variable_commands'],['variable {n : Nat}'])
 def test_frozen_scope_drift_rejected(self):
  with patch('census.subprocess.run') as run:
   run.return_value.stdout=b'changed module map'
   with self.assertRaisesRegex(ValueError,'frozen module map changed'): census.census()
 def test_frozen_source_drift_rejected(self):
  with patch('census.subprocess.run') as run:
   run.side_effect=[type('R',(),{'stdout':census.MAP.read_bytes()})(),type('R',(),{'stdout':b'changed source'})()]
   with self.assertRaisesRegex(ValueError,'frozen source changed'): census.census()
 def test_let_assignments_are_part_of_signature(self):
  source='theorem t (n : Nat) : (let x := n; x = n) ∧ (let y := n; y = n) := by simp\n'
  d=list(census.declarations(source))[0]
  self.assertEqual(d['signature'],source.split(' := by')[0])
  source='theorem t (n : Nat) :\n  let x := n\n  let y := x\n  y = n := by rfl\n'
  d=list(census.declarations(source))[0]
  self.assertEqual(d['signature'],source.split(' := by')[0])
 def test_real_frozen_census(self):
  c=census.census()
  ds=[d for f in c['files'] for d in f['declarations']]
  self.assertEqual(c['scope_files'],17)
  self.assertEqual(len(ds),138)
  self.assertEqual(sum(d['visibility']=='private' for d in ds),4)
  self.assertEqual(len({d['name'] for d in ds}),138)
if __name__=='__main__': unittest.main()
