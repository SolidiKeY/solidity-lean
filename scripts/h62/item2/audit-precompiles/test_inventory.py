#!/usr/bin/env python3
"""Source-classification regressions, no Lean server or frozen source writes."""
import json,os,pathlib,tempfile,unittest
from unittest.mock import patch
import inventory
EVIDENCE=pathlib.Path(os.environ.get('H62_AUDIT_EVIDENCE','/workspace/h62-audit-precompiles-evidence-4'))
class InventoryTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.value=inventory.generate(EVIDENCE);cls.rows={r['name']:r for r in cls.value['rows']}
 def test_exact_once_and_complete_source_classification(self):
  self.assertEqual(len(self.rows),138);self.assertEqual(self.value['source_classified'],138)
  self.assertFalse(self.value['kernel_inventory_complete'])
  bridge=self.rows['SolidityBridge.PrecompileAgreement.byte_list']
  self.assertEqual(bridge['package_root'],'Bridge')
  self.assertIn('EvmYul.EVM.PrecompiledContracts',bridge['file_imports'])
 def test_global_configuration_is_not_input_inhabitance(self):
  r=self.rows['Solidity.Precompiles.Bls12381.msmGas_mono']
  self.assertEqual(r['joint_premises']['configuration_binders'],['hlen','htab'])
  self.assertEqual(r['joint_premises']['input_binders'],['h'])
  self.assertFalse(r['joint_premises']['kernel_joint_witness_checked'])
 def test_h_array_binder_is_data(self):
  r=self.rows['Solidity.Precompiles.Blake2f.compress_size']
  h=next(b for b in r['binders'] if b['name']=='h')
  self.assertEqual(h['type'],'Array UInt64');self.assertEqual(h['role'],'data-parameter')
 def test_membership_is_a_proof_hypothesis(self):
  r=self.rows['SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths']
  self.assertEqual(r['joint_premises']['proof_binders'],['member'])
  self.assertEqual(next(b for b in r['binders'] if b['name']=='member')['depends_on'],['n'])
 def test_scope_preserves_contract_not_closed_typeclass_history(self):
  r=self.rows['Solidity.Stipend.empty_fits']
  self.assertTrue(r['source_full_type'].startswith('∀ {C : Contract},'))
  self.assertEqual(r['category'],'unconditional-data-domain')
  self.assertEqual(self.rows['Solidity.Precompiles.mapM_eq_none_iff']['active_source_variables'],[])
 def test_mutual_end_keeps_scope(self):
  source='namespace A\nvariable {C : Contract}\nmutual\ndef x := 0\nend\ntheorem t : C = C := rfl\nend A\n'
  self.assertEqual(inventory.source_context(source,6)[0]['names'],['C'])
 def test_full_let_conclusion_is_retained(self):
  r=self.rows['Solidity.Precompiles.Bn254.decodeG1_eq_none_iff']
  self.assertIn('let x :=',r['source_full_type']);self.assertIn('let y :=',r['source_full_type'])
  self.assertTrue(r['source_full_type'].endswith('% p'))
 def test_private_names_not_invented(self):
  private=[r for r in self.rows.values() if r['private_constant_name_pending']]
  self.assertEqual(len(private),4)
  self.assertTrue(all(not r['kernel_full_type_checked'] for r in private))
 def test_closed_statements_not_promoted(self):
  closed=[r for r in self.rows.values() if r['category']=='closed-statement']
  self.assertEqual(len(closed),28);self.assertTrue(all(not r['kernel_applicability_checked'] for r in closed))
 def test_no_classification_promotes_pending_proofs(self):
  self.assertEqual(self.value['pending_categories'],{'proof-premises':30,'unconditional-data-domain':56,'closed-statement':28})
  self.assertEqual(self.value['proof_hypothesis_binders'],47)
  self.assertEqual(self.value['configuration_proof_binders'],7)
 def test_missing_membership_annotation_rejected(self):
  data=json.loads(inventory.ROLE_FILE.read_text())
  del data['proof_binders']['SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths']
  with tempfile.TemporaryDirectory(dir=str(EVIDENCE)) as d:
   p=pathlib.Path(d)/'roles.json';p.write_text(json.dumps(data))
   with patch('inventory.ROLE_FILE',p):
    with self.assertRaises(AssertionError):inventory.generate(EVIDENCE)
 def test_typed_value_domain_caution(self):
  self.assertIn('dependent_domain_caution',self.rows['Solidity.Stipend.pow_not_fits'])
 def test_isolated_fixture_never_promotes_bls(self):
  r=self.rows['Solidity.Precompiles.Bls12381.msmGas_mono']
  self.assertFalse(r['isolated_joint_constraint_fixture']['counts_as_original_statement_witness'])
  self.assertFalse(r['kernel_applicability_checked'])
 def test_exclusive_pending_wait_groups(self):
  groups=self.value['pending_wait_disposition']['groups']
  self.assertEqual({k:v['statements'] for k,v in groups.items()},{'Bls12381':29,'Syntax-Raw':12,'Bridge-compatible-dependencies':73})
  pending=[r for r in self.rows.values() if not r['kernel_applicability_checked']]
  self.assertEqual(len(pending),114);self.assertTrue(all(not r['dependency_receipt_accepted'] for r in pending))
 def test_partial_raw_does_not_accept_dependency(self):
  raw=self.value['pending_wait_disposition']['partial_Raw']
  self.assertTrue(raw['content_hashes_verified']);self.assertFalse(raw['trust_accepted']);self.assertFalse(raw['dependency_accepted'])
  self.assertEqual(raw['reported_axiom_growth_entries'],30)
  packet=json.loads(inventory.external_record('partial-Raw-receipt.json').read_text())
  packet['dependency_accepted']=True
  disposition=json.loads(inventory.external_record('h70-waits.json').read_text())
  with patch('inventory.json.loads',side_effect=[packet,disposition]):
   with self.assertRaises(AssertionError):inventory.pending_wait_disposition(list(self.rows.values()),EVIDENCE)
 def test_staged_compiler_route_is_not_delivered(self):
  d=self.value['pending_wait_disposition']['current_disposition']
  self.assertEqual(d['compiler_success_owner'],'claudecloud/move5-20261106/v14-g43')
  self.assertEqual(d['compiler_route_status'],'staged-pending-delivery');self.assertFalse(d['compiler_delivery_confirmed'])
  packet=json.loads(inventory.external_record('partial-Raw-receipt.json').read_text())
  disposition=json.loads(inventory.external_record('h70-waits.json').read_text())
  disposition['current_disposition']['compiler_delivery_confirmed']=True
  with patch('inventory.json.loads',side_effect=[packet,disposition]):
   with self.assertRaises(AssertionError):inventory.pending_wait_disposition(list(self.rows.values()),EVIDENCE)
 def test_failed_full_type_receipt_rejected(self):
  p=EVIDENCE/'type-fidelity-final.json';meta=json.loads(p.read_text());meta['exit']=1
  with tempfile.TemporaryDirectory(dir=str(EVIDENCE)) as d:
   directory=pathlib.Path(d);(directory/p.name).write_text(json.dumps(meta))
   with self.assertRaises(AssertionError):inventory.checked_type_receipt(directory)
if __name__=='__main__':unittest.main()
