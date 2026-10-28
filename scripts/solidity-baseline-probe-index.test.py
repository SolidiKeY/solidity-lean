#!/usr/bin/env python3
import importlib.util,json,unittest,hashlib,tarfile,tempfile
from pathlib import Path
from unittest.mock import patch
spec=importlib.util.spec_from_file_location('probe',Path(__file__).with_name('solidity-baseline-probe-index.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
ROOT=Path(__file__).resolve().parents[1]
class ProbeIntegrity(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  inputs=ROOT/m.PROBES;ledger=json.loads((inputs/'reproduction-inputs.json').read_text())
  archive=inputs/'reproduction-inputs.tar.gz'
  if hashlib.sha256(archive.read_bytes()).hexdigest()!=ledger['archiveSha256']:raise ValueError('historical input archive drift')
  directory=tempfile.TemporaryDirectory(prefix='baseline-probes-');cls.addClassCleanup(directory.cleanup)
  snapshot=Path(directory.name)
  with tarfile.open(archive) as tf:
   if {v.name for v in tf.getmembers()}!=set(ledger['files']):raise ValueError('historical input membership drift')
   for member in tf.getmembers():
    if not member.isfile() or hashlib.sha256(tf.extractfile(member).read()).hexdigest()!=ledger['files'][member.name]:raise ValueError('historical input hash drift')
   tf.extractall(snapshot,filter='data')
  (snapshot/m.BASE).parent.mkdir(parents=True,exist_ok=True)
  (snapshot/m.BASE).symlink_to(ROOT/m.BASE,target_is_directory=True)
  cls.x=m.derive(snapshot)
 def test_exact40_questions(self):
  self.assertEqual(len(self.x['features']),40);self.assertEqual(len(self.x['coverage']['evidenceNeededIds']),25);self.assertEqual(len(self.x['coverage']['documentaryQuestionIds']),15)
 def test_pipeline_integrity(self):
  for r in self.x['features']:
   for field in ['positiveControls','negativeOrBoundaryControls']:
    groups={x['case'] for x in r[field]}
    for c in groups:self.assertEqual({x['pipeline'] for x in r[field] if x['case']==c},{'legacy','viaIR'})
 def test_duplicate_feature_refused(self):
  row='id|pos|neg|kind|question|recommendation\n'
  with self.assertRaisesRegex(ValueError,'duplicate'):m.parse_plan(row+row)
 def test_literal_or_in_final_column_preserved(self):
  self.assertEqual(m.parse_plan('id|pos|neg|kind|question|a || b')[0]['recommendation'],'a || b')
 def test_no_native_or_replay_claim(self):
  self.assertFalse(self.x['nativeValidationComplete']);self.assertFalse(self.x['semanticCoveragePromoted']);self.assertEqual(self.x['controls']['falsePropertyExecution'],'not run')
  for r in self.x['features']:self.assertIn('blocked',r['nativeTypedValidation'])
 def test_bad_clause_is_not_claimed_refused(self):
  r=next(r for r in self.x['features'] if r['id']=='comments')
  self.assertIn('retains malformed',r['boundedAssessment']);self.assertFalse(r['observedRefusals'])
 def test_only_valid_source_refusals_attributed(self):
  self.assertEqual(set(r['id'] for r in self.x['features'] if r['observedRefusals']),{'increments','valueTypeDeclarations','valueTypes'})
  for r in self.x['features']:
   for obs in r['observedRefusals']:
    for f in obs['rows']:self.assertEqual(f['status'],'reader-refused');self.assertNotIn('not imported',f['reason'])
 def test_no_original_variant_reassignment(self):
  self.assertEqual(self.x['originalCounts'],{'working':4135,'broken':196,'blocked':5329})
  self.assertTrue(all(not r['baselineVariantAssociations'] for r in self.x['features']))
 def test_tampered_immutable_index_rejected(self):
  with patch.object(m,'sha',return_value='changed'):
   with self.assertRaisesRegex(ValueError,'prior index changed'):m.derive(ROOT)
 def test_outputs_reproduce(self):
  self.assertEqual(json.loads((ROOT/m.PROBES/'matrix.json').read_text()),self.x)
  self.assertEqual((ROOT/m.PROBES/'README.md').read_text(),m.render(self.x))
if __name__=='__main__':unittest.main()
