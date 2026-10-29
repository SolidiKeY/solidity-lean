#!/usr/bin/env python3
"""Attribution integrity, no compiler or Lean process."""
import importlib.util
import json
import hashlib
import tarfile
import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch
spec=importlib.util.spec_from_file_location('attribution',Path(__file__).with_name('solidity-baseline-attribution.py'))
a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
ROOT=Path(__file__).resolve().parents[1]
class Attribution(unittest.TestCase):
 def test_duplicate_id_refused(self):
  row='x|boundary|wave|source|remaining|none\n'
  with self.assertRaisesRegex(ValueError,'duplicate'): a.parse_table(row+row)
 def test_missing_question_refused(self):
  with self.assertRaisesRegex(ValueError,'exact evidence'): a.parse_table('x|evidence-needed|wave|source|remaining|none')
 def test_empty_field_refused(self):
  with self.assertRaisesRegex(ValueError,'empty'): a.parse_table('x|boundary|wave|source||none')
 def test_bad_disposition_refused(self):
  with self.assertRaisesRegex(ValueError,'disposition'): a.parse_table('x|present|wave|source|remaining|none')
 def test_immutable_hash_refused_before_derivation(self):
  with patch.object(a,'file_sha',return_value='changed'):
   with self.assertRaisesRegex(ValueError,'immutable input hash mismatch'): a.derive(ROOT)
 def test_selected_associations_are_source_specific(self):
  self.assertNotIn('typeBounds',a.ASSOCIATIONS)
  self.assertNotIn('fixedArrays',a.ASSOCIATIONS)
  self.assertNotIn('numericLiterals',a.ASSOCIATIONS)
  self.assertNotIn('doWhileStatement',a.ASSOCIATIONS)
 def test_saved_catalog_integrity(self):
  x=json.loads((ROOT/a.BASE/'attribution/index.json').read_text())
  self.assertEqual([r['id'] for r in x['features']],x['originalUnresolvedIds'])
  inherited={r['id'] for r in x['inheritedReviewedFeatures']}
  current={r['id'] for r in x['features']}
  self.assertFalse(inherited & current)
  self.assertEqual(len(inherited|current),160)
  self.assertFalse(x['semanticGapAttributionComplete'])
  self.assertTrue(x['diagnosticReviewComplete'])
  self.assertEqual(x['counts'],{'working':4135,'broken':196,'blocked':5329})
  self.assertEqual(len({i for q in x['nextWaves'].values() for k in ('establishedBoundaryIds','evidenceNeededIds') for i in q[k]}),84)
  for r in x['features']:
   self.assertTrue(r['citations']);self.assertTrue(r['remaining']);self.assertTrue(r['missingEvidence'])
   for g in r['observedGaps']:
    self.assertIn(g['pipeline'],g['requiredPipelines'])
    self.assertTrue(g['sourceSha256']);self.assertTrue(g['jsonPointer'].startswith('/results/'))
 def test_reproduction_matches_committed_output(self):
  # Reproduce the historical report from its hash-checked original inputs.
  # The merged manifest and cited sources deliberately describe newer work.
  inputs=ROOT/a.BASE/'attribution'
  ledger=json.loads((inputs/'reproduction-inputs.json').read_text())
  archive=inputs/'reproduction-inputs.tar.gz'
  self.assertEqual(hashlib.sha256(archive.read_bytes()).hexdigest(),ledger['archiveSha256'])
  with tempfile.TemporaryDirectory(prefix='baseline-attribution-') as directory:
   snapshot=Path(directory)
   with tarfile.open(archive) as tf:
    self.assertEqual({m.name for m in tf.getmembers()},set(ledger['files']))
    for member in tf.getmembers():
     self.assertTrue(member.isfile())
     self.assertEqual(hashlib.sha256(tf.extractfile(member).read()).hexdigest(),ledger['files'][member.name])
    tf.extractall(snapshot,filter='data')
   (snapshot/a.BASE/'portable-evidence.tar.gz').symlink_to(ROOT/a.BASE/'portable-evidence.tar.gz')
   (snapshot/'tests/upstream/solidity-0.8.38.tar.gz').symlink_to(ROOT/'tests/upstream/solidity-0.8.38.tar.gz')
   x=a.derive(snapshot)
  self.assertEqual(json.loads((ROOT/a.BASE/'attribution/index.json').read_text()),x)
  self.assertEqual((ROOT/a.BASE/'attribution/README.md').read_text(),a.render(x))
if __name__=='__main__': unittest.main()
