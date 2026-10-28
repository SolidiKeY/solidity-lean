#!/usr/bin/env python3
"""Attribution integrity, no compiler or Lean process."""
import importlib.util
import json
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
  x=a.derive(ROOT)
  self.assertEqual(json.loads((ROOT/a.BASE/'attribution/index.json').read_text()),x)
  self.assertEqual((ROOT/a.BASE/'attribution/README.md').read_text(),a.render(x))
if __name__=='__main__': unittest.main()
