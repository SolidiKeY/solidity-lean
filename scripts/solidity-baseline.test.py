#!/usr/bin/env python3
"""Integrity checks for diagnostic work queues, with no Lean worker."""
import importlib.util
import tempfile
from pathlib import Path
import unittest
import json, hashlib, sys
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('baseline',Path(__file__).with_name('solidity-baseline.py'))
b=importlib.util.module_from_spec(spec); spec.loader.exec_module(b)

class Integrity(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup); self.root=Path(self.tmp.name)
  for _,_,p,_ in b.BOUNDARIES:
   q=self.root/p; q.parent.mkdir(parents=True,exist_ok=True); q.write_text('current documentation')
  self.manifest={'features':[{'id':'publicGetters','current':'partial','requirement':'getters','localEvidence':[]}]}
 def derive(self,rows): return b.derive({'metadata':{},'results':rows},self.manifest,self.root)
 def test_duplicate_paths_rejected(self):
  row={'path':'a','status':'blocked','stage':'lean-runtime'}
  with self.assertRaisesRegex(ValueError,'duplicate'): self.derive([row,row])
 def test_working_runtime_cannot_omit_required_modes(self):
  with self.assertRaisesRegex(ValueError,'valid required pipelines'): self.derive([{'path':'a','stage':'lean-runtime','status':'working','variants':[]}])
 def test_working_requires_both_pipelines(self):
  row={'path':'a','status':'working','stage':'lean-runtime','requiredPipelines':['legacy','viaIR'],'variants':[{'pipeline':'legacy','status':'working'}]}
  with self.assertRaisesRegex(ValueError,'required pipelines'): self.derive([row])
 def test_working_cannot_hide_blocked_variant(self):
  row={'path':'a','status':'working','stage':'lean-runtime','requiredPipelines':['legacy'],'variants':[{'pipeline':'legacy','status':'blocked'}]}
  with self.assertRaises(ValueError): self.derive([row])
 def test_exact_gap_objects_retained(self):
  gap={'status':'implementation','reason':'tuple target','function':'f()','extra':[1,2]}
  row={'path':'a','status':'broken','stage':'lean-runtime','requiredPipelines':['legacy'],'variants':[{'pipeline':'legacy','status':'broken','gaps':[gap]}]}
  result=self.derive([row]); self.assertEqual(result['exactVariantGaps'][0]['gap'],gap); self.assertEqual(result['counts'],{'working':0,'broken':1,'blocked':0}); self.assertEqual(result['stages']['lean-runtime'],{'working':0,'broken':1,'blocked':0})
 def test_unrouted_blocks_remain_visible(self):
  row={'path':'a','status':'blocked','stage':'upstream-harness','reason':'unknown native harness'}
  result=self.derive([row]); self.assertEqual(result['unrouted'][0]['path'],'a'); self.assertEqual(result['partialFeatures'][0]['current'],'partial')
 def test_generic_import_gap_is_not_source_unit_attribution(self):
  row={'path':'a','status':'broken','stage':'lean-runtime','reason':'frontend import gaps'}
  self.assertEqual(self.derive([row])['routes']['step-02-source-units'],[])
 def test_main_accepts_runner_zero_count_stages(self):
  (self.root/'Solidity').mkdir()
  for name in ('scripts/solidity-upstream.mjs','scripts/solc-code.mjs'):
   q=self.root/name; q.parent.mkdir(exist_ok=True); q.write_text('test reference')
  meta={'filter':None,'archiveSha256':'archive','runnerSha256':b.digest(self.root/'scripts/solidity-upstream.mjs'),'compilerCodeAdapterSha256':b.digest(self.root/'scripts/solc-code.mjs'),'modelSha256':hashlib.sha256(b'').hexdigest()}
  results=self.root/'results'; results.mkdir()
  row={'path':'test/a.sol','status':'blocked','stage':'upstream-harness','reason':'unported'}
  summary={**meta,'complete':True,'completedFixtureFiles':1,'totalFixtureFiles':1,'counts':{'working':0,'broken':0,'blocked':1},'stages':{'upstream-harness':{'working':0,'broken':0,'blocked':1}}}
  (results/'results.json').write_text(json.dumps({'metadata':meta,'results':[row]})); (results/'summary.json').write_text(json.dumps(summary))
  q=self.root/'tests/upstream/snapshot.json'; q.parent.mkdir(parents=True); q.write_text(json.dumps({'archiveSha256':'archive','files':[{'path':'test/a.sol'}]}))
  (self.root/'docs/solidity-features.json').write_text(json.dumps(self.manifest))
  with patch.object(sys,'argv',['baseline',str(results),'--root',str(self.root),'--out',str(self.root/'derived'),'--base','b'*40]), patch.object(b.subprocess,'run'):
   b.main()
  self.assertEqual(json.loads((self.root/'derived/gaps.json').read_text())['counts'],summary['counts'])
if __name__=='__main__': unittest.main()
