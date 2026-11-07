"""Join controls use historical actual metadata as fixture, never as current proof."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('join',ROOT/'scripts/roadmap-v17-join.py')
j=importlib.util.module_from_spec(spec); spec.loader.exec_module(j)
class JoinControls(unittest.TestCase):
    def setUp(self):
        self.row=json.loads((ROOT/'tests/roadmap-v17/requests/historical-keysort-row.json').read_text())['row']; n=self.row['name']
        self.current={'revision':'a'*40,'sourceTree':'b'*40,'sourceToolchainKey':'c'*64}
        self.ledger={'workPackages':['G52'],'features':[],'combinations':[],'symbolCombinations':[],'decisions':[]}
        self.report={'schema':1,'revision':self.current['revision'],'imports':[self.row['module']],'ledgerSha256':j.e.digest(json.dumps(self.ledger,sort_keys=True).encode()),'theorems':[{'name':n,'module':self.row['module'],'revision':self.current['revision'],'kind':'parameterized','axioms':self.row['axioms'],'premises':[],'observations':[]}],'claims':[{'id':'child:G52','revision':self.current['revision'],'status':'pending','theorems':[n],'observations':[]}]}
        self.bindings={'schema':1,'snapshot':copy.deepcopy(self.current),'declarations':[{'declaration':{k:self.row[k] for k in j.FIELDS},'accountedPropositionBinders':[]}]}
    def join(self,rows=None):
        return j.joined(self.report,self.ledger,self.current,[self.row['module']],self.bindings,{self.row['name']:self.row} if rows is None else rows)
    def test_actual_metadata_matching_baseline_keeps_conditions_open(self):
        result=self.join(); d=result['declarations'][0]
        self.assertTrue(d['declarationEvidenceMatched']); self.assertEqual(d['unaccountedPropositionBinders'],[3,4])
        self.assertIn('conditional-declaration',d['obligations']); self.assertEqual(result['openRows'],['child:G52'])
        self.assertFalse(result['semanticPremisesDischarged']); self.assertFalse(result['accountingComplete']); self.assertFalse(result['releaseClosed'])
    def test_acknowledgment_is_not_discharge(self):
        self.bindings['declarations'][0]['accountedPropositionBinders']=[3,4]
        d=self.join()['declarations'][0]; self.assertEqual(d['unaccountedPropositionBinders'],[])
        self.assertIn('semantic-premises-not-discharged',d['obligations'])
    def test_missing_evidence_and_binding_are_explicit(self):
        d=self.join({})['declarations'][0]; self.assertFalse(d['declarationEvidenceMatched']); self.assertIn('missing-current-checked-declaration-evidence',d['obligations'])
        self.bindings['declarations']=[]; self.assertIn('missing-exact-declaration-binding',self.join()['declarations'][0]['obligations'])
    def test_exact_binding_mutations(self):
        baseline=copy.deepcopy(self.bindings)
        for field,value in [('name','wrong'),('module','Solidity.Other'),('kind','definition'),('typeSha256','0'*64),('valueSha256','0'*64),('axioms',[]),('typeDependencies',[]),('valueDependencies',[]),('typeProjectionDependencies',['fake']),('propositionBinders',[]),('binderCount',0)]:
            self.bindings=copy.deepcopy(baseline); self.bindings['declarations'][0]['declaration'][field]=value
            with self.subTest(field=field),self.assertRaises(ValueError): self.join()
    def test_stale_source_tool_and_producer(self):
        for field in ['revision','sourceTree','sourceToolchainKey']:
            old=copy.deepcopy(self.bindings); self.bindings['snapshot'][field]='wrong'
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'binding source'): self.join()
            self.bindings=old
        self.report['revision']='wrong'
        with self.assertRaisesRegex(ValueError,'revision'): self.join()
    def test_forged_producer_claims(self):
        for key,value in [('axioms',[]),('module','Solidity.Other')]:
            before=copy.deepcopy(self.report); self.report['theorems'][0][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError): self.join()
            self.report=before
        self.bindings['declarations'][0]['accountedPropositionBinders']=[0]
        with self.assertRaisesRegex(ValueError,'invented'): self.join()
    def test_observations_remain_unverified_and_done_is_rejected(self):
        self.report['theorems'][0]['observations']=['callback rollback'];self.report['claims'][0]['observations']=['callback rollback']
        d=self.join()['declarations'][0]; self.assertEqual(d['unverifiedObservations'],['callback rollback'])
        self.report['theorems'][0]['kind']='kernel';self.report['claims'][0]['status']='done'
        with self.assertRaisesRegex(ValueError,'feature closure'): self.join()
    def test_promotion_flags_rejected(self):
        for key in ['semanticPremisesDischarged','releaseClosed']:
            self.report[key]=True
            with self.assertRaisesRegex(ValueError,'semantic closure'): self.join()
            del self.report[key]
    def test_feature_observations_and_promotion_are_explicit(self):
        self.report['claims'][0]['observations']=['unmatched rollback']
        row=self.join()['featureEvidenceAccounting'][0]
        self.assertEqual(row['unmatchedProducerObservations'],['unmatched rollback'])
        self.assertEqual(row['unverifiedObservations'],['unmatched rollback'])
        for flag in ('semanticPremisesDischarged','releaseClosed'):
            self.report['claims'][0][flag]=True
            with self.assertRaisesRegex(ValueError,'feature row attempts'): self.join()
            del self.report['claims'][0][flag]
    def test_boolean_metadata_is_not_exact(self):
        self.row['binderCount']=1; self.row['propositionBinders']=[0]
        self.bindings['declarations'][0]['declaration']={field:self.row[field] for field in j.FIELDS}
        self.join()
        self.bindings['declarations'][0]['declaration']['binderCount']=True
        with self.assertRaisesRegex(ValueError,'wrong checked'): self.join()
        self.bindings['declarations'][0]['declaration']['binderCount']=1
        self.bindings['declarations'][0]['declaration']['propositionBinders']=[False]
        with self.assertRaisesRegex(ValueError,'wrong checked'): self.join()
    @unittest.skipUnless(ROOT.is_relative_to('/workspace'), 'production evidence-path guard requires workspace checkout')
    def test_mutated_retained_record_after_replay_is_rejected(self):
        with tempfile.TemporaryDirectory(dir=ROOT.parent) as tmp:
            path=Path(tmp)/'record.json'; path.write_text(json.dumps({'before':self.current,'after':self.current}))
            manifest={'schema':1,'snapshot':self.current,'records':[{'path':str(path),'sha256':j.e.digest(path.read_bytes())}]}
            def replay(*args):
                path.write_text('corrupt'); return {'exit':0,'result':{'rows':[self.row]}}
            with patch.object(j.k,'validate_record',return_value={'module':'Solidity.KeySort'}),patch.object(j.k,'collect',side_effect=replay),patch.object(j.e,'snapshot',return_value=self.current),patch.object(j.k,'match_replay'),self.assertRaisesRegex(ValueError,'changed during replay'):
                j.live_rows(manifest,self.current,Path(tmp))
    @unittest.skipUnless(ROOT.is_relative_to('/workspace'), 'production evidence-path guard requires workspace checkout')
    def test_loader_requires_validation_and_fresh_replay(self):
        with tempfile.TemporaryDirectory(dir=ROOT.parent) as tmp:
            out=Path(tmp); record=out/'record.json'; record.write_text(json.dumps({'before':self.current,'after':self.current}))
            manifest={'schema':1,'snapshot':self.current,'records':[{'path':str(record),'sha256':j.e.digest(record.read_bytes())}]}
            req={'module':'Solidity.KeySort'}; replay={'exit':0,'result':{'rows':[self.row]}}
            with patch.object(j.k,'validate_record',return_value=req) as validation,patch.object(j.k,'collect',return_value=replay) as collect,patch.object(j.e,'snapshot',return_value=self.current),patch.object(j.k,'match_replay') as match:
                rows,receipts=j.live_rows(manifest,self.current,out)
                self.assertEqual(rows,{self.row['name']:self.row});self.assertEqual(validation.call_count,3);collect.assert_called_once();match.assert_called_once();self.assertEqual(len(receipts),1)
            record.write_text('corrupt')
            with self.assertRaisesRegex(ValueError,'corrupt retained'): j.live_rows(manifest,self.current,out)
    @unittest.skipUnless(ROOT.is_relative_to('/workspace'), 'production evidence-path guard requires workspace checkout')
    def test_invalid_kernel_record_never_reaches_join(self):
        with tempfile.TemporaryDirectory(dir=ROOT.parent) as tmp:
            path=Path(tmp)/'record.json'; path.write_text(json.dumps({'before':self.current,'after':self.current}))
            manifest={'schema':1,'snapshot':self.current,'records':[{'path':str(path),'sha256':j.e.digest(path.read_bytes())}]}
            for reason in ('stale revision','wrong module','corrupt attachment','forged type','changed tool/import inputs'):
                with self.subTest(reason=reason),patch.object(j.k,'validate_record',side_effect=ValueError(reason)),patch.object(j.k,'collect') as collect,self.assertRaisesRegex(ValueError,reason):
                    j.live_rows(manifest,self.current,Path(tmp))
                collect.assert_not_called()
    def test_source_catalog_preserves_all_actual_ledger_rows(self):
        ledger=j.e.load(ROOT/j.e.LEDGER); result=j.catalog(self.current,ledger)
        self.assertEqual(result['ledger'],ledger); self.assertEqual(result['openRows'],j.e.inventory(ledger));self.assertEqual(len(result['openRows']),457)
        self.assertEqual(sum(len(f['declarations']) for f in result['families']),14)
        correct=next(d for f in result['families'] for d in f['declarations'] if d['name']=='Solidity.Evm.Compiler.Compilation.correct')
        self.assertIn('(h : result.Input L frame base σ m)',correct['sourceHeader'])
        self.assertFalse(result['semanticPremisesDischarged'])
        self.assertTrue(all(not d['semanticFeatureMatches'] for f in result['families'] for d in f['declarations']))
    def test_stale_manifest_rejected_before_replay(self):
        with self.assertRaisesRegex(ValueError,'record manifest revision'): j.live_rows({'schema':1,'snapshot':{},'records':[]},self.current,Path('/workspace/scratch/test'))
if __name__=='__main__': unittest.main()
