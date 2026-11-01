"""New published-component controls; synthetic parser cases are not kernel proof."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from types import SimpleNamespace
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('m',ROOT/'scripts/roadmap-v17-memory-calls.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class MemoryCallsControls(unittest.TestCase):
    def row(self):return dict(schema=1,isMemoryCalls=True,usesMemory=True,requiredFrame=12,callerFrame=4,allocationCost=5,sourceAliases=[2,7,88,0],targetWords=[77,261,99,42,8,1,7,2,88,0],emptyCodeWords=[77,256],intrinsicCode='actual fixture code bytes',semanticPremisesDischarged=False,releaseClosed=False)
    def raw(self,r):return ('V17_MEMORY_CALLS_BEGIN\n'+json.dumps(r)+'\nV17_MEMORY_CALLS_END\n').encode()
    def test_positive_and_mutations(self):
        r=self.row();self.assertEqual(m.observation(self.raw(r)),r);self.assertFalse(m.exact_replay(r,copy.deepcopy(r))['releaseClosed'])
        for key,value in [('intrinsicCode','changed call code bytes'),('requiredFrame',4),('allocationCost',0),('sourceAliases',[2,0,88,0]),('targetWords',[77,0]),('isMemoryCalls',False),('requiredFrame',True),('semanticPremisesDischarged',True)]:
            bad=copy.deepcopy(r);bad[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):m.exact_replay(r,bad)
            if key!='intrinsicCode':
                with self.assertRaises(ValueError):m.observation(self.raw(bad))
    def test_frames_missing_duplicate_truncated(self):
        raw=self.raw(self.row())
        for bad in [b'',raw+raw,raw[:-8],raw.replace(b'"schema": 1',b'"schema": 1, "schema": 1')]:
            with self.subTest(bad=bad[:20]),self.assertRaises(ValueError):m.observation(bad)
    def test_publication_and_query_scope(self):
        # Old exact-publication consumer must refuse the changed current Compiler.
        import subprocess
        published=subprocess.check_output(['git','show',m.PUBLICATION+':Solidity/Evm/Compiler.lean'],cwd=ROOT)
        if published==(ROOT/'Solidity/Evm/Compiler.lean').read_bytes():
            identity=m.publication_identity();self.assertEqual(identity['publication'],m.PUBLICATION)
        else:
            with self.assertRaisesRegex(ValueError,'producer differs'):m.publication_identity()
        self.assertEqual(len(m.PUBLIC_REQUESTS)+len(m.PRIVATE),16)
        raw=m.query_bytes();self.assertIn(m.name_term('Solidity.Evm.Compiler.Compilation.memoryCalls').encode(),raw);self.assertIn(b'wrong_code_rejected',raw);self.assertIn(b'private_frame_rejected',raw)
        self.assertIn(b'KernelQuery.extract #[request] includeValues',raw)
    def test_failed_or_missing_producer_cannot_reach_frames(self):
        fake=SimpleNamespace(p=SimpleNamespace(validate=lambda *a,**kw:False))
        with patch.object(m,'load_kernel',return_value=fake),patch.object(m,'observation') as observed:
            with self.assertRaisesRegex(ValueError,'missing producer'):m.verify({},Path('/tmp'),{})
            with self.assertRaisesRegex(ValueError,'failed producer'):m.verify({},Path('/tmp'),{},producer={},producer_directory=Path('/tmp'))
            observed.assert_not_called()
        fake.p.validate=lambda record,*a,**kw:record['exit']==0
        with patch.object(m,'load_kernel',return_value=fake),patch.object(m,'observation') as observed:
            with self.assertRaisesRegex(ValueError,'failed observation'):m.verify({'exit':125},Path('/tmp'),{},producer={'exit':0},producer_directory=Path('/tmp'))
            observed.assert_not_called()
    def test_producer_import_and_installed_continuity_guards(self):
        producer={'exit':0,'buildEnd':{'files':{'module':'hash'}},'cacheEnd':{'key':'same'},'installedAfter':{'lib':'hash'}}
        record={'exit':0,'buildStart':copy.deepcopy(producer['buildEnd']),'cacheStart':copy.deepcopy(producer['cacheEnd']),'installedBefore':copy.deepcopy(producer['installedAfter']),'log':'log','logSha256':'hash'}
        fake=SimpleNamespace(p=SimpleNamespace(validate=lambda *a,**kw:True,read_bound=lambda *a:b'fixture'))
        with patch.object(m,'load_kernel',return_value=fake),patch.object(m,'observation',side_effect=RuntimeError('positive guards reached')):
            with self.assertRaisesRegex(RuntimeError,'positive guards'):m.verify(record,Path('/tmp'),{},producer,Path('/tmp'))
            previous={'before':{},'after':{},'exit':0,'buildEnd':record['buildStart'],'cacheEnd':{'log':'updated by first query'}}
            chained=copy.deepcopy(record);chained['cacheStart']=previous['cacheEnd']
            with self.assertRaisesRegex(RuntimeError,'positive guards'):m.verify(chained,Path('/tmp'),{},producer,Path('/tmp'),previous=previous)
            previous['exit']=125
            with self.assertRaisesRegex(ValueError,'predecessor'):m.verify(chained,Path('/tmp'),{},producer,Path('/tmp'),previous=previous)
            for field in ['buildStart','cacheStart','installedBefore']:
                bad=copy.deepcopy(record);bad[field]={}
                with self.subTest(field=field),self.assertRaises(ValueError):m.verify(bad,Path('/tmp'),{},producer,Path('/tmp'))
    def test_constructor_and_explicit_type_only_boundary(self):
        k=m.load_kernel();row={'name':'Solidity.Evm.Compiler.Compilation.memoryCalls','kind':'constructor','type':['sort',['zero']],'value':None,'typeDependencies':[],'valueDependencies':[]}
        m.check_value_evidence(row,k)
        row['kind']='theorem'
        with self.assertRaises(ValueError):m.check_value_evidence(row,k)
        row.update(name='Solidity.Evm.Compiler.Compilation.correct',valueOmitted=True,valueDependencies=None)
        m.check_value_evidence(row,k)
        row['type']=None
        with self.assertRaises(ValueError):m.check_value_evidence(row,k)
    def test_full_wrapper_replay_and_axiom_refusals(self):
        first={'observation':self.row(),'metadata':{'kind':'constructor'},'profile':{'source':'published'},'sourceSnapshot':{'revision':'a'},'installedInputs':{'olean':'sha'}}
        m.exact_replay(first,copy.deepcopy(first))
        for field in ['metadata','profile','sourceSnapshot','installedInputs']:
            bad=copy.deepcopy(first);bad[field]={}
            with self.subTest(field=field),self.assertRaises(ValueError):m.exact_replay(first,bad)
        names=['compile_identity','endpoint_input','endpoint_agreement','target_observation','wrong_code_rejected','wrong_alias_rejected','private_frame_rejected']
        raw=''.join("'Solidity.Roadmap.V17.MemoryCalls."+n+"' does not depend on any axioms\n" for n in names).encode()
        self.assertEqual(len(m.headline_axioms(raw)),7)
        for bad in [b'',raw+raw,raw.replace(b'does not depend on any axioms',b'depends on axioms: [sorryAx]',1)]:
            with self.assertRaises(ValueError):m.headline_axioms(bad)
if __name__=='__main__':unittest.main()
