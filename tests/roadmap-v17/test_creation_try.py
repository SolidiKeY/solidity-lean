"""Preparation controls; synthetic baselines never substitute for live evidence."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from types import SimpleNamespace
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('c',ROOT/'scripts/roadmap-v17-creation-try.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
class CreationControls(unittest.TestCase):
    def row(self):
        expected=[[0]*128,[1]*128]
        ctx=dict(kind='creation-try-source',selfAddress='457415396813334496268612927368880745799219276745',sender='103164821458651970696730694074090566093359944210',value='0',ownerFunds='0',timestamp='0',senderFunds='1000000000000000000000000000000',firstCreationNonce=1)
        r=dict(schema=1,orderedSignatures=['f()','g()'],legacy=expected,ordinary=copy.deepcopy(expected),viaIR=copy.deepcopy(expected),expectedLegacy=copy.deepcopy(expected),expectedIR=copy.deepcopy(expected),collision={'kind':'bare-revert','bytes':[]},installations=[True,True],arguments=[3,8],hostContext=ctx,first='428238858683769988117249899297947241168592284849',second='765865378857594171345198072072138302409814020804',semanticPremisesDischarged=False,releaseClosed=False)
        native={'status':'working','reason':'synthetic parser baseline','selfAddress':ctx['selfAddress'],'observed':[dict(signature=r['orderedSignatures'][i],failed=False,values=[],returnBytes=expected[i],revertBytes=[],creationTarget=r[['first','second'][i]],creationNonce=i+1,constructorInstalled=i==1) for i in range(2)]}
        r['nativeLegacy']=copy.deepcopy(native);r['nativeIR']=copy.deepcopy(native);return r
    def raw(self,r):return ('V17_CREATION_BEGIN\n'+json.dumps(r)+'\nV17_CREATION_END\n').encode()
    def test_synthetic_shape_only(self):
        r=self.row();self.assertEqual(c.observation(self.raw(r)),r)
        self.assertFalse(c.load_memory().exact_replay(r,copy.deepcopy(r))['releaseClosed'])
    def test_actual_fields_refuse_changed_bytes_world_and_accounts(self):
        mutations=[('orderedSignatures',['g()','f()']),('legacy',[[0]*127,[1]*128]),('viaIR',[[1]*128,[0]*128]),('ordinary',None),('collision',{'kind':'return','bytes':[]}),('installations',[False,True]),('arguments',[8,3]),('first','0'),('second','0'),('schema',True),('releaseClosed',True),('semanticPremisesDischarged',True)]
        for key,value in mutations:
            bad=copy.deepcopy(self.row());bad[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):c.observation(self.raw(bad))
    def test_context_and_native_mutations(self):
        for pipeline in ['nativeLegacy','nativeIR']:
            for key,value in [('creationTarget','0'),('creationNonce',2),('constructorInstalled',True),('failed',True),('returnBytes',[]),('revertBytes',[1])]:
                r=self.row();r[pipeline]['observed'][0][key]=value
                with self.subTest(pipeline=pipeline,key=key),self.assertRaises(ValueError):c.observation(self.raw(r))
        for key,value in [('sender','0'),('selfAddress','0'),('senderFunds','0'),('value','1'),('firstCreationNonce',True)]:
            r=self.row();r['hostContext'][key]=value
            with self.subTest(context=key),self.assertRaises(ValueError):c.observation(self.raw(r))
    def test_frames_and_complete_bytes(self):
        raw=self.raw(self.row())
        for bad in [b'',raw+raw,raw[:-5],raw.replace(b'"schema": 1',b'"schema": 1, "schema": 1')]:
            with self.assertRaises(ValueError):c.observation(bad)
        r=self.row();r['expectedLegacy'][0]=[False]*128
        with self.assertRaises(ValueError):c.observation(self.raw(r))
    def test_publication_and_no_local_byte_oracle(self):
        profile=c.publication_identity();self.assertFalse(profile['fixtures']['tests/solc/CreationTry.ast.json']['header']['settings']['viaIR']);self.assertTrue(profile['fixtures']['tests/solc/CreationTryIR.ast.json']['header']['settings']['viaIR'])
        query=c.query_bytes();self.assertIn(b'info.type.getAppArgs[2]!',query);self.assertIn(b'KernelQuery.extract #[',query);self.assertNotIn(b'includeValues',query.split(b'run_cmd do')[-1]);self.assertEqual(len(c.REQUESTS),16)
        for _,name,_ in c.REQUESTS:self.assertIn(c.load_memory().name_term(name).encode(),query)
    def test_missing_or_failed_receipts_reject_before_observation(self):
        m=c.load_memory();k=SimpleNamespace(p=SimpleNamespace(validate=lambda *a,**kw:False));m.load_kernel=lambda:k
        with patch.object(c,'load_memory',return_value=m),patch.object(c,'observation') as observe:
            with self.assertRaisesRegex(ValueError,'missing producer'):c.verify({},Path('/tmp'),{})
            with self.assertRaisesRegex(ValueError,'failed producer'):c.verify({},Path('/tmp'),{},producer={},producer_directory=Path('/tmp'))
            observe.assert_not_called()
    def test_full_wrapper_mutations(self):
        base={'observation':self.row(),'metadata':{'rows':[{'type':'actual checked AST'}]},'profile':{'pipeline':False,'astSha256':'a','sourceSha256':'b'},'sourceSnapshot':{'revision':'c'},'installedInputs':{'x':'d'}}
        for key in base:
            changed=copy.deepcopy(base);changed[key]={'forged':'claim'}
            with self.subTest(key=key),self.assertRaises(ValueError):c.load_memory().exact_replay(base,changed)
    def test_missing_metadata_not_promoted(self):
        for value in [{'schema':1,'rows':[],'imports':[],'releaseClosed':False},{'schema':1,'rows':[],'imports':[],'releaseClosed':True}]:
            raw=('V17_CREATION_KERNEL_BEGIN\n'+json.dumps(value)+'\nV17_CREATION_KERNEL_END\n').encode()
            with self.assertRaises(ValueError):c.metadata(raw)
