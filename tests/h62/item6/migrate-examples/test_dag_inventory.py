#!/usr/bin/env python3
"""Integrity controls for complete, shared structural type/name inventories."""
import copy
import importlib.util
import json
import pathlib
import tempfile
import hashlib
import sys
import unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
TOOLS=ROOT/'scripts/h62/item6/migrate-examples'
sys.path.insert(0,str(TOOLS))
import dag_inventory as audit


def name(*parts):
    result=['anonymous']
    for part in parts:result=['str',result,part]
    return result


def line(tag,value):return tag+' '+json.dumps(value)+'\n'


class DagInventoryTests(unittest.TestCase):
    def fixture(self):
        m='Solidity.Examples.A';z='Solidity.Examples.Zero'
        scope={'base':audit.BASE,'modules':[{'module':m},{'module':z}]}
        rows=[('H62-EXAMPLES-HEADER',{'schema':'h62-examples-dag-v1','base':audit.BASE,'modules':[m,z],'lean_version':audit.OLD_VERSION,'lean_commit':audit.OLD_COMMIT,'source_commit':'a'*40,'capture_id':'fixture'}),
              ('H62-NODE',{'module':m,'id':0,'tag':'const','data':[name('Nat'),[]],'children':[]}),
              ('H62-EXAMPLES-DECL',{'module':m,'name':'A.proof','name_parts':name('A','proof'),'kind':'theorem','unsafe':False,'private_name':False,'protected_name':False,'level_parameters':[],'type_root':0}),
              ('H62-EXAMPLES-EXTRA',{'module':m,'name':'A._compiled','name_parts':name('A','_compiled'),'private_name':False,'internal':True}),
              ('H62-EXAMPLES-MODULE',{'module':m,'kernel':1,'compiler_extra':1,'nodes':1}),
              ('H62-EXAMPLES-MODULE',{'module':z,'kernel':0,'compiler_extra':0,'nodes':0}),
              ('H62-EXAMPLES-COMPLETE',{'modules':2,'kernel':1,'compiler_extra':1})]
        return scope,rows

    def collect(self,scope,rows,exit=0):return audit.collect(scope,(line(*r) for r in rows),exit)

    def test_complete_with_zero_module_and_unresolved_extra(self):
        scope,rows=self.fixture();entries,summary=self.collect(scope,rows)
        self.assertEqual(summary['kernel_declarations'],1)
        self.assertEqual(summary['compiler_extra_names'],1)
        extra=next(v for v in entries.values() if v['category']=='compiler_extra')
        self.assertIsNone(extra['old_signature']);self.assertFalse(extra['excluded'])
        self.assertEqual(summary['exclusions'],0)

    def test_footer_counts_scope_and_failed_compiler(self):
        scope,rows=self.fixture()
        for altered in (rows[:-1],rows+[rows[1]],rows[:5]+rows[6:]):
            with self.assertRaises(ValueError):self.collect(scope,altered)
        altered=copy.deepcopy(rows);altered[0][1]['modules']=altered[0][1]['modules'][:1]
        with self.assertRaises(ValueError):self.collect(scope,altered)
        for code in (1,-9,False):
            with self.assertRaises(ValueError):self.collect(scope,rows,code)

    def test_visibility_and_structural_identity_affect_hash(self):
        scope,rows=self.fixture();_,old=self.collect(scope,rows)
        altered=copy.deepcopy(rows);altered[2][1]['protected_name']=True
        _,new=self.collect(scope,altered)
        self.assertNotEqual(old['kernel_interface_sha256'],new['kernel_interface_sha256'])
        altered=copy.deepcopy(rows);altered[2][1]['name_parts']=name('A.proof')
        _,new=self.collect(scope,altered)
        self.assertNotEqual(old['kernel_interface_sha256'],new['kernel_interface_sha256'])

    def test_duplicate_and_forward_edge_refused(self):
        scope,rows=self.fixture()
        altered=copy.deepcopy(rows);altered.insert(3,copy.deepcopy(altered[2]))
        with self.assertRaisesRegex(ValueError,'DUPLICATE'):self.collect(scope,altered)
        altered=copy.deepcopy(rows);altered[1][1].update(tag='app',data=None,children=[0,0])
        with self.assertRaises(ValueError):self.collect(scope,altered)

    def test_open_types_and_missing_visibility_refused(self):
        scope,rows=self.fixture()
        for tag,data in [('fvar',name('x')),('sort',['mvar',name('u')]),('bvar','0')]:
            altered=copy.deepcopy(rows);altered[1][1].update(tag=tag,data=data)
            with self.assertRaises(ValueError):self.collect(scope,altered)
        altered=copy.deepcopy(rows);del altered[2][1]['protected_name']
        with self.assertRaises(ValueError):self.collect(scope,altered)

    def test_hash_independent_of_unreferenced_node_ids(self):
        scope,rows=self.fixture();_,old=self.collect(scope,rows)
        altered=copy.deepcopy(rows)
        altered.insert(1,('H62-NODE',{'module':rows[1][1]['module'],'id':0,'tag':'sort','data':['zero'],'children':[]}))
        altered[2][1]['id']=1;altered[3][1]['type_root']=1;altered[5][1]['nodes']=2
        _,new=self.collect(scope,altered)
        self.assertEqual(old['kernel_interface_sha256'],new['kernel_interface_sha256'])

    def test_wrong_compiler_and_capture_commit_refused(self):
        scope,rows=self.fixture()
        for field,value in [('lean_version','4.35.0'),('lean_commit','0'*40),('source_commit','invalid')]:
            changed=copy.deepcopy(rows);changed[0][1][field]=value
            with self.assertRaises(ValueError):self.collect(scope,changed)
        with self.assertRaises(ValueError):
            audit.collect(scope,(line(*r) for r in rows),0,source_commit='b'*40)

    def test_provenance_binding(self):
        scope,_=self.fixture()
        with tempfile.TemporaryDirectory() as tmp:
            source=pathlib.Path(tmp)/'Fixture.lean'
            generator=audit.load('scripts/h62/item6/migrate-examples/generate-dag-inventory.py')
            source.write_text(generator.generate(sorted(r['module'] for r in scope['modules']),'a'*40,capture_id='Fixture'))
            log=pathlib.Path(tmp)/'Fixture.jsonl'
            fixture={'toolchain_version':audit.OLD_VERSION,'base':audit.BASE,'source_commit':'a'*40,'original_scope_modules':2,
                     'modules':sorted(r['module'] for r in scope['modules']),
                     'census_sha256':'c'*64,'pinned_closure_equal':True,
                     'capture_id':'Fixture','stream_file':'Fixture.jsonl','fixture_file':source.name,'fixture_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                     'inputs':[{'repository_path':p,'sha256':hashlib.sha256((audit.ROOT/p).read_bytes()).hexdigest()} for p in audit.INPUTS]}
            compiler={'command':['lake','env','lean','-j1','--tstack=131072',str(source)],'exit':0,'stop':None,'resource_violations':[]}
            audit.verify_provenance(scope,'c'*64,fixture,compiler,log)
            for field,value in [('toolchain_version','4.35.0'),('base','wrong'),('census_sha256','d'*64),('modules',[]),('inputs',[]),('fixture_sha256','0'*64),('pinned_closure_equal',False)]:
                changed=copy.deepcopy(fixture);changed[field]=value
                with self.assertRaises(ValueError):audit.verify_provenance(scope,'c'*64,changed,compiler,log)
            for field,value in [('exit',False),('stop','RESOURCE_STOP'),('command',['lean',str(source)])]:
                changed=copy.deepcopy(compiler);changed[field]=value
                with self.assertRaises(ValueError):audit.verify_provenance(scope,'c'*64,fixture,changed,log)

    def test_compiler_seal_binds_stream_capture(self):
        scope,rows=self.fixture();_,summary=self.collect(scope,rows)
        fixture={'capture_id':'fixture','stream_file':'stream.jsonl'}
        seal=dict(summary['compiler']);seal.update(stream_file='stream.jsonl',modules=2,kernel=1,compiler_extra=1)
        audit.verify_seal([line('H62-EXAMPLES-SEAL',seal)],summary,fixture)
        for field,value in [('capture_id','other'),('stream_file','wrong'),('kernel',2)]:
            changed=copy.deepcopy(seal);changed[field]=value
            with self.assertRaises(ValueError):audit.verify_seal([line('H62-EXAMPLES-SEAL',changed)],summary,fixture)
        with self.assertRaises(ValueError):audit.verify_seal([],summary,fixture)

    def test_legitimate_module_reemission_and_category_overlap_retained(self):
        scope,rows=self.fixture()
        changed=copy.deepcopy(rows)
        overlap=copy.deepcopy(changed[3]);overlap[1].update(name=changed[2][1]['name'],name_parts=changed[2][1]['name_parts'],internal=False)
        changed.insert(4,overlap);changed[5][1]['compiler_extra']=2;changed[-1][1]['compiler_extra']=2
        entries,summary=self.collect(scope,changed)
        self.assertEqual(summary['kernel_compiler_name_overlaps'],1)
        self.assertEqual(len(entries),3)
        # The same generated kernel name may be realized in another module.
        changed=copy.deepcopy(rows);z=scope['modules'][1]['module']
        node=copy.deepcopy(changed[1]);node[1]['module']=z
        decl=copy.deepcopy(changed[2]);decl[1]['module']=z
        changed[5:5]=[node,decl];changed[7][1].update(kernel=1,nodes=1);changed[-1][1]['kernel']=2
        entries,summary=self.collect(scope,changed)
        self.assertEqual(summary['module_data_kernel_reemissions'],1)
        self.assertEqual(summary['unique_kernel_names'],1)
        self.assertEqual(summary['kernel_names_with_multiple_signatures'],{})


if __name__=='__main__':unittest.main()
