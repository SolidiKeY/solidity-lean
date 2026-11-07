"""Guard lost obligations, hidden body/dependency drift and false proof promotion."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec=importlib.util.spec_from_file_location('current_ledger',Path(__file__).with_name('current_dependencies.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


def node(path,blob='same',imports=None,status='parsed-header'):
    return {'path':path,'git_blob':blob,'source_sha256':blob,'header_sha256':'header',
            'module':m.headers.encoded(Path(path).with_suffix('').parts),'status':status,'imports':imports or []}


def edge(path):return {'module':m.headers.encoded(Path(path).with_suffix('').parts),'implicit':False,'importAll':False,'isMeta':False,'isExported':True,'resolution':{'status':'project-source','path':path}}


class CurrentDependencyControls(unittest.TestCase):
    def setUp(self):
        files=[f'A{i}.lean' for i in range(129)]
        self.rows=[{'file':files[i%129],'source_name':f'N.t{i}','signature':'unchanged statement','signature_sha256':f's{i}','variable_context':[],'visibility':'private' if i==0 else 'public','owner':'historical only','witness_status':'pending'} for i in range(792)]
        self.frozen={'base':m.headers.BASE,'theorem_count':792,'modules':[{'file':f} for f in files],'declarations':self.rows,'map_sha256':'map'}
        self.nodes=[node(f) for f in files]
        self.graph={'schema':1,'kind':m.original.KIND,'original_base':m.headers.BASE,'original_obligations':792,'frozen_target_files':129,'frozen_map_sha256':'map','held_module':m.headers.HELD,'source_head':'captured','nodes':self.nodes}
        self.base={f:{'mode':'100644','kind':'blob','blob':'same'} for f in files}
        self.refresh()

    def refresh(self):self.graph['targets']=m.headers.target_records(self.nodes,[x['file'] for x in self.frozen['modules']])

    def test_exact_obligations_historical_owner_and_no_credit(self):
        result=m.account(self.frozen,self.graph,self.rows,self.base)
        self.assertEqual(len(result['rows']),792);self.assertEqual(len(result['modules']),129)
        self.assertEqual(result['original_obligations_discharged'],0);self.assertFalse(result['runtime_gate_pass'])
        for row in result['rows']:
            self.assertEqual(row['frozen'],self.rows[int(row['frozen']['source_name'][3:])])
            self.assertEqual(row['current_kernel_fidelity'],'pending');self.assertEqual(row['live_ownership'],'unverified');self.assertEqual(row['timing_hold'],'retained')

    def test_unchanged_signature_changed_dependency_is_visible(self):
        before=m.account(self.frozen,self.graph,self.rows,self.base)
        self.nodes[0]['imports']=[edge('A1.lean')];self.nodes[1].update(git_blob='changed-body',source_sha256='changed-body');self.refresh()
        after=m.account(self.frozen,self.graph,self.rows,self.base)
        self.assertEqual(after['current_lexical_statuses'],{'lexical-header-retained':792})
        observed=next(x for x in after['modules'] if x['target']=='A0.lean')
        self.assertEqual(observed['changed_since_original_base'],['A1.lean'])
        self.assertNotEqual(observed['fingerprint'],before['modules'][0]['fingerprint'])

    def test_private_absence_never_removes_original(self):
        result=m.account(self.frozen,self.graph,self.rows[1:],self.base)
        missing=[x for x in result['rows'] if x['current_lexical_status']=='absent-upstream']
        self.assertEqual(len(missing),1);self.assertEqual(missing[0]['frozen'],self.rows[0]);self.assertEqual(len(result['rows']),792)

    def test_cycles_and_input_node_order(self):
        nodes=[node('A.lean',imports=[edge('B.lean')]),node('B.lean',imports=[edge('A.lean')])]
        a=m.closure(nodes,'A.lean',{});b=m.closure(list(reversed(nodes)),'A.lean',{})
        self.assertEqual(a,b);self.assertEqual(a['declared_source_nodes'],2);self.assertTrue(a['complete_declared_observation']);self.assertEqual(a['timing_hold'],'retained')

    def test_unresolved_missing_and_header_failure_stay_explicit(self):
        for nodes in [[],[node('A.lean',imports=[edge('Missing.lean')])],[node('A.lean',status='header-error')],[node('A.lean',imports=[{'resolution':{'status':'unresolved-module'},'module':['anonymous']}])]]:
            result=m.closure(nodes,'A.lean',{})
            self.assertFalse(result['complete_declared_observation']);self.assertTrue(result['unresolved'])
        self.nodes[0]['imports']=[edge(m.headers.HELD)];self.refresh()
        result=m.account(self.frozen,self.graph,self.rows,self.base)
        row=next(x for x in result['rows'] if x['frozen']['file']=='A0.lean')
        self.assertEqual(row['current_declared_dependency']['status'],'declared-path-to-held-module');self.assertEqual(row['timing_hold'],'retained')

    def test_forged_dependency_report_and_duplicate_nodes_refused(self):
        self.nodes[0]['imports']=[edge(m.headers.HELD)]
        with self.assertRaisesRegex(ValueError,'path/report'):m.account(self.frozen,self.graph,self.rows,self.base)
        self.nodes[0]['imports']=[];self.nodes.append(copy.deepcopy(self.nodes[0]))
        with self.assertRaisesRegex(ValueError,'duplicate path'):m.account(self.frozen,self.graph,self.rows,self.base)

    def test_import_flags_and_sdk_hash_part_of_fingerprint(self):
        item={'module':['anonymous'],'importAll':False,'resolution':{'status':'sdk-artifact-observed-not-loaded','artifact_sha256':'one'}}
        original=m.closure([node('A.lean',imports=[item])],'A.lean',{})
        for changed in [dict(item,importAll=True),dict(item,resolution={'status':'sdk-artifact-observed-not-loaded','artifact_sha256':'two'})]:
            self.assertNotEqual(m.closure([node('A.lean',imports=[changed])],'A.lean',{})['fingerprint'],original['fingerprint'])

    def test_returned_child_receipt_substitution_refused(self):
        returned={'schema':1,'status':'pass','inventory_sha256':'actual'}
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'receipt.json';path.write_text(json.dumps(returned,indent=2)+'\n')
            expected=m.authenticate_capture(path,returned)
            self.assertEqual(expected,m.original.sha(path.read_bytes()))
            substituted=dict(returned,inventory_sha256='forged')
            path.write_text(json.dumps(substituted,indent=2)+'\n')
            with self.assertRaisesRegex(ValueError,'SHA256'):m.authenticate_capture(path,returned)
            with self.assertRaisesRegex(ValueError,'unsuccessful'):m.authenticate_capture(path,{'status':'failed'})

    def test_modules_without_theorems_and_lost_originals(self):
        frozen=copy.deepcopy(self.frozen)
        for row in frozen['declarations']:row['file']='A0.lean'
        result=m.account(frozen,self.graph,frozen['declarations'],self.base)
        self.assertEqual(sum(x['original_declarations']==0 for x in result['modules']),128)
        frozen['declarations'].pop()
        with self.assertRaises(ValueError):m.account(frozen,self.graph,self.rows,self.base)


if __name__=='__main__':unittest.main()
