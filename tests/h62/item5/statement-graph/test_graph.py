import copy
import importlib.util
import json
import multiprocessing
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('h62graph', ROOT/'scripts/h62/item5/statement-graph/graph.py')
g = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(g)
OVERLAY_SPEC = importlib.util.spec_from_file_location('h70overlay', ROOT/'scripts/h62/item5/statement-graph/owner_overlay.py')
overlay = importlib.util.module_from_spec(OVERLAY_SPEC)
OVERLAY_SPEC.loader.exec_module(overlay)
VERIFY_SPEC = importlib.util.spec_from_file_location('h62verify', ROOT/'scripts/h62/item5/statement-graph/verify.py')
verifier = importlib.util.module_from_spec(VERIFY_SPEC)
VERIFY_SPEC.loader.exec_module(verifier)
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
TREE = '1'*40


def inputs():
    # Unit models exercise validation; Lean fixture acceptance is a separate gate.
    def row(name, refs=(), proof=(), binders=(), theorem=False):
        return dict(declaration=name, role='unclassified', exists=True, type='True', typeExpr='Expr.sort 0',
                    typeReferences=list(refs), proofReferences=list(proof), binders=list(binders), fields=[], taggedReferences=[], fieldDeclarations=[], isTheorem=theorem, axioms=[])
    export = dict(schema=1, source='Lean.ConstantInfo.type', declarations=[
        row('P'), row('H', proof=['R']), row('L', proof=['H'], theorem=True),
        row('R', refs=['P'], proof=['L'], binders=[dict(name='assumption', type='P', typeExpr='P', isProp=True, references=['P'])])])
    catalog = dict(fixture=True, nodes=[dict(id=n, declaration=n, kind=k, area=a, owner='owner', **kw) for n,k,a,kw in [
        ('P','premise','producer',{}),('H','helper','helpers',{}),
        ('L','statement','producer',{'completed':True}),('R','statement','consumer',{'binderRoles':{'0':{'kind':'premise','owner':'premise-producer'}}})]], roots={'G49':['R'],'G50':['L']})
    return export, catalog


def contender(state, graph, queue):
    try:
        result = g.transact(state, graph, 'claim', 'P', 'owner', now=100)
        queue.put(('won', result['token']))
    except ValueError as exc:
        queue.put(('lost', str(exc)))


class GraphTests(unittest.TestCase):
    def test_refusal_controls_require_exact_error_diagnostic_bodies(self):
        expected = 'H62 witness requires kernel checking'
        self.assertFalse(verifier.has_error_diagnostic('/tmp/'+expected+'.lean: unknown module', expected))
        for message in [dict(severity='warning', data=expected),
                        dict(severity='error', data='Unknown constant at /tmp/'+expected+'.lean'),
                        dict(severity='error', data={'message': expected})]:
            self.assertFalse(verifier.has_error_diagnostic(json.dumps(message), expected))
        self.assertTrue(verifier.has_error_diagnostic(json.dumps(dict(severity='error', data=expected)), expected))

    def setUp(self):
        self.export, self.catalog = inputs()
        self.graph = g.build(self.export, self.catalog, BASE, TREE)
        self.tmp = tempfile.TemporaryDirectory()
        self.state = Path(self.tmp.name)/'state.json'

    def tearDown(self):
        self.tmp.cleanup()

    def reject(self, fragment):
        with self.assertRaisesRegex(ValueError, fragment):
            g.build(self.export, self.catalog, BASE, TREE)

    def test_type_edges_exclude_proof_helpers(self):
        nodes = {n['id']:n for n in self.graph['nodes']}
        self.assertEqual(nodes['R']['dependencies'], ['P'])
        self.assertEqual(nodes['R']['proofDependencies'], ['L'])
        self.assertEqual(nodes['L']['dependencies'], [])
        self.assertEqual(nodes['L']['proofHelpers'], ['H'])
        self.assertEqual(nodes['L']['status'], 'done')
        self.assertEqual(nodes['H']['status'], 'open')
        self.assertEqual(nodes['R']['premises'][0]['name'], 'assumption')
        self.assertEqual(self.graph['counts'], dict(open=1,ready=1,blocked=1,done=1,total=4,typedDeclarations=4,pendingInputs=0,knownOpenPremises=1,dischargedPremises=0,premiseInventoryComplete=True,openPremises=1))
        self.assertEqual(self.graph['progress']['G49']['nodes'], ['P','R'])
        self.assertEqual(self.graph['progress']['G49']['openPremises'], 1)

    def test_deterministic_order(self):
        self.export['declarations'].reverse()
        self.catalog['nodes'].reverse()
        # Hashes bind exact input order; payload topology/counts remain canonical.
        other = g.build(self.export, self.catalog, BASE, TREE)
        for key in ('nodes','counts','progress','areas'):
            self.assertEqual(self.graph[key], other[key])
        self.assertEqual(g.canonical(self.graph), g.canonical(g.build(*inputs(), BASE, TREE)))

    def test_dead_declaration(self):
        self.export['declarations'].pop()
        self.reject('dead declaration')

    def test_missing_exists(self):
        self.export['declarations'][0]['exists'] = False
        self.reject('dead declaration')

    def test_duplicate_declaration(self):
        self.export['declarations'].append(self.export['declarations'][0])
        self.reject('duplicate exported')

    def test_dead_root(self):
        self.catalog['roots']['G49'] = ['missing']
        self.reject('dead/empty progress root')

    def test_cycle(self):
        self.export['declarations'][0]['typeReferences'] = ['R']
        self.reject('dependency cycle')

    def test_self_cycle(self):
        self.export['declarations'][0]['typeReferences'] = ['P']
        self.reject('dependency cycle')

    def test_duplicate_ids(self):
        self.catalog['nodes'][0]['id'] = 'L'
        self.reject('duplicate node ID')

    def test_owner_required(self):
        self.catalog['nodes'][0]['owner'] = ''
        self.reject('missing area/owner')

    def test_tag_mismatch(self):
        self.export['declarations'][0]['role'] = 'helper'
        self.reject('tag/catalog')

    def test_unproved_completion(self):
        self.catalog['nodes'][0]['completed'] = True
        self.reject('checked theorem')

    def test_open_premise_completion(self):
        self.catalog['nodes'][-1]['completed'] = True
        self.export['declarations'][-1]['isTheorem'] = True
        self.reject('open named premises')

    def test_unapproved_axiom(self):
        self.export['declarations'][2]['axioms'] = ['sorryAx']
        self.reject('unapproved axiom')

    def test_invalid_provenance(self):
        with self.assertRaisesRegex(ValueError,'SHA1'):
            g.build(self.export,self.catalog,'wrong',TREE)
        altered = copy.deepcopy(self.graph)
        altered['tree'] = '2'*40
        with self.assertRaisesRegex(ValueError,'checksum'):
            g.transact(self.state,altered,'claim','P','owner')

    def test_hash_binds_base_tree_and_inputs(self):
        other = g.build(self.export,self.catalog,BASE,'2'*40)
        self.assertNotEqual(self.graph['graphSha256'],other['graphSha256'])
        self.assertEqual(self.graph['exportSha256'],other['exportSha256'])
        self.assertEqual(self.graph['tree'],TREE)

    def test_double_claim_and_wrong_owner(self):
        first = g.transact(self.state,self.graph,'claim','P','owner',now=100)
        before = self.state.read_bytes()
        for owner in ('owner','intruder'):
            with self.assertRaises(ValueError):
                g.transact(self.state,self.graph,'claim','P',owner,now=101)
        self.assertEqual(before,self.state.read_bytes())
        g.transact(self.state,self.graph,'release','P','owner',first['token'],now=102)
        self.assertEqual(g.read(self.state)['claims'],{})

    def test_stale_owner_and_expiry(self):
        first = g.transact(self.state,self.graph,'claim','P','owner',ttl=10,now=100)
        second = g.transact(self.state,self.graph,'claim','P','owner',ttl=10,now=111)
        self.assertNotEqual(first['token'],second['token'])
        before = self.state.read_bytes()
        for op in ('renew','release'):
            with self.assertRaisesRegex(ValueError,'stale owner/token'):
                g.transact(self.state,self.graph,op,'P','owner',first['token'],now=112)
        self.assertEqual(before,self.state.read_bytes())
        renewed = g.transact(self.state,self.graph,'renew','P','owner',second['token'],now=113)
        self.assertEqual(renewed['revision'],3)

    def test_stale_graph(self):
        g.transact(self.state,self.graph,'claim','P','owner',now=100)
        other = g.build(self.export,self.catalog,BASE,'2'*40)
        with self.assertRaisesRegex(ValueError,'stale graph state'):
            g.transact(self.state,other,'claim','P','owner',now=500)

    def test_missing_axiom_evidence_rejected(self):
        del self.export['declarations'][2]['axioms']
        with self.assertRaises(KeyError):
            g.build(self.export,self.catalog,BASE,TREE)

    def test_export_catalog_coverage(self):
        self.catalog['nodes'].pop(0)
        self.reject('catalog must cover')

    def test_omitted_tagged_dependency(self):
        self.catalog['nodes'].pop(0)
        self.export['declarations'].pop(0)
        self.export['declarations'][-1]['taggedReferences'] = ['P']
        self.reject('omitted tagged dependency')

    def test_type_valued_certificate(self):
        self.export['declarations'][-1]['binders'][0]['isProp'] = False
        self.export['declarations'][-1]['isTheorem'] = True
        self.catalog['nodes'][-1]['completed'] = True
        self.reject('open named premises')

    def test_unclassified_type_binder(self):
        self.export['declarations'][-1]['binders'][0]['isProp'] = False
        del self.catalog['nodes'][-1]['binderRoles']
        self.reject('unclassified/missing typed binder')

    def test_interface_cannot_be_data_parameter(self):
        self.export['declarations'][-1]['binders'][0]['isProp'] = False
        self.catalog['nodes'][-1]['binderRoles']['0'] = {'kind':'parameter','reason':'misclassification'}
        self.reject('proof/interface binder')

    def test_premise_producer_owner(self):
        node = next(n for n in self.graph['nodes'] if n['id']=='R')
        self.assertEqual(node['premises'][0]['owner'],'premise-producer')
        self.catalog['nodes'][-1]['binderRoles']['0']['owner'] = ''
        self.reject('producer owner')

    def test_structure_fields_are_open_premises(self):
        self.export['declarations'][0]['fields'] = [dict(name='sound',type='True',typeExpr='True',isProp=True,references=[])]
        self.catalog['nodes'][0]['binderRoles'] = {'field:0':{'kind':'premise','owner':'field-producer'}}
        graph = g.build(self.export,self.catalog,BASE,TREE)
        node = next(n for n in graph['nodes'] if n['id']=='P')
        self.assertEqual(node['status'],'blocked')
        self.assertEqual(node['premises'][0]['name'],'sound')

    def test_production_owner_validation(self):
        catalog = copy.deepcopy(self.catalog)
        del catalog['fixture']
        with self.assertRaisesRegex(ValueError,'ownership snapshot'):
            g.build(self.export,catalog,BASE,TREE)
        ownership = {'items':[{'id':'producer-item','owner':'owner'},{'id':'premise-item','owner':'premise-producer'}]}
        for node in catalog['nodes']:
            node['ownerReference']='producer-item'
        catalog['nodes'][-1]['binderRoles']['0']['ownerReference']='premise-item'
        graph = g.build(self.export,catalog,BASE,TREE,ownership)
        self.assertFalse(graph['fixture'])
        self.assertEqual(graph['ownershipSha256'],g.digest(ownership))
        ownership['items'][1]['owner']='new-owner'
        with self.assertRaisesRegex(ValueError,'owner snapshot mismatch'):
            g.build(self.export,catalog,BASE,TREE,ownership)

    def test_production_pending_inventory(self):
        catalog = g.read(ROOT/'tests/h62/item5/statement-graph/pending-inputs.json')
        source = catalog['sourceSnapshot']
        records = catalog['pendingInputs']+source['sourceInputBindings']+source['sharedPublicObligations']
        assignments = {p['ownerReference']:p['owner'] for p in records}
        ownership = {'items':[{'id':ref,'owner':owner} for ref,owner in assignments.items()]}
        export = dict(schema=1,source='Lean.ConstantInfo.type',declarations=[])
        graph = g.build(export,catalog,BASE,TREE,ownership)
        self.assertFalse(graph['fixture'])
        self.assertEqual(graph['counts']['blocked'],5)
        self.assertEqual(graph['counts']['pendingInputs'],5)
        self.assertEqual(graph['counts']['typedDeclarations'],0)
        self.assertEqual(graph['counts']['knownOpenPremises'],0)
        self.assertIsNone(graph['counts']['openPremises'])
        self.assertFalse(graph['counts']['premiseInventoryComplete'])
        self.assertEqual(graph['progress']['G49']['pendingInputs'],3)
        self.assertEqual(graph['progress']['G50']['pendingInputs'],2)
        for node in graph['nodes']:
            self.assertEqual(node['inputStatus'],'pending-input')
            self.assertEqual(node['declaration'],source['theorem'])
            self.assertEqual(node['declarationEvidence'],'static-source-only')
            self.assertIsNone(node['exists'])
            self.assertIsNone(node['typeExpr'])
            self.assertFalse(node['dependenciesKnown'])
            with self.assertRaisesRegex(ValueError,'pending-input'):
                g.transact(self.state,graph,'claim',node['id'],node['owner'])
        self.assertFalse(self.state.exists())
        other = copy.deepcopy(catalog)
        other['pendingInputs'][0]['owner']='unrelated-owner'
        with self.assertRaisesRegex(ValueError,'owner snapshot mismatch'):
            g.build(export,other,BASE,TREE,ownership)

    def test_mixed_pending_inputs_preserve_available_graph(self):
        entry = dict(id='pending',area='consumer',owner='owner',ownerReference='item',
                     inputArtifact='shapes.json',reason='not yet supplied',source='test producer')
        self.catalog['pendingInputs']=[entry]
        self.catalog['roots']['G49'].append('pending')
        graph=g.build(self.export,self.catalog,BASE,TREE)
        for node in self.graph['nodes']:
            self.assertEqual(node,next(n for n in graph['nodes'] if n['id']==node['id']))
        self.assertEqual(graph['counts']['done'],1)
        self.assertEqual(graph['counts']['blocked'],2)
        self.assertEqual(graph['counts']['knownOpenPremises'],1)
        self.assertIsNone(graph['counts']['openPremises'])
        self.assertFalse(graph['progress']['G49']['premiseInventoryComplete'])
        self.assertTrue(graph['progress']['G50']['premiseInventoryComplete'])
        self.assertEqual(g.canonical(graph),g.canonical(g.build(self.export,self.catalog,BASE,TREE)))
        for field,value in (('completed',True),('declaration','Invented.theorem'),('dependencies',['L'])):
            modified=copy.deepcopy(self.catalog)
            modified['pendingInputs'][0][field]=value
            with self.assertRaisesRegex(ValueError,'only nonempty provenance'):
                g.build(self.export,modified,BASE,TREE)
        self.catalog['pendingInputs'][0]['id']='L'
        self.reject('duplicate typed/pending')

    def test_h70_exact_base_target_and_original_preservation(self):
        source = ROOT/overlay.REL_PATH
        before = source.read_bytes()
        dest,meta = overlay.prepare(Path(self.tmp.name)/'source')
        self.assertEqual(overlay.blob(before),meta['baseBlob'])
        self.assertEqual(overlay.blob(dest.read_bytes()),meta['targetBlob'])
        self.assertTrue(meta['targetBlob'].startswith('092971eda'))
        self.assertEqual(source.read_bytes(),before)
        self.assertEqual(overlay.prepare(Path(self.tmp.name)/'source'),(dest,meta))

    def test_h70_wrong_base_and_checkout_destination(self):
        meta = g.read(overlay.BUNDLE/'h70-collision-bound.json')
        with self.assertRaisesRegex(ValueError,'base mismatch'):
            overlay.check_base(b'wrong base',meta)
        with self.assertRaisesRegex(ValueError,'outside every registered checkout'):
            overlay.prepare(ROOT/'tests/h62/item5/statement-graph/not-created')
        self.assertFalse((ROOT/'tests/h62/item5/statement-graph/not-created').exists())

    def test_h70_rejects_preserved_original_checkout(self):
        target = Path('/workspace/solidity-lean/.h62-h70-overlay-must-not-be-created')
        before = target.exists()
        with self.assertRaisesRegex(ValueError,'outside every registered checkout'):
            overlay.prepare(target)
        self.assertEqual(target.exists(),before)

    def test_h70_preserves_unexpected_existing_copy(self):
        copy_root = Path(self.tmp.name)/'source'
        dest = copy_root/overlay.REL_PATH
        dest.parent.mkdir(parents=True)
        dest.write_bytes(b'preserve unexpected work')
        with self.assertRaisesRegex(ValueError,'refusing to overwrite'):
            overlay.prepare(copy_root)
        self.assertEqual(dest.read_bytes(),b'preserve unexpected work')

    def test_h70_rejects_changed_relay_patch(self):
        original_bundle = overlay.BUNDLE
        changed = Path(self.tmp.name)/'changed-relay'
        changed.mkdir()
        for name in ('h70-collision-bound.patch.json','h70-collision-bound.json'):
            (changed/name).write_bytes((original_bundle/name).read_bytes())
        changed_patch = g.read(changed/'h70-collision-bound.patch.json')
        changed_patch['patch'] += 'changed'
        (changed/'h70-collision-bound.patch.json').write_text(json.dumps(changed_patch))
        overlay.BUNDLE = changed
        try:
            with self.assertRaisesRegex(ValueError,'patch identity mismatch'):
                overlay.prepare(Path(self.tmp.name)/'not-created')
        finally:
            overlay.BUNDLE = original_bundle
        self.assertFalse((Path(self.tmp.name)/'not-created').exists())

    def witness_model(self, prior=False, typed=False):
        export,catalog=inputs()
        proof_binders=[]
        roles={}
        if prior:
            proof_binders.append(dict(name='unproved',type='False',typeExpr='False',isProp=True,references=[]))
            roles['0']={'kind':'premise','owner':'proof-owner'}
        index=len(proof_binders)
        key=str(index)
        ty='Certificate' if typed else 'True'
        evidence=dict(consumer='R',scope='binder',index=index,declaration='W',checkedDeclaration='Checked.R.'+key,
                      kernelChecked=True,binderTypeExpr=ty,expectedTypeExpr='closed:'+ty,helperTypeExpr='closed:'+ty,
                      priorBinders=['0'] if prior else [],axioms=[])
        proof_binders.append(dict(name='cert' if typed else 'proof',type=ty,typeExpr=ty,isProp=not typed,references=[],witness=evidence))
        roles[key]={'kind':'premise','owner':'proof-owner'}
        row=copy.deepcopy(export['declarations'][2]);row.update(declaration='R',binders=proof_binders,typeReferences=[],proofReferences=[],isTheorem=True)
        producer=copy.deepcopy(export['declarations'][2]);producer.update(declaration='W',binders=[],typeReferences=[],proofReferences=[],isTheorem=not typed)
        return dict(schema=1,source='Lean.ConstantInfo.type',declarations=[row,producer]),dict(fixture=True,nodes=[
            dict(id='R',declaration='R',kind='statement',area='consumer',owner='consumer-owner',binderRoles=roles,completed=not prior),
            dict(id='W',declaration='W',kind='helper',area='producer',owner='proof-owner')],roots={'G49':['R']})

    def test_checked_witness_discharges_exact_premise(self):
        export,catalog=self.witness_model()
        graph=g.build(export,catalog,BASE,TREE)
        root=next(n for n in graph['nodes'] if n['id']=='R')
        self.assertEqual(root['status'],'done')
        self.assertEqual(root['premises'][0]['status'],'done')
        self.assertEqual(root['witnessDependencies'],['W'])
        self.assertEqual(root['dependencies'],[])
        self.assertEqual(graph['counts']['openPremises'],0)
        self.assertEqual(graph['counts']['dischargedPremises'],1)

    def test_checked_type_certificate_and_prior_open_condition(self):
        export,catalog=self.witness_model(typed=True)
        graph=g.build(export,catalog,BASE,TREE)
        self.assertEqual(next(n for n in graph['nodes'] if n['id']=='R')['status'],'done')
        export,catalog=self.witness_model(prior=True)
        graph=g.build(export,catalog,BASE,TREE)
        root=next(n for n in graph['nodes'] if n['id']=='R')
        self.assertEqual(root['status'],'blocked')
        self.assertEqual(root['premises'][1]['blockedByPremises'],['R#0'])
        self.assertEqual(graph['counts']['openPremises'],2)
        self.assertEqual(graph['counts']['dischargedPremises'],0)
        root_spec=next(n for n in catalog['nodes'] if n['id']=='R');root_spec['completed']=True
        with self.assertRaisesRegex(ValueError,'open named premises'):
            g.build(export,catalog,BASE,TREE)

    def test_checked_witness_rejects_wrong_identity_type_axioms_and_prerequisites(self):
        mutations=[('consumer','Other','location mismatch'),('scope','field','location mismatch'),('index',True,'location mismatch'),
                   ('kernelChecked',False,'kernel check'),('binderTypeExpr','Wrong','type evidence mismatch'),
                   ('helperTypeExpr','Wrong','type evidence mismatch'),('axioms',['Classical.choice'],'axiom-free'),
                   ('priorBinders',['0'],'prerequisite inventory'),('declaration','Missing','dead/unclassified')]
        for field,value,pattern in mutations:
            with self.subTest(field=field):
                export,catalog=self.witness_model()
                export['declarations'][0]['binders'][0]['witness'][field]=value
                with self.assertRaisesRegex(ValueError,pattern):g.build(export,catalog,BASE,TREE)
        export,catalog=self.witness_model(prior=True)
        export['declarations'][0]['binders'][1]['witness']['priorBinders']=[]
        with self.assertRaisesRegex(ValueError,'prerequisite inventory'):g.build(export,catalog,BASE,TREE)

    def test_checked_witness_requires_producer_owner_and_axiom_evidence(self):
        export,catalog=self.witness_model()
        catalog['nodes'][1]['owner']='another-owner'
        with self.assertRaisesRegex(ValueError,'producer owner mismatch'):g.build(export,catalog,BASE,TREE)
        export,catalog=self.witness_model()
        export['declarations'][1]['axioms']=['sorryAx']
        with self.assertRaisesRegex(ValueError,'axiom-dependent'):g.build(export,catalog,BASE,TREE)

    def test_checked_field_witnesses_require_constructor_prefix_and_do_not_complete_type(self):
        export,catalog=self.witness_model()
        root=export['declarations'][0]
        proof=root['binders'][0]
        root['binders']=[dict(name='n',type='Nat',typeExpr='Nat',isProp=False,references=[])]
        first=copy.deepcopy(proof);first['name']='first'
        first['witness'].update(scope='field',index=0,priorBinders=['0'],checkedDeclaration='Checked.R.field0')
        second=copy.deepcopy(first);second['name']='second'
        second['witness'].update(index=1,priorBinders=['0','field:0'],declaration='W2',checkedDeclaration='Checked.R.field1')
        root['fields']=[first,second];root['isTheorem']=False
        producer=copy.deepcopy(export['declarations'][1]);producer['declaration']='W2';export['declarations'].append(producer)
        spec=catalog['nodes'][0];spec['completed']=False
        spec['binderRoles']={'0':{'kind':'parameter','reason':'ordinary data'},'field:0':{'kind':'premise','owner':'proof-owner'},'field:1':{'kind':'premise','owner':'proof-owner'}}
        catalog['nodes'].append(dict(id='W2',declaration='W2',kind='helper',area='producer',owner='proof-owner'))
        graph=g.build(export,catalog,BASE,TREE)
        row=next(n for n in graph['nodes'] if n['id']=='R')
        self.assertEqual(row['status'],'ready')
        self.assertEqual([p['status'] for p in row['premises']],['done','done'])
        self.assertEqual(graph['counts']['dischargedPremises'],2)
        second['witness']['priorBinders']=['field:0']
        with self.assertRaisesRegex(ValueError,'prerequisite inventory'):g.build(export,catalog,BASE,TREE)

    def test_checked_helper_identity_cannot_be_replayed_at_another_target(self):
        export,catalog=self.witness_model()
        second=copy.deepcopy(export['declarations'][0]['binders'][0])
        second['name']='second'
        second['witness'].update(index=1,priorBinders=['0'])
        export['declarations'][0]['binders'].append(second)
        catalog['nodes'][0]['binderRoles']['1']={'kind':'premise','owner':'proof-owner'}
        with self.assertRaisesRegex(ValueError,'duplicate checked witness helper'):g.build(export,catalog,BASE,TREE)

    def test_imported_witness_conflict_requires_diagnostic_body(self):
        filename='witness-overlay-conflict.lean'
        setup=dict(fileName=filename,severity='error',data='unknown module prefix WitnessOverlayA')
        self.assertFalse(verifier.is_witness_conflict_diagnostic(json.dumps(setup)))
        self.assertFalse(verifier.is_witness_conflict_diagnostic(filename+':1:0: error: unknown module'))
        real=dict(fileName=filename,severity='error',data='conflicting imported H62 witnesses')
        self.assertTrue(verifier.is_witness_conflict_diagnostic(json.dumps(real)))
        duplicate=dict(fileName=filename,severity='error',data="import WitnessOverlayB failed, environment already contains 'H62.CheckedWitness.H62Fixture.root.binder_1' from WitnessOverlayA")
        self.assertTrue(verifier.is_witness_conflict_diagnostic(json.dumps(duplicate)))
        duplicate['data']="environment already contains 'Unrelated.declaration'"
        self.assertFalse(verifier.is_witness_conflict_diagnostic(json.dumps(duplicate)))

    def test_bad_lease_and_done_node(self):
        for ttl in (0,-1,float('nan'),float('inf'),86401):
            with self.assertRaisesRegex(ValueError,'lease time'):
                g.transact(self.state,self.graph,'claim','P','owner',ttl=ttl)
        with self.assertRaisesRegex(ValueError,'completed node'):
            g.transact(self.state,self.graph,'claim','L','owner')

    def test_concurrent_exclusive_claim(self):
        ctx = multiprocessing.get_context('spawn')
        queue = ctx.Queue()
        workers = [ctx.Process(target=contender,args=(str(self.state),self.graph,queue)) for _ in range(12)]
        for worker in workers:
            worker.start()
        for worker in workers:
            worker.join(20)
            self.assertEqual(worker.exitcode,0)
        outcomes = [queue.get(timeout=2) for _ in workers]
        self.assertEqual(sum(o[0]=='won' for o in outcomes),1)
        self.assertEqual(g.read(self.state)['revision'],1)
        self.assertEqual(len(g.read(self.state)['claims']),1)
        self.assertEqual(list(Path(self.tmp.name).glob('.state.json.*')),[])

if __name__ == '__main__':
    unittest.main(verbosity=2)
