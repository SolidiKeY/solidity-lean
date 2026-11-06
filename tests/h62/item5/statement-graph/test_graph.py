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
        self.assertEqual(self.graph['counts'], dict(open=1,ready=1,blocked=1,done=1,total=4,openPremises=1))
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
