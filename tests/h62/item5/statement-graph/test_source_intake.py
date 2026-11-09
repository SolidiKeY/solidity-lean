"""Guard static G49 locations from typed counts, owner reassignment and discharge.

Fixtures are deliberately unelaborated source text. They exercise metadata
boundaries, not Lean declarations, real producer delivery or theorem proofs.
"""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
CODE = ROOT/'scripts/h62/item5/statement-graph'

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value

intake = module('h62source', CODE/'source_intake.py')
graph = module('h62sourcegraph', CODE/'graph.py')
EXPORT = {'schema':1, 'source':'Lean.ConstantInfo.type', 'declarations':[]}
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'


def fixture():
    bodies = {}
    for path, rows in intake.DECLARATIONS.items():
        lines = ['namespace Solidity.Roadmap.G49Final']
        for form, name in rows:
            lines.append(form+' '+name+' fixture')
            if name=='PublicObligations':
                lines += ['  '+field+' : Fixture' for field in intake.PUBLIC_FIELDS]
        lines.append('end Solidity.Roadmap.G49Final')
        bodies[path] = ('\n'.join(lines)+'\n').encode()
    files = {path:intake.sha(data) for path,data in bodies.items()}
    owners = dict(S='P8a-SPEC', I='G18.02', Asm='G49.01', V='G47', lowering='P8b',
                  backend='G49.01', execution='G49.02', compiler='G49.03', decode='G50.02',
                  sourceApproved='P8a-SPEC', sourceNonVacuous='P8a-SPEC', targetApproved='G47', keccak='G47',
                  coverage='G49.03', bothPipelines='G49.03', artifact='G49.02', fixed='G49.02',
                  session='G49.02', ifixed='G49.02', isession='G49.02', creates_table='G50.01',
                  hashes_source='G49.02', decode_reach='G50.02', decode_commutes='G50.02')
    registry = {'items':[{'id':key,'owner':'fixture-owner:'+key} for key in sorted(set(owners.values()))]+[{'id':'unassigned'}]}
    shapes = dict(exhaustiveLaneCoverage=False, owners=owners, binderOrder=list(intake.INPUTS+intake.PUBLIC_FIELDS),
                  checkedDeclarations=['producer-reported-only'], sourceHashes={'historical.lean':'f'*64})
    bridges = dict(families=[dict(family='family'+str(i),factory=intake.FACTORIES[i],status='pending',deliveredDeclaration=None) for i in range(5)],
                   checkedAgainst=dict(sha='0'*40,method='historical producer report'))
    metadata = {'shapes':shapes,'bridges':bridges}
    catalog = intake.assemble(files,bodies,metadata,{'shapes':'a'*64,'bridges':'b'*64},registry,'c'*40)
    return bodies, files, registry, metadata, catalog


class SourceIntakeTests(unittest.TestCase):
    def test_exact_inventory_bytes_and_headers(self):
        bodies, files, _, _, _ = fixture()
        header = ('Static source inventory from fetched origin/master '+intake.MASTER+'\nG49 checkpoint '+intake.CHECKPOINT+'\n\n').encode()
        raw = header + b''.join(('PATH '+p+' sha256 '+files[p]+'\n').encode()+data+b'\n\n' for p,data in bodies.items())
        self.assertEqual(intake.verify_inventory(raw,bodies.__getitem__,intake.sha(raw)),(files,bodies))
        with self.assertRaisesRegex(ValueError,'inventory SHA256'):
            intake.verify_inventory(raw+b'x',bodies.__getitem__,intake.sha(raw))
        changed = raw.replace(next(iter(bodies.values())),b'changed\n',1)
        with self.assertRaisesRegex(ValueError,'inline inventory differs'):
            intake.verify_inventory(changed,bodies.__getitem__,intake.sha(changed))
        wrong_source = dict(bodies);wrong_source[next(iter(bodies))] += b'changed'
        with self.assertRaisesRegex(ValueError,'source hash mismatch'):
            intake.verify_inventory(raw,wrong_source.__getitem__,intake.sha(raw))
        duplicate = raw+('PATH '+next(iter(files))+' sha256 '+next(iter(files.values()))+'\n').encode()
        with self.assertRaisesRegex(ValueError,'duplicate source path'):
            intake.verify_inventory(duplicate,bodies.__getitem__,intake.sha(duplicate))

    def test_owner_slices_preserve_global_open_fields(self):
        _,_,registry,_,catalog = fixture()
        g = graph.build(EXPORT,catalog,BASE,'d'*40,registry)
        self.assertEqual(g['counts']['typedDeclarations'],0)
        self.assertEqual(g['counts']['pendingInputs'],5)
        self.assertEqual(g['counts']['sourceLocatedInputs'],5)
        self.assertEqual(g['counts']['distinctLocatedSourceDeclarations'],1)
        self.assertIsNone(g['counts']['openPremises'])
        self.assertFalse(g['counts']['premiseInventoryComplete'])
        self.assertEqual(g['counts']['blocked'],5)
        self.assertEqual(g['sourceCounts']['namedOpenPublicFields'],15)
        self.assertEqual(g['sourceCounts']['sourceContextBindings'],9)
        self.assertEqual(g['sourceCounts']['certificatePackageAssumptions'],3)
        self.assertEqual(g['sourceCounts']['reportedBridgeRequests'],5)
        self.assertEqual(g['sourceCounts']['dischargedPremises'],0)
        self.assertIsNone(g['sourceCounts']['atomicOpenPremises'])
        self.assertEqual(len(g['sourceEvidence']['sourceBinderNames']),10)
        for row in g['nodes']:
            self.assertEqual(row['declaration'],intake.THEOREM)
            self.assertIsNone(row['exists']);self.assertIsNone(row['typeExpr'])
            self.assertFalse(row['dependenciesKnown']);self.assertEqual(row['dependencies'],[])
        fields = {p['name']:p for p in g['sourceEvidence']['sharedPublicObligations']}
        self.assertEqual(fields['sourceApproved']['ownerReference'],'P8a-SPEC')
        self.assertEqual(fields['keccak']['ownerReference'],'G47')
        self.assertEqual({p['status'] for p in fields.values()},{'open'})
        self.assertFalse(g['sourceEvidence']['freshLeanRun'])

    def test_source_locations_remain_unclaimable(self):
        _,_,registry,_,catalog = fixture()
        g = graph.build(EXPORT,catalog,BASE,'d'*40,registry)
        with tempfile.TemporaryDirectory() as tmp:
            for node in g['nodes']:
                with self.assertRaisesRegex(ValueError,'pending-input node cannot be claimed'):
                    graph.transact(Path(tmp)/'claims.json',g,'claim',node['id'],node['owner'])

    def test_no_source_metadata_can_promote_typed_or_done(self):
        _,_,registry,_,catalog = fixture()
        mutations = [
            lambda c:c['sourceSnapshot'].update(freshLeanRun=True),
            lambda c:c['sourceSnapshot'].update(premiseInventoryComplete=True),
            lambda c:c['sourceSnapshot'].update(typedDeclarations=5),
            lambda c:c['sourceSnapshot']['sharedPublicObligations'][0].update(status='done'),
            lambda c:c['sourceSnapshot']['reportedProducerGaps'][0].update(locallyVerifiedDelivery=True),
            lambda c:c['pendingInputs'][0].update(completed=True),
            lambda c:c['pendingInputs'][0]['sourceLocator'].update(exists=True),
            lambda c:c['nodes'].append({'id':'fake'}),
            lambda c:c['sourceSnapshot']['sharedPublicObligations'].pop(0),
            lambda c:c['sourceSnapshot']['sourceInputBindings'][5].update(role='context-or-function'),
            lambda c:c['sourceSnapshot']['declarationLocators'].pop(),
            lambda c:c['sourceSnapshot']['reportedProducerGaps'].pop(),
            lambda c:c['sourceSnapshot']['reportedProducerGaps'][0].update(requiredFactory='invented'),
            lambda c:c['pendingInputs'].pop(),
            lambda c:c['pendingInputs'][0].pop('sourceLocator'),
        ]
        for mutate in mutations:
            c=copy.deepcopy(catalog);mutate(c)
            with self.subTest(mutate=mutate),self.assertRaises(ValueError):graph.build(EXPORT,c,BASE,'d'*40,registry)

    def test_named_slots_and_provenance_cannot_be_reassigned(self):
        _,_,registry,_,catalog = fixture()
        mutations = [
            lambda c:c['pendingInputs'][0]['sourceLocator'].update(fileSha256='0'*64),
            lambda c:c['pendingInputs'][0]['sourceLocator'].update(sourceCommit='0'*40),
            lambda c:c['pendingInputs'][0]['sourceLocator'].update(declaration='invented'),
            lambda c:c['pendingInputs'][0]['sourceLocator']['ownerSlots'].pop(),
            lambda c:c['pendingInputs'][0]['sourceLocator']['ownerSlots'][0].update(index=0),
            lambda c:c['sourceSnapshot']['sharedPublicObligations'][0].update(owner='invented'),
        ]
        for mutate in mutations:
            c=copy.deepcopy(catalog);mutate(c)
            with self.subTest(mutate=mutate),self.assertRaises(ValueError):graph.build(EXPORT,c,BASE,'d'*40,registry)
        c=copy.deepcopy(catalog);c.pop('sourceSnapshot')
        with self.assertRaisesRegex(ValueError,'lacks snapshot'):graph.build(EXPORT,c,BASE,'d'*40,registry)

    def test_intake_does_not_flatten_binder_order_into_indices(self):
        bodies,files,registry,metadata,catalog = fixture()
        metadata['shapes']['binderOrder'].reverse()
        other = intake.assemble(files,bodies,metadata,{'shapes':'a'*64,'bridges':'b'*64},registry,'c'*40)
        self.assertEqual(catalog,other)
        self.assertEqual(catalog['pendingInputs'][0]['sourceLocator']['ownerSlots'],
                         [{'scope':'binder','name':'Asm'},{'scope':'binder','name':'backend'}])
        metadata['bridges']['families'][0]['status']='done'
        with self.assertRaisesRegex(ValueError,'changed producer delivery'):intake.assemble(files,bodies,metadata,{},registry,'c'*40)

    def test_deterministic_graph_without_source_promotion(self):
        _,_,registry,_,catalog = fixture()
        a=graph.build(EXPORT,catalog,BASE,'d'*40,registry)
        b=graph.build(EXPORT,copy.deepcopy(catalog),BASE,'d'*40,copy.deepcopy(registry))
        self.assertEqual(graph.canonical(a),graph.canonical(b))


if __name__=='__main__':unittest.main()
