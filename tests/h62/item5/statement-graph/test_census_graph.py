"""Guard census slots becoming proof credit or hiding production-view gaps.

Synthetic unelaborated metadata below tests classification/refusal only. The CLI
separately requires the exact authenticated source/log/output-bound census.
"""
import copy
from concurrent.futures import ThreadPoolExecutor
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


C = load('census_graph', ROOT/'scripts/h62/item5/statement-graph/census_graph.py')
FIXTURES = load('constructor_fixture', ROOT/'tests/h55/g49-final-theorem/test_constructor_slots.py')
POLICY = json.loads((ROOT/'tests/h55/g49-final-theorem/h64-shapes.json').read_text())


def inputs():
    snapshot = FIXTURES.fixture()
    for row in snapshot['declarations']:
        row.update(role='unclassified', type='Unelaborated type', typeExpr='Unelaborated type',
                   typeReferences=sorted({r for field in row['fields'] for r in field['references']}),
                   taggedReferences=[], proofReferences=[])
        if row['declaration'] in (C.PUBLIC, C.THEOREM):
            row['typeReferences'] += list(C.H55.PACKAGES.values())
        if row['declaration'] == C.THEOREM:
            row['typeReferences'].append(C.PUBLIC)
    ownership = {'items':[{'id':ref,'owner':'fixture-logical-owner'} for ref in sorted(set(POLICY['owners'].values()))]}
    pending = json.loads((ROOT/'tests/h62/item5/statement-graph/pending-inputs.json').read_text())
    for row in pending['pendingInputs']:
        row['owner'] = 'fixture-logical-owner'
    return snapshot, ownership, pending


class ConditionalCensus(unittest.TestCase):
    def build(self, snapshot, ownership, pending):
        catalog = C.catalog_for(snapshot, POLICY, ownership, pending)
        return C.GRAPH.build(snapshot, catalog, 'a'*40, 'b'*40, ownership)

    def test_typed_surface_and_production_gaps_remain_distinct(self):
        graph = self.build(*inputs())
        self.assertEqual(graph['counts'], dict(open=0,ready=0,blocked=12,done=0,total=12,
            typedDeclarations=7,pendingInputs=5,knownOpenPremises=72,dischargedPremises=0,
            premiseInventoryComplete=False,openPremises=None))
        self.assertEqual(graph['progress']['G49']['typedDeclarations'],7)
        self.assertEqual(graph['progress']['G49']['pendingInputs'],3)
        self.assertEqual(graph['progress']['G50']['typedDeclarations'],7)
        self.assertEqual(graph['progress']['G50']['pendingInputs'],2)
        # The overlapping closures are not two independent collections of proofs.
        self.assertEqual(set(graph['progress']['G49']['nodes']) & set(graph['progress']['G50']['nodes']),
                         set(C.SELECTION[name][0] for name in C.SELECTION))

    def test_every_generic_binder_and_field_preserves_its_exact_type(self):
        snapshot, ownership, pending = inputs()
        graph = self.build(snapshot, ownership, pending)
        by_id = {node['id']:node for node in graph['nodes']}
        for row in snapshot['declarations']:
            node = by_id[C.SELECTION[row['declaration']][0]]
            original = row['binders'] + row['fields']
            self.assertEqual([(p['name'],p['type'],p['typeExpr']) for p in node['premises']],
                             [(p['name'],p['type'],p['typeExpr']) for p in original])
            self.assertTrue(all(p['status']=='open' and 'witness' not in p for p in node['premises']))
        slots = C.H55.census(snapshot,POLICY,'fixture/collector')
        self.assertEqual(slots['totalSuppliedSlots'],54)
        self.assertIsNone(slots['atomicOpenPremises'])
        self.assertFalse(slots['productionSelectionComplete'])

    def test_missing_and_duplicate_logical_owner_refused(self):
        x, owners, pending = inputs()
        missing = copy.deepcopy(owners);missing['items'] = [r for r in missing['items'] if r['id']!='P8b']
        with self.assertRaisesRegex(ValueError,'missing logical owner'):
            self.build(x,missing,pending)
        owners['items'].append(copy.deepcopy(owners['items'][0]))
        with self.assertRaisesRegex(ValueError,'duplicate owner'):
            self.build(x,owners,pending)

    def test_omitted_pending_view_and_changed_roots_refused(self):
        x, owners, pending=inputs()
        missing=copy.deepcopy(pending);missing['pendingInputs'].pop()
        with self.assertRaisesRegex(ValueError,'five located pending'):
            self.build(x,owners,missing)
        pending['roots']['G49'].pop()
        with self.assertRaisesRegex(ValueError,'changed representative roots'):
            self.build(x,owners,pending)

    def test_nonstring_blank_and_placeholder_owners_refused(self):
        for invalid in [None,{},['owner'],'','  ',' owner ','unknown','-','unowned']:
            x, owners, pending=inputs()
            next(row for row in owners['items'] if row['id']=='P8b')['owner']=invalid
            with self.subTest(owner=invalid), self.assertRaisesRegex(ValueError,'missing logical owner'):
                self.build(x,owners,pending)

    def test_original_pending_catalog_is_not_mutated_or_reclassified(self):
        x, owners, pending = inputs();before=copy.deepcopy(pending)
        catalog = C.catalog_for(x,POLICY,owners,pending)
        self.assertEqual(pending,before)
        self.assertEqual({p['id'] for p in catalog['pendingInputs']},{p['id'] for p in before['pendingInputs']})
        self.assertTrue(all('sourceLocator' not in p for p in catalog['pendingInputs']))
        self.assertTrue(all('completed' not in row for row in catalog['nodes']))

    def test_unsealed_synthetic_run_cannot_enter_production_collector(self):
        with tempfile.TemporaryDirectory() as folder:
            run=Path(folder);(run/'results.json').write_text('[]')
            with self.assertRaisesRegex(ValueError,'unrecognized checked run'):
                C.checked_export(run)

    def test_output_is_complete_exclusive_and_race_safe(self):
        with tempfile.TemporaryDirectory() as folder:
            output=Path(folder)/'new.json'
            def publish(data):
                try:
                    C.write_new(output,data)
                    return True
                except FileExistsError:
                    return False
            with ThreadPoolExecutor(max_workers=2) as workers:
                successes=list(workers.map(publish,[b'first',b'second']))
            self.assertEqual(sorted(successes),[False,True])
            original=output.read_bytes()
            self.assertIn(original,[b'first',b'second'])
            with self.assertRaises(FileExistsError):C.write_new(output,original)
            self.assertEqual(output.read_bytes(),original)
            self.assertEqual(list(Path(folder).iterdir()),[output])

    def test_checkout_and_dangling_symlink_outputs_refused(self):
        with self.assertRaisesRegex(ValueError,'outside the repository'):
            C.write_new(ROOT/'tests/h62/item5/statement-graph/MUST-NOT-WRITE.json',b'no')
        with tempfile.TemporaryDirectory() as folder:
            target=Path(folder)/'missing';link=Path(folder)/'link';link.symlink_to(target)
            with self.assertRaisesRegex(ValueError,'symlink'):C.write_new(link,b'no')
            self.assertFalse(target.exists())

    def test_missing_constructor_field_is_not_hidden_by_graph_counts(self):
        x, owners, pending = inputs()
        next(row for row in x['declarations'] if row['declaration']==C.PUBLIC)['fields'].pop()
        with self.assertRaises(ValueError):
            self.build(x,owners,pending)


if __name__ == '__main__':
    unittest.main(verbosity=2)
