#!/usr/bin/env python3
"""Acceptance controls for reduced-premise inspection and H69 classification."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('semantic', Path(__file__).with_name('semantic_census.py'))
semantic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(semantic)
EV = Path('/workspace/h62-audit-readonly-calls/continuation-semantic/evidence')
EXACT = Path('/workspace/h62-audit-readonly-calls/continuation-h69/evidence/elaborated-signatures.json')
POLICY = Path(__file__).resolve().parents[4]/'tests/h62/item2/audit-readonly-calls/semantic-policy.json'


class SemanticAcceptance(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = semantic.exporter.census.census()
        cls.exact = json.loads(EXACT.read_text())
        cls.artifact = json.loads((EV/'semantic-types.json').read_text())
        cls.policy = json.loads(POLICY.read_text())

    def test_real_semantic_receipt_and_partition(self):
        semantic.verify_artifact(self.artifact, self.data, self.exact)
        kinds = [semantic.classification(r, self.policy) for r in self.artifact['declarations']]
        self.assertEqual(kinds.count('no-top-level-input-hypotheses'), 256)
        self.assertEqual(kinds.count('checked-joint-impossibility'), 42)
        self.assertEqual(kinds.count('pending'), 41)

    def test_binder_array_tampering_rejected(self):
        artifact = copy.deepcopy(self.artifact)
        row = next(r for r in artifact['declarations'] if r['inspection']['reducing_binders'])
        row['inspection']['reducing_binders'] = []
        with self.assertRaisesRegex(ValueError, 'canonical verified log'):
            semantic.verify_artifact(artifact, self.data, self.exact)

    def test_axiom_array_tampering_rejected(self):
        artifact = copy.deepcopy(self.artifact)
        artifact['declarations'][0]['axioms'] = ['sorryAx']
        with self.assertRaisesRegex(ValueError, 'canonical verified log'):
            semantic.verify_artifact(artifact, self.data, self.exact)

    def test_unreviewed_negative_is_not_auto_accepted(self):
        pin = self.policy['intentional_controls'][0]
        row = next(r for r in self.artifact['declarations'] if r['source_name'] == pin['source_name'])
        policy = copy.deepcopy(self.policy)
        policy['intentional_controls'] = [p for p in policy['intentional_controls'] if p['source_name'] != row['source_name']]
        self.assertEqual(semantic.classification(row, policy), 'pending')

    def test_unsupported_axiom_or_policy_rejected(self):
        row = copy.deepcopy(self.artifact['declarations'][0])
        row['axioms'].append('sorryAx')
        with self.assertRaisesRegex(ValueError, 'unsupported proof axiom'):
            semantic.classification(row, self.policy)
        policy = copy.deepcopy(self.policy)
        policy['allowed_axioms'].append('sorryAx')
        with self.assertRaisesRegex(ValueError, 'standard three'):
            semantic.classification(row, policy)

    def test_hidden_ordinary_inputs_remain_pending(self):
        for r in self.artifact['declarations']:
            if r['raw_head'] in ['Solidity.Lowering.Readonly.SourceHistory.Effect', 'Solidity.Lowering.Readonly.EnvironmentHistory.CallbackHistories', 'Solidity.Lowering.Readonly.StaticJournal.SameStorage', 'Function.Injective']:
                self.assertTrue(r['inspection']['reducing_binders'])
                self.assertEqual(semantic.classification(r, self.policy), 'pending')

    def test_type_pin_mutation_rejected(self):
        policy = copy.deepcopy(self.policy)
        policy['intentional_controls'][0]['raw_type_sha256'] = '0'*64
        row = next(r for r in self.artifact['declarations'] if r['source_name'] == policy['intentional_controls'][0]['source_name'])
        with self.assertRaisesRegex(ValueError, 'type pin'):
            semantic.classification(row, policy)


if __name__ == '__main__':
    unittest.main()
