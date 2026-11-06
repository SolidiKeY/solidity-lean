#!/usr/bin/env python3
"""Adversarial source/kernel linkage, namespace, premise-role and proof census controls."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
import generate_witnesses
import inventory
import verify_census


class InventoryTests(unittest.TestCase):
    def test_global_data_and_per_input_props_are_distinguished(self):
        self.assertEqual(inventory.classify(dict(type_head=inventory.S+"BinaryCertificate",is_proposition=False,instance_implicit=False)),"global-uniform-premise-structure")
        self.assertEqual(inventory.classify(dict(type_head=inventory.S+"BinaryInvocation",is_proposition=True,instance_implicit=False)),"per-input-feasibility-structure")
        self.assertEqual(inventory.classify(dict(type_head="[anonymous]",type="∀ a, a = a",is_proposition=True,instance_implicit=False)),"global-function-law")

    def test_actual_namespace_is_required_and_duplicate_markers_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp); tests=repo/"tests/h62/item2/audit-g25-scalar-lowering"; tests.mkdir(parents=True)
            text="namespace Actual.Namespace\n-- AUDIT-WITNESS: Original.theorem\ntheorem witness : True := True.intro\nend Actual.Namespace\n"
            (tests/"Fixture.lean").write_text(text)
            rows=[dict(name="Original.theorem",visibility="public")]
            self.assertEqual(verify_census.candidates(repo,rows)["Original.theorem"]["declaration"],"Actual.Namespace.witness")
            (tests/"Duplicate.lean").write_text(text)
            with self.assertRaisesRegex(ValueError,"duplicate witness"): verify_census.candidates(repo,rows)

    def test_duplicate_generator_inputs_fail_before_writes(self):
        row=dict(name="N.t",visibility="public",path="Solidity/F.lean")
        kernel=dict(name="N.t",binders=[],binder_count=0)
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError,"duplicate census"):
                generate_witnesses.render(Path(tmp),dict(theorems=[row]),[kernel,kernel])

    def test_mismatched_or_weakened_or_untrusted_verification_is_rejected(self):
        kernel=[dict(name="N.t",kernel_type="exact-frozen-type",binder_count=2)]
        links={"N.t":dict(declaration="Actual.Namespace.witness")}
        good=dict(name="N.t",witness="Actual.Namespace.witness",kernel_type="exact-frozen-type",checked_binders=2,
                  axioms=["propext"],status="verified-full-telescope-and-conclusion")
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/"verification.json"
            path.write_text(json.dumps([good]))
            self.assertEqual(len(verify_census.verified_rows(path,kernel,links)),1)
            cases=[dict(witness="Wrong.Namespace.witness"),dict(kernel_type="weakened"),dict(checked_binders=1),
                   dict(axioms=["sorryAx"]),dict(status="draft")]
            for change in cases:
                row=copy.deepcopy(good);row.update(change);path.write_text(json.dumps([row]))
                with self.subTest(change=change),self.assertRaises(ValueError): verify_census.verified_rows(path,kernel,links)

if __name__=="__main__": unittest.main()
