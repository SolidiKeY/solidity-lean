"""Unelaborated metadata fixtures test accounting refusals, not Lean proofs."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("constructor_slots", ROOT / "scripts/h55/g49-final-theorem/constructor-slots.py")
tool = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(tool)
POLICY = json.loads((ROOT / "tests/h55/g49-final-theorem/h64-shapes.json").read_text())


def fixture():
    p = "Solidity.Roadmap."
    specs = {
        p+"Lowering": (["S", "I"], [("lower", False), ("pass", False), ("dom", True), ("agrees", True), ("cert", False)]),
        p+"Compilation": (["I", "Asm"], [("compile", False), ("pass", False), ("dom", True), ("agrees", True), ("cert", False)]),
        p+"Execution": (["Asm", "V"], [("assemble", False), ("pass", False), ("dom", True), ("agrees", True), ("cert", False)]),
        p+"Pass": (["E", "O", "A", "B"], [("Dom", False), ("run", False), ("envAbs", False)]),
        p+"Cert": (["E", "O", "A", "B", "pass"], [("envSound", True), ("envOnto", True), ("need", False), ("need_ok", True), ("back", True)]),
        tool.PUBLIC: (POLICY["binderOrder"][:9], [(name, True) for name in POLICY["binderOrder"][9:]]),
        tool.THEOREM: (POLICY["binderOrder"][:9] + ["obligations"], []),
    }
    rows = []
    for name, (binders, fields) in specs.items():
        rows.append(dict(declaration=name, exists=True, isTheorem=name == tool.THEOREM,
                         axioms=[], binders=[dict(name=n, isProp=n == "obligations", type="Unelaborated binder",
                                               typeExpr="Unelaborated binder", contextSize=i, references=[])
                                  for i,n in enumerate(binders)],
                         fieldDeclarations=[name+"."+f for f, _ in fields],
                         fields=[dict(name=f, isProp=prop, contextSize=len(binders)+i,
                                      type="Unelaborated fixture", typeExpr="Unelaborated fixture",
                                      references=[p+{"pass":"Pass", "cert":"Cert"}[f]] if f in ("pass", "cert") else [])
                                 for i, (f, prop) in enumerate(fields)]))
    return dict(schema=1, source="Lean.ConstantInfo.type", declarations=rows)


def row(snapshot, name):
    return next(r for r in snapshot["declarations"] if r["declaration"] == name)


class ConstructorSlotControls(unittest.TestCase):
    def test_slots_are_not_atoms_or_discharge(self):
        out = tool.census(fixture(), POLICY, "coordinator")
        self.assertEqual((out["packageLeafSlots"], out["packagePropSlots"], out["packageDataSlots"],
                          out["namedPublicPropFields"], out["totalSuppliedSlots"]), (33, 18, 15, 15, 54))
        self.assertEqual((out["aggregateTheoremBinders"], out["topLevelConstructorBinders"]), (10, 24))
        self.assertEqual(len(out["suppliedSlots"]), 54)
        opaque = [r for r in out["suppliedSlots"] if "theoremContext" in r]
        self.assertEqual([r["path"] for r in opaque], ["S", "I", "Asm", "V", "compiler", "decode"])
        self.assertTrue(all(r["logicalObligation"] and r["theoremContext"]["binder"]["typeExpr"] for r in opaque))
        self.assertIsNone(out["atomicOpenPremises"])
        self.assertFalse(out["productionSelectionComplete"])
        self.assertFalse(out["premiseDischargeClaim"])
        self.assertTrue(all(not r["concreteProducerSupplied"] for r in out["suppliedSlots"]))

    def test_generic_constructor_contexts_are_retained(self):
        out = tool.census(fixture(), POLICY, "coordinator")
        field = next(r for r in out["suppliedSlots"] if r["path"] == "lowering.cert.back")
        self.assertEqual([x["projection"] for x in field["constructorContexts"]],
                         ["Solidity.Roadmap.Lowering.cert", "Solidity.Roadmap.Cert.back"])
        self.assertEqual(field["logicalObligation"], "P8b")
        self.assertEqual(field["deliveryLane"], "coordinator")

    def test_missing_and_duplicate_declarations_refused(self):
        x = fixture(); x["declarations"].pop()
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")
        x = fixture(); x["declarations"].append(copy.deepcopy(x["declarations"][0]))
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")

    def test_hidden_field_refused(self):
        x = fixture(); row(x, "Solidity.Roadmap.Cert")["fields"].pop()
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")

    def test_prop_data_relabel_refused(self):
        x = fixture(); row(x, "Solidity.Roadmap.Pass")["fields"][0]["isProp"] = True
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")

    def test_constructor_reorder_refused(self):
        x = fixture(); row(x, "Solidity.Roadmap.Cert")["fields"].reverse()
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")

    def test_nested_reference_and_projection_refused(self):
        x = fixture(); row(x, "Solidity.Roadmap.Lowering")["fields"][1]["references"] = []
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")
        x = fixture(); row(x, "Solidity.Roadmap.Cert")["fieldDeclarations"].pop()
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")

    def test_unexpected_axiom_and_owner_refused(self):
        x = fixture(); row(x, tool.THEOREM)["axioms"] = ["sorryAx"]
        with self.assertRaises(tool.BASE.Invalid): tool.census(x, POLICY, "coordinator")
        policy = copy.deepcopy(POLICY); policy["owners"]["lowering"] = ""
        with self.assertRaises(tool.BASE.Invalid): tool.census(fixture(), policy, "coordinator")

    def test_unnamed_delivery_lane_refused(self):
        for collector in ("", "-", "unknown", "later", " coordinator "):
            with self.subTest(collector=collector):
                with self.assertRaises(tool.BASE.Invalid): tool.census(fixture(), POLICY, collector)


if __name__ == "__main__":
    unittest.main()
