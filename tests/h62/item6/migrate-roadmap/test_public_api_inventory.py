"""No Lean execution; controls for silent inventory/visibility/type weakening."""
import importlib.util
from pathlib import Path
import sys
import unittest
sys.dont_write_bytecode = True
P = Path(__file__).resolve().parents[4] / "scripts/h62/item6/migrate-roadmap/public_api_inventory.py"
s = importlib.util.spec_from_file_location("inventory", P)
m = importlib.util.module_from_spec(s); s.loader.exec_module(m)


class Controls(unittest.TestCase):
    def test_duplicate_declaration_refused(self):
        with self.assertRaises(ValueError): m.unique([dict(name="A"), dict(name="A")])

    def test_absent_metadata_does_not_imply_public(self):
        for n in ("A.noConfusion", "_private.A.0.x"):
            self.assertIsNone(m.visibility(n)["public_visibility"])
            self.assertIsNone(m.visibility(n)["protected_status"])
        self.assertTrue(m.visibility("_private.A.0.x")["private_name_encoding"])

    def test_explicit_and_implicit_binders_stay_distinct(self):
        for k in ("explicit", "implicit", "strictImplicit", "instance"):
            self.assertEqual(m.binders(["forall", k, ["const", "Nat", []], ["bvar", 0]])[0]["binder_kind"], k)

    def test_erased_or_unknown_binders_refused(self):
        for k in ("erased", "future_kind"):
            with self.assertRaises(ValueError): m.binders(["forall", k, [], []])

    def test_order_and_dependent_domain_preserved(self):
        e = ["forall", "implicit", ["sort", ["zero"]], ["forall", "explicit", ["bvar", 0], ["bvar", 1]]]
        a = m.binders(e)
        self.assertEqual([r["position"] for r in a], [0, 1])
        self.assertEqual(a[1]["domain"], ["bvar", 0])

    def test_missing_export_is_not_an_invented_signature(self):
        self.assertIsNone(m.signature(None))
        a = m.signature(dict(type_debug="forall {x : Nat}, x = x", universe_parameters=[], is_theorem=True, is_unsafe=False))
        self.assertIsNone(a["ordered_binders"])
        self.assertEqual(a["type_debug"], "forall {x : Nat}, x = x")

    def test_one_alias_cannot_mask_the_other(self):
        expected = ["Solidity.Roadmap.Evm.Fork.toCtorIdx", "Solidity.Roadmap.Evm.Precompile.toCtorIdx"]
        complete = "protected abbrev Fork.toCtorIdx : Fork → Nat := Fork.ctorIdx\nprotected abbrev Precompile.toCtorIdx : Precompile → Nat := Precompile.ctorIdx"
        m.candidate_coverage(complete, expected)
        for line in complete.splitlines():
            with self.assertRaises(ValueError): m.candidate_coverage(line, expected)

    def test_changed_fixture_cannot_inherit_passing_run(self):
        fixture = m.ROOT / "tests/h62/item6/migrate-roadmap/HashContainsFixture.lean"
        key = str(fixture.relative_to(m.ROOT))
        run = dict(exit=0, guard=None, inputs_before={key: "stale"}, inputs_after={key: "stale"})
        with self.assertRaises(ValueError): m.verify_fixture(run, fixture)
        run["inputs_before"] = run["inputs_after"] = {key: m.sha(fixture)}
        m.verify_fixture(run, fixture)

    def test_non_theorem_kind_is_not_guessed(self):
        a = m.signature(dict(type_debug="Nat", universe_parameters=[], is_theorem=False, is_unsafe=False))
        self.assertEqual(a["kind"], "non_theorem_subkind_not_captured")


if __name__ == "__main__": unittest.main()
