"""Identity controls for the exact census; these are external tooling tests."""
import importlib.util
from pathlib import Path
import sys
import unittest
sys.dont_write_bytecode = True
SCRIPT = Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus/reconcile.py"
spec = importlib.util.spec_from_file_location("reconcile", SCRIPT)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def source(name="M.t", private=False, mod="M"):
    return {"file": mod.replace(".", "/") + ".lean", "source_name": name,
            "private": private, "id": mod + ":" + name + ":" + str(private)}


def theorem(name="M.t", user=None, private=False, mod="M"):
    return {"module": mod, "name": name, "user_name": user or name,
            "is_private": private, "type_expression": "exact dependent type",
            "joint_witness": "pending"}


class ReconciliationControls(unittest.TestCase):
    def test_unwitnessed_public_retains_exact_identity(self):
        row = theorem()
        kernel = {("M", "M.t"): row}
        found = module.reconcile_sources([source()], kernel)
        self.assertEqual(kernel[found[source()["id"]]]["type_expression"], "exact dependent type")
        self.assertEqual(row["joint_witness"], "pending")

    def test_private_matches_once_without_extra_generated_row(self):
        row = theorem("_private.M.0.M.t", "M.t", True)
        kernel = {("M", row["name"]): row}
        found = module.reconcile_sources([source(private=True)], kernel)
        self.assertEqual(set(kernel) - set(found.values()), set())

    def test_privacy_distinguishes_same_canonical_name(self):
        public = theorem()
        private = theorem("_private.M.0.M.t", "M.t", True)
        kernel = {("M", row["name"]): row for row in [public, private]}
        rows = [source(), source(private=True)]
        found = module.reconcile_sources(rows, kernel)
        self.assertNotEqual(found[rows[0]["id"]], found[rows[1]["id"]])

    def test_ambiguous_private_name_is_rejected(self):
        rows = [theorem("_private.M.0.M.t", "M.t", True),
                theorem("_private.M.1.M.t", "M.t", True)]
        with self.assertRaises(RuntimeError):
            module.reconcile_sources([source(private=True)], {("M", r["name"]): r for r in rows})

    def test_same_name_in_distinct_modules_is_not_collapsed(self):
        rows = [source(), source(mod="N")]
        kernel = {(mod, "M.t"): theorem(mod=mod) for mod in ["M", "N"]}
        self.assertEqual(len(set(module.reconcile_sources(rows, kernel).values())), 2)

    def test_missing_export_remains_pending(self):
        self.assertEqual(module.reconcile_sources([source()], {}), {})

    def test_duplicate_source_identity_is_rejected(self):
        with self.assertRaises(RuntimeError):
            module.reconcile_sources([source(), source()], {})

class VerificationRequestControls(unittest.TestCase):
    def test_private_and_two_formats_preserve_order(self):
        text="#verify_private_joint M N.t with p\n#verify_joint_dag A.t with d\n#verify_joint B.t with b\n"
        self.assertEqual(module.verification_requests(text),[
            ("_private.M.0.N.t","p","repr-v1"),("A.t","d","expr-dag-v1"),("B.t","b","repr-v1")])

    def test_malformed_verification_fails_closed(self):
        with self.assertRaises(RuntimeError):
            module.verification_requests("#verify_joint_dag missing")

    def test_comments_do_not_add_requests(self):
        self.assertEqual(module.verification_requests("-- #verify_joint M.t with p"),[])


if __name__ == "__main__":
    unittest.main()
