import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SCRIPT = ROOT / "scripts/h62/item1/duplication-scanner/scan.py"
spec = importlib.util.spec_from_file_location("h62_scanner", SCRIPT)
scanner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scanner)

class ScannerControls(unittest.TestCase):
    def test_binder_scope_and_intrinsic_types(self):
        self.assertEqual(scanner.normalize("(x : Nat) : x = x"), scanner.normalize("(y : Nat) : y = y"))
        self.assertNotEqual(scanner.normalize("(x : Nat) : x = x"), scanner.normalize("(x : Int) : x = x"))
        self.assertNotEqual(scanner.normalize("(x : y) (y : Nat) : x = x"),
                            scanner.normalize("(x : z) (z : Nat) : x = x"))
        self.assertEqual(scanner.normalize("{x : Nat} : x = x"), scanner.normalize("{y : Nat} : y = y"))
        self.assertEqual(scanner.normalize("[x : Nat] : x = x"), scanner.normalize("[y : Nat] : y = y"))
        self.assertNotEqual(scanner.normalize("{x : Nat} : x = x"), scanner.normalize("(x : Nat) : x = x"))
        self.assertEqual(scanner.normalize("(α : Type) : α = α"), scanner.normalize("(β : Type) : β = β"))
        self.assertEqual(scanner.normalize("(α : Type) : α→α"), scanner.normalize("(β : Type) : β→β"))
        self.assertIsNone(scanner.normalize("{x : Nat) : x = x"))
        self.assertIsNone(scanner.normalize("(_ : Nat) : True"))
        self.assertIsNone(scanner.normalize("{_ : Nat} : _ = _"))
        self.assertIsNone(scanner.normalize("(x : Nat) (p : ∀ x, x = x) : True"))
        self.assertIsNone(scanner.normalize("(x : Nat) (p : fun x => x) : True"))
        self.assertIsNone(scanner.normalize("(x : Nat) : «x» = x"))
        self.assertIsNone(scanner.normalize("(x : Nat) : ∀ x, x = x"))
        self.assertIsNone(scanner.normalize("(x : Nat) : .x = x"))
        self.assertIsNone(scanner.normalize("(x : Nat) (y : .x) : y = y"))
        self.assertNotEqual(scanner.normalize("(x : Nat) : x' = x"),
                            scanner.normalize("(y : Nat) : y' = y"))

    def test_definition_delimiter_scope(self):
        split = scanner.split_definition('(x : String := ":=") : String := x')
        self.assertEqual(split, ('(x : String := ":=") : String ', ' x'))
        self.assertIsNone(scanner.split_definition('(x : Nat := 3)'))

    def test_nested_comments_and_strings(self):
        text = 'a /- one /- two -/ three -/ "not -- a comment" -- gone\nb'
        masked = scanner.mask(text)
        self.assertIn('"not -- a comment"', masked)
        self.assertNotIn("three", masked)
        self.assertEqual(text.count("\n"), masked.count("\n"))
        with self.assertRaises(ValueError): scanner.mask("/- missing")
        fake = 'def a : String := "first\ntheorem fake : True := by trivial\nlast"'
        self.assertEqual(len(list(scanner.DECL.finditer(scanner.hide_strings(scanner.mask(fake))))), 1)
        self.assertEqual(len(list(scanner.DECL.finditer("  example (x : Nat) : x = x := by rfl"))), 1)
        self.assertEqual(len(list(scanner.DECL.finditer("definition := 1"))), 0)
        self.assertEqual(len(list(scanner.DECL.finditer("local theorem x : True := by trivial"))), 1)
        self.assertEqual(len(list(scanner.DECL.finditer("inductive X where"))), 1)

    def test_structure_defaults_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "A.lean"
            source.write_text("structure S where\n  x : Nat := 0\n")
            rows = scanner.scan(source, root)
            self.assertEqual(rows[0]["reject_reason"], "unsupported-declaration-form")
            self.assertIsNone(rows[0]["statement"])

    def test_string_does_not_end_body(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "A.lean"
            source.write_text('def a : String := "first\nend\nlast"\n')
            rows = scanner.scan(source, root)
            self.assertEqual(rows[0]["body"], ['"first\nend\nlast"'])

    def test_fixture_body_copy_with_different_signatures(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("def natFixture : Nat := 0\ndef intFixture : Int := 0\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual(data["candidates"], [])
            self.assertEqual(len(data["body_candidates"]), 1)
            self.assertIn("different-or-unsupported-statements", data["body_candidates"][0]["reject_reasons"])

    def test_namespace_context_is_not_conflated(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("namespace A\ntheorem a (x : T) : x = x := by rfl\nend A\n")
            (root / "B.lean").write_text("namespace B\ntheorem b (x : T) : x = x := by rfl\nend B\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual(data["candidates"], [])
            self.assertEqual(len(data["body_candidates"]), 1)
            self.assertIn("different-or-unsupported-statements", data["body_candidates"][0]["reject_reasons"])

    def test_report_and_incremental(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("theorem a (x : Nat) : x = x := by rfl\n")
            (root / "Solidity").mkdir()
            (root / "Solidity" / "C.lean").write_text("theorem c (z : Nat) : z = z := by rfl\n")
            (root / "B.lean").write_text("theorem b (y : Nat) : y = y := by rfl\n")
            owner = root / "owners.json"
            owner.write_text(json.dumps({"A.lean": "lane-a"}))
            registry = root / "registry.json"
            registry.write_text(json.dumps({"items": [{"id": "G1", "owner": "lane-a", "status": "in-progress", "evidence": {"files": ["Solidity/C.lean", "Solidity/"]}}]}))
            cmd = [sys.executable, "-B", str(SCRIPT), str(root), "**/*.lean", "--owners", str(owner), "--registry", str(registry)]
            first = subprocess.check_output(cmd)
            self.assertEqual(first, subprocess.check_output(cmd))
            missing = subprocess.run([sys.executable, "-B", str(SCRIPT), str(root), "missing/*.lean"], capture_output=True)
            self.assertNotEqual(missing.returncode, 0)
            self.assertEqual(json.loads(missing.stdout)["unmatched_patterns"], ["missing/*.lean"])
            data = json.loads(first)
            self.assertEqual(len(data["candidates"]), 1)
            self.assertIn("intrinsic-signature-unresolved", data["body_candidates"][0]["reject_reasons"])
            self.assertIn("ownership-requires-live-verification", data["body_candidates"][0]["reject_reasons"])
            self.assertEqual(len(data["inventory"]), data["declarations"])
            self.assertEqual([x["owner"] for x in data["candidates"][0]["members"]], ["lane-a", "unknown", "unknown"])
            self.assertEqual({r["pattern"] for r in data["candidates"][0]["members"][2]["registry_references"]}, {"Solidity/", "Solidity/C.lean"})
            previous = root / "previous.json"
            previous.write_bytes(first)
            owner.write_text(json.dumps({"A.lean": "lane-b"}))
            changed_owner = json.loads(subprocess.check_output(cmd + ["--previous", str(previous)]))
            self.assertTrue(changed_owner["incremental"]["owner_config_changed"])
            registry.write_text(json.dumps({"items": []}))
            changed_registry = json.loads(subprocess.check_output(cmd + ["--previous", str(previous)]))
            self.assertTrue(changed_registry["incremental"]["registry_changed"])
            (root / "A.lean").unlink()
            (root / "B.lean").write_text("theorem b : True := by trivial\n")
            data = json.loads(subprocess.check_output(cmd + ["--previous", str(previous)]))
            self.assertEqual(data["incremental"]["removed"], ["A.lean"])
            self.assertEqual(data["incremental"]["changed"], ["B.lean"])

if __name__ == "__main__":
    unittest.main()
