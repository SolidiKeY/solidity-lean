import contextlib
import importlib.util
import io
import json
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
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
        self.assertIsNone(scanner.normalize("(x : Nat) (p : ∃ x, x = x) : True"))
        self.assertIsNone(scanner.normalize("(x : Nat) (p : fun x => x) : True"))
        self.assertIsNone(scanner.normalize("(x : Nat) : «x» = x"))
        self.assertIsNone(scanner.normalize("(x : Nat) : ∀ x, x = x"))
        self.assertIsNone(scanner.normalize("(x : Nat) : ∃ x, x = x"))
        self.assertIsNone(scanner.normalize("(x : Nat) : match n with | x => x"))
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
        self.assertEqual(len(list(scanner.DECL.finditer("partial def f : Nat := 1"))), 1)
        self.assertEqual(len(list(scanner.DECL.finditer("unsafe def f : Nat := 1"))), 1)
        self.assertEqual(len(list(scanner.DECL.finditer("partial syntax foo"))), 0)

    def test_where_and_equation_forms_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "A.lean"
            source.write_text('partial def e : Nat → Nat\n  | 0 => 0\n  | n+1 => n\ndef w : T where\n  source := id\ndef s : String := "where"\n')
            rows = scanner.scan(source, root)
            self.assertEqual(len(rows), 3)
            self.assertIsNone(rows[0]["reject_reason"])
            self.assertEqual(rows[0]["body_form"], "equations")
            self.assertEqual(rows[0]["qualifiers"], ["partial"])
            self.assertEqual(rows[1]["reject_reason"], "unsupported-where-declaration")
            self.assertIsNone(rows[2]["reject_reason"])
            report = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual(report["rejections"]["by_reason"],
                             {"unsupported-where-declaration": 1})

    def test_equation_bodies_and_local_helpers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text(
                "def a : Nat → Nat\n  | 0 => 0\n  | n => let q := n; q\n"
                "def b : Nat → Nat\n  | 0 => 0\n  | n => let q := n; q\n"
                "def c : Nat → Nat\n  | 0 => 1\n  | n => let q := n; q\n"
                "def d : Int → Nat\n  | 0 => 0\n  | n => let q := n; q\n"
                "def noType\n  | 0 => 0\n"
                "def outerA : Nat := helper where\n  def helper : Nat := 1\n"
                "def outerB : Nat := helper where\n  def helper : Nat := 2\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            inventory = data["inventory"]
            rows = {row["name"]: row for row in inventory}
            self.assertEqual(rows["a"]["body_form"], "equations")
            self.assertIsNone(rows["a"]["reject_reason"])
            self.assertEqual(rows["noType"]["reject_reason"], "missing-top-level-definition")
            self.assertIsNotNone(rows["outerA"]["body_reject_reason"])
            self.assertIsNotNone(rows["outerB"]["body_reject_reason"])
            body_groups = [{r["name"] for r in group["members"]} for group in data["body_candidates"]]
            self.assertIn({"a", "b", "d"}, body_groups)
            matching = next(group for group in data["body_candidates"] if {r["name"] for r in group["members"]} == {"a", "b", "d"})
            self.assertIn("different-or-unsupported-statements", matching["reject_reasons"])
            self.assertFalse(any("outerA" in group or "outerB" in group for group in body_groups))
            self.assertFalse(any("c" in group for group in body_groups))

    def test_indentation_excludes_modifiers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "A.lean"
            source.write_text("def a : Nat := 0\nprivate def b : Nat := 0\n")
            rows = scanner.scan(source, root)
            self.assertIsNone(rows[0]["body_reject_reason"])
            source.write_text("private def a : Nat := 0\n  def b : Nat := 0\n")
            rows = scanner.scan(source, root)
            self.assertEqual(rows[0]["body_reject_reason"], "nested-declaration-boundary")

    def test_equation_delimiters_fail_closed(self):
        self.assertIsNone(scanner.split_declaration(" : Nat → Nat\n  | 0\n    => 0"))
        self.assertIsNone(scanner.split_declaration(" : (Nat | Nat)\n  | 0"))
        self.assertIsNone(scanner.split_declaration(" (x : Nat)\n  | 0 => 0"))
        self.assertIsNone(scanner.split_declaration(scanner.mask(" : Nat /- | 0 => 0 -/")))
        assignment = scanner.split_declaration(' : String := " | x => y "')
        self.assertEqual(assignment[2], "assignment")
        assignment = scanner.split_declaration(" : Nat := by\n  match 0 with\n  | 0 => 1")
        self.assertEqual(assignment[2], "assignment")

    def test_escaped_identifiers_do_not_conflate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text(
                "def «a:=b» : Nat := 1\n"
                "def x : Nat := «a b»\n"
                "def y : Nat := «a  b»\n"
                "def z : Nat := «a--b»\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual(len(data["inventory"]), 4)
            self.assertEqual(data["inventory"][0]["reject_reason"], "unsupported-binder-syntax")
            self.assertEqual(data["inventory"][0]["body_reject_reason"], "escaped-identifier-boundary")
            self.assertEqual(data["body_candidates"], [])
            self.assertNotEqual(scanner.tokenize("«a b»"), scanner.tokenize("«a  b»"))
            self.assertIn("«a--b»", scanner.mask("«a--b»"))

    def test_character_literals_do_not_confuse_identifier_or_string_masks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("""def a : Char := '«'\ndef b : Char := '»'\ndef c : Char := '"'\ndef d' : Nat := 1\n""")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual(len(data["inventory"]), 4)
            self.assertEqual(data["errors"], [])
            self.assertEqual(data["body_candidates"], [])
            self.assertNotEqual(scanner.tokenize("'«'"), scanner.tokenize("'»'"))

    def test_escaped_character_literal_boundaries(self):
        for literal in (r"'\''", r"'\\'", r"'\n'", r"'\u{00ab}'"):
            with self.subTest(literal=literal):
                source = "def x : Char := " + literal + "\ndef y : Nat := 0\n"
                self.assertEqual(scanner.mask(source), source)
                self.assertEqual(len(scanner.hide_strings(source)), len(source))
                self.assertEqual(scanner.tokenize(literal), [literal])
        self.assertEqual(scanner.tokenize("f' x"), ["f'", "x"])

    def test_raw_strings_preserve_delimiters_and_content(self):
        raw = 'r#"one " -- «not an identifier»\ndef fake : Nat := 0\ntwo"#'
        source = 'def a : String := ' + raw + '\ndef b : String := r#"one  two"#\n'
        self.assertEqual(scanner.mask(source), source)
        self.assertEqual(len(list(scanner.DECL.finditer(scanner.hide_strings(source)))), 2)
        self.assertEqual(scanner.tokenize(raw), [raw])
        self.assertNotEqual(scanner.tokenize('r#"one two"#'), scanner.tokenize('r#"one  two"#'))
        self.assertEqual(scanner.tokenize('r##"a "# b"##'), ['r##"a "# b"##'])
        with self.assertRaises(ValueError): scanner.mask('def x := r#"unterminated"')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            literal = 'r##"a "# -- fake comment\ndef fake : Nat := 0\nend"##'
            (root / "A.lean").write_text("def a : String := " + literal + "\ndef b : String := " + literal + "\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual([row["name"] for row in data["inventory"]], ["a", "b"])
            self.assertEqual(len(data["body_candidates"]), 1)

    def test_full_skeleton_slice_alignment(self):
        source = (
            "def «a:=b» : Nat := 1\n"
            "def x : Char := '«'\n"
            "def text : String := r##\"quote \"# -- literal\ndef fake : Nat := 1\nend\"##\n"
            "def f : Nat → Nat\n  | 0 => 1\n  | n => let q := n; q\n"
            "def g : Nat := 1 -- comment «not a quote»\n")
        text = scanner.mask(source)
        skeleton = scanner.hide_strings(text)
        matches = list(scanner.DECL.finditer(skeleton))
        self.assertEqual(len(matches), 5)
        for i, match in enumerate(matches):
            end = matches[i+1].start() if i+1 < len(matches) else len(text)
            self.assertEqual(skeleton[match.end():end], scanner.hide_strings(text[match.end():end]))

    def test_indented_command_does_not_group_truncated_bodies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text(
                "theorem a : True := by\n  open Foo in\n  exact 1\n"
                "theorem b : True := by\n  open Bar in\n  exact 2\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            rows = {row["name"]: row for row in data["inventory"]}
            self.assertEqual(rows["a"]["body_reject_reason"], "indented-command-boundary")
            self.assertEqual(rows["b"]["body_reject_reason"], "indented-command-boundary")
            self.assertEqual(data["body_candidates"], [])

    def test_structure_defaults_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "A.lean"
            source.write_text("structure S where\n  x : Nat := 0\n")
            rows = scanner.scan(source, root)
            self.assertEqual(rows[0]["reject_reason"], "unsupported-declaration-form")
            self.assertIsNone(rows[0]["statement"])
            report = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual(report["rejections"]["by_reason"], {"unsupported-declaration-form": 1})

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

    def test_body_copy_with_different_qualifiers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("partial def a : Nat := 0\ndef b : Nat := 0\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual(data["candidates"], [])
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

    def test_input_read_failure_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "A.lean"
            source.write_text("def a : Nat := 0\n")
            original = Path.read_bytes
            def checked_read(path):
                if path == source: raise OSError("simulated read failure")
                return original(path)
            output = io.StringIO()
            with mock.patch.object(Path, "read_bytes", checked_read), mock.patch.object(sys, "argv", [str(SCRIPT), str(root), "*.lean"]), contextlib.redirect_stdout(output):
                result = scanner.main()
            data = json.loads(output.getvalue())
            self.assertTrue(result)
            self.assertEqual(len(data["errors"]), 1)
            self.assertIn("simulated read failure", data["errors"][0]["reason"])
            self.assertEqual(data["incremental"]["comparison_status"], "current-incomplete")
            self.assertIsNone(data["incremental"]["added"])

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
            stable = json.loads(subprocess.check_output(cmd + ["--previous", str(previous)]))
            self.assertEqual(stable["incremental"]["candidate_groups"]["statements"]["changed"], [])
            mismatch = subprocess.run([sys.executable, "-B", str(SCRIPT), str(root), "*.lean", "--previous", str(previous)], capture_output=True)
            self.assertNotEqual(mismatch.returncode, 0)
            self.assertIn(b"incompatible version or selection", mismatch.stderr)
            corrupt = json.loads(first)
            corrupt["inputs"].append(corrupt["inputs"][0])
            bad = root / "bad.json"
            bad.write_text(json.dumps(corrupt))
            self.assertNotEqual(subprocess.run(cmd + ["--previous", str(bad)], capture_output=True).returncode, 0)
            owner.write_text(json.dumps({"A.lean": "lane-b"}))
            changed_owner = json.loads(subprocess.check_output(cmd + ["--previous", str(previous)]))
            self.assertTrue(changed_owner["incremental"]["owner_config_changed"])
            self.assertEqual(len(changed_owner["incremental"]["candidate_groups"]["statements"]["changed"]), 1)
            self.assertEqual(len(changed_owner["incremental"]["candidate_groups"]["bodies"]["changed"]), 1)
            corrupt["inputs"].pop()
            corrupt["errors"] = [{"path": "A.lean", "reason": "unreadable"}]
            bad.write_text(json.dumps(corrupt))
            bad_result = subprocess.run(cmd + ["--previous", str(bad)], capture_output=True)
            self.assertNotEqual(bad_result.returncode, 0)
            self.assertIn(b"previous report is incomplete", bad_result.stderr)
            corrupt["errors"] = []
            corrupt["unmatched_patterns"] = ["missing/*.lean"]
            bad.write_text(json.dumps(corrupt))
            bad_result = subprocess.run(cmd + ["--previous", str(bad)], capture_output=True)
            self.assertNotEqual(bad_result.returncode, 0)
            self.assertIn(b"previous report is incomplete", bad_result.stderr)
            (root / "B.lean").write_text("/- unterminated")
            incomplete = subprocess.run(cmd + ["--previous", str(previous)], capture_output=True)
            self.assertNotEqual(incomplete.returncode, 0)
            self.assertEqual(json.loads(incomplete.stdout)["incremental"]["comparison_status"], "current-incomplete")
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["candidate_groups"])
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["removed"])
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["added"])
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["changed"])
            (root / "B.lean").write_text("theorem b (y : Nat) : y = y := by rfl\n")
            registry.write_text(json.dumps({"items": []}))
            changed_registry = json.loads(subprocess.check_output(cmd + ["--previous", str(previous)]))
            self.assertTrue(changed_registry["incremental"]["registry_changed"])
            (root / "A.lean").unlink()
            (root / "B.lean").write_text("theorem b : True := by trivial\n")
            (root / "D.lean").write_text("def d : Int := 0\ndef e : Int := 0\n")
            data = json.loads(subprocess.check_output(cmd + ["--previous", str(previous)]))
            self.assertEqual(data["incremental"]["removed"], ["A.lean"])
            self.assertEqual(data["incremental"]["changed"], ["B.lean"])
            self.assertTrue(data["incremental"]["candidate_groups"]["statements"]["removed"])
            self.assertTrue(data["incremental"]["candidate_groups"]["statements"]["added"])
            self.assertTrue(data["incremental"]["candidate_groups"]["bodies"]["removed"])
            self.assertTrue(data["incremental"]["candidate_groups"]["bodies"]["added"])

if __name__ == "__main__":
    unittest.main()
