import contextlib
import copy
import hashlib
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

def pinned(path):
    return ["--previous", str(path), "--previous-sha256", hashlib.sha256(path.read_bytes()).hexdigest()]

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

    def test_identifier_punctuation_does_not_conflate_binders(self):
        for suffix in ("?", "!", "?foo", "!!"):
            with self.subTest(suffix=suffix):
                left = "(x : Nat) : x" + suffix + " = x"
                right = "(y : Nat) : y" + suffix + " = y"
                self.assertNotEqual(scanner.normalize(left), scanner.normalize(right))
                self.assertEqual(scanner.normalize("(x" + suffix + " : Nat) : x" + suffix + " = x" + suffix),
                                 scanner.normalize("(y" + suffix + " : Nat) : y" + suffix + " = y" + suffix))
        self.assertEqual(scanner.tokenize("x?foo x!! x ? Nat.x? 1?"),
                         ["x?foo", "x!!", "x", "?", "Nat.x?", "1", "?"])
        self.assertIsNone(scanner.raw_literal('x?r#"s"#', 2))
        self.assertIsNone(scanner.char_literal("x?'a'", 2))

    def test_lean_unicode_identifier_continuations(self):
        for suffix in ("℘", "₀", "ₐ", "ᵢ", "𝒜"):
            with self.subTest(suffix=suffix):
                self.assertNotEqual(scanner.normalize("(x : Nat) : x" + suffix + " = x"),
                                    scanner.normalize("(y : Nat) : y" + suffix + " = y"))
                self.assertEqual(scanner.tokenize("x" + suffix), ["x" + suffix])
                self.assertIsNone(scanner.raw_literal('x' + suffix + 'r#"a"#', 2))
                self.assertIsNone(scanner.char_literal("x" + suffix + "'a'", 2))
        self.assertEqual(scanner.normalize("(x℘ : Nat) : x℘ = x℘"),
                         scanner.normalize("(y℘ : Nat) : y℘ = y℘"))

    def test_lean_identifier_operator_boundaries(self):
        for op in ("×", "÷", "λ", "Π", "Σ"):
            with self.subTest(op=op):
                self.assertEqual(scanner.tokenize("x" + op + "y"), ["x", op, "y"])
        for op, literal in (("×", "'«'"), ("÷", "'»'")):
            source = "def x := 2" + op + literal
            self.assertEqual(scanner.mask(source), source)
            self.assertEqual(len(scanner.hide_strings(source)), len(source))

    def test_multiline_and_stacked_attribute_declarations_are_inventoried(self):
        root = Path("/virtual")
        source = ("@[simp,\n  inline] def target : Nat := 1\n"
                  "@[foo [bar],\n  baz]\n@[other] theorem next : True := by trivial\n"
                  "def visible : String := \"@[fake] def hidden\"\n")
        rows = scanner.scan(root / "A.lean", root, source.encode())
        self.assertEqual([(r["name"], r["line"]) for r in rows],
                         [("target", 2), ("next", 5), ("visible", 6)])
        self.assertEqual([r["reject_reason"] for r in rows], [None, None, None])
        with_comment = "@[simp, /- nested [ comment ] -/\n  inline] def x : Nat := 1\n"
        self.assertEqual(scanner.scan(root / "B.lean", root, with_comment.encode())[0]["name"], "x")
        nested = "@[foo [[bar]]] def target : Nat := 1\ndef visible : Nat := 2\n"
        self.assertEqual([r["name"] for r in scanner.scan(root / "C.lean", root, nested.encode())], ["target", "visible"])
        rows = scanner.scan(root / "D.lean", root, b"@[unsafe] def a : Nat := 0\nunsafe def b : Nat := 0\n")
        self.assertEqual(rows[0]["qualifiers"], [])
        self.assertEqual(rows[1]["qualifiers"], ["unsafe"])
        aligned = scanner.scan(root / "F.lean", root, b"@[simp] def first : Nat := 0\n  def inner : Nat := 1\n")
        self.assertEqual(aligned[0]["body_reject_reason"], "nested-declaration-boundary")
        following = ("def a : Nat := 1\n@[foo,\n bar] def b : Nat := 2\n"
                     "def c : Nat := 1\n@[other,\n baz] def d : Nat := 3\n")
        rows = scanner.scan(root / "G.lean", root, following.encode())
        self.assertEqual(rows[0]["body"], rows[2]["body"])
        self.assertEqual(rows[0]["body"], ["1"])
        with self.assertRaisesRegex(ValueError, "unterminated attribute"):
            scanner.scan(root / "E.lean", root, b"@[foo [bar]\ndef hidden := 0\n")

    def test_lean_declaration_modifiers_and_candidate_distinctions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = ("def before : Nat := 0\n"
                      "public theorem first : True := by trivial\n"
                      "meta def second : Nat := 0\n"
                      "nonrec def third : Nat := 0\n"
                      "@[foo,\n bar] public protected meta unsafe nonrec def combined : Nat := 0\n"
                      "private def hidden : Nat := 0\n"
                      "def visible : Nat := 0\n")
            path = root / "A.lean"
            path.write_text(source)
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            rows = {r["name"]: r for r in data["inventory"]}
            self.assertEqual(set(rows), {"before", "first", "second", "third", "combined", "hidden", "visible"})
            self.assertEqual(rows["first"]["qualifiers"], ["public"])
            self.assertEqual(rows["second"]["qualifiers"], ["meta"])
            self.assertEqual(rows["third"]["qualifiers"], ["nonrec"])
            self.assertEqual(rows["combined"]["qualifiers"], ["meta", "nonrec", "protected", "public", "unsafe"])
            self.assertEqual(rows["combined"]["line"], 6)
            body = next(g for g in data["body_candidates"] if {"second", "third", "hidden", "visible"}.issubset({m["name"] for m in g["members"]}))
            self.assertIn("different-or-unsupported-statements", body["reject_reasons"])
            self.assertIn("intrinsic-signature-unresolved", body["reject_reasons"])
            self.assertFalse(any({"second", "third"}.issubset({m["name"] for m in g["members"]}) for g in data["candidates"]))
            parsed = scanner.scan(path, root)
            self.assertEqual(parsed[0]["body"], ["0"])
            split = ("def before : Nat := 0\npublic\n  def one : Nat := 0\n"
                     "@[foo]\nprivate\n  nonrec\n  def two : Nat := 0\n")
            split_rows = scanner.scan(path, root, split.encode())
            self.assertEqual([r["name"] for r in split_rows], ["before", "one", "two"])
            self.assertEqual(split_rows[1]["qualifiers"], ["public"])
            self.assertEqual(split_rows[2]["qualifiers"], ["nonrec", "private"])
            self.assertEqual(split_rows[1]["line"], 3)
            self.assertEqual(split_rows[2]["line"], 7)
            self.assertEqual(split_rows[0]["body"], ["0"])

    def test_compound_class_declarations_keep_their_names_and_refusals(self):
        root = Path("/virtual")
        source = ("def before : Nat := 0\n"
                  "class inductive Foo where\n  | mk : Foo\n"
                  "@[foo] public class\n  abbrev Bar := Nat\n"
                  "class Ordinary where\n  field : Nat\n"
                  "def after : Nat := 1\n")
        rows = scanner.scan(root / "A.lean", root, source.encode())
        self.assertEqual([(r["kind"], r["name"]) for r in rows],
                         [("def", "before"), ("class inductive", "Foo"),
                          ("class abbrev", "Bar"), ("class", "Ordinary"), ("def", "after")])
        self.assertEqual(rows[0]["body"], ["0"])
        self.assertEqual(rows[-1]["body"], ["1"])
        self.assertEqual(rows[2]["qualifiers"], ["public"])
        for row in rows[1:4]:
            self.assertEqual(row["reject_reason"], "unsupported-declaration-form")
            self.assertIsNone(row["statement"])
            self.assertEqual(row["body"], [])

    def test_explicit_universe_suffix_does_not_change_declaration_name(self):
        root = Path("/virtual")
        source = ("def before : Nat := 0\n"
                  "@[simp] public def Foo.{u} : Type u := Nat\n"
                  "def N.Bar.{u,v} : Type u := Nat\n"
                  "def after : Nat := 1\n")
        rows = scanner.scan(root / "A.lean", root, source.encode())
        self.assertEqual([r["name"] for r in rows], ["before", "Foo", "N.Bar", "after"])
        self.assertEqual(rows[0]["body"], ["0"])
        self.assertEqual(rows[-1]["body"], ["1"])
        self.assertEqual(rows[1]["qualifiers"], ["public"])
        for row in rows[1:3]:
            self.assertEqual(row["reject_reason"], "unsupported-binder-syntax")
            self.assertIsNone(row["statement"])
        multiline = scanner.scan(root / "B.lean", root, b"def Multi.{\n u, v\n} : Type u := Nat\n")
        self.assertEqual(multiline[0]["name"], "Multi")
        self.assertIsNone(multiline[0]["statement"])
        malformed = scanner.scan(root / "C.lean", root, b"def Broken.{u : Type := Nat\n")
        self.assertEqual(malformed[0]["name"], "Broken")
        self.assertIsNone(malformed[0]["statement"])
        self.assertIsNotNone(malformed[0]["reject_reason"])

    def test_escaped_declaration_names_are_lexical_spellings_only(self):
        root = Path("/virtual")
        source = ('def before : Nat := 0\n@[simp] public def «a.b» : Nat := 1\n'
                  'def a.b : Nat := 1\ndef N.«b c» : Nat := 1\n'
                  'def «a--b».part.{u} : Type u := Nat\n'
                  'theorem «return» : True := by trivial\n'
                  'example : True := by trivial\ndef after : Nat := 2\n')
        rows = scanner.scan(root / "A.lean", root, source.encode())
        self.assertEqual([r["name"] for r in rows],
                         ["before", "«a.b»", "a.b", "N.«b c»", "«a--b».part", "«return»", "<anonymous>", "after"])
        self.assertEqual(rows[0]["body"], ["0"])
        self.assertEqual(rows[-1]["body"], ["2"])
        for index in (1, 3, 4, 5):
            self.assertEqual(rows[index]["reject_reason"], "unsupported-binder-syntax")
            self.assertEqual(rows[index]["body_reject_reason"], "escaped-identifier-boundary")
            self.assertIsNone(rows[index]["statement"])
        self.assertNotEqual(rows[1]["name"], rows[2]["name"])
        with self.assertRaises(ValueError):
            scanner.scan(root / "B.lean", root, 'def «unclosed : Nat := 0\n'.encode())
        unusual = ('def N.«a\nb» : Nat := 0\ndef N.«» : Nat := 0\n'
                   'def «» : Nat := 0\ndef visible : Nat := 1\n')
        unusual_rows = scanner.scan(root / "C.lean", root, unusual.encode())
        self.assertEqual([r["name"] for r in unusual_rows], ["N.«a\nb»", "N.«»", "«»", "visible"])
        for row in unusual_rows[:3]:
            self.assertEqual(row["reject_reason"], "unsupported-binder-syntax")
            self.assertEqual(row["body_reject_reason"], "escaped-identifier-boundary")

    def test_named_and_anonymous_priority_instances_are_accounted(self):
        root = Path("/virtual")
        source = ("def before : Nat := 0\n"
                  "instance (priority := 17) global17 : Marker Nat := foo\n"
                  "private instance (priority := low) hidden : Marker Bool := foo\n"
                  "scoped instance (priority := 41) scoped41 : Marker Int := foo\n"
                  "instance (priority := 100) : Marker String := foo\n"
                  "@[simp] instance (priority := (10)) «a.b» : Marker UInt64 := foo\n"
                  "def after : Nat := 1\n")
        rows = scanner.scan(root / "A.lean", root, source.encode())
        self.assertEqual([r["name"] for r in rows], ["before", "global17", "hidden", "scoped41", "<anonymous>", "«a.b»", "after"])
        self.assertEqual(rows[2]["qualifiers"], ["private"])
        self.assertEqual(rows[3]["qualifiers"], ["scoped"])
        self.assertEqual(rows[0]["body"], ["0"])
        self.assertEqual(rows[-1]["body"], ["1"])
        for row in rows[1:6]:
            self.assertEqual(row["reject_reason"], "unsupported-instance-priority")
            self.assertEqual(row["body_reject_reason"], "unsupported-instance-priority")
            self.assertIsNone(row["statement"])
        with self.assertRaisesRegex(ValueError, "unterminated instance priority"):
            scanner.scan(root / "B.lean", root, b"instance (priority := 10\ndef after : Nat := 1\n")
        split = ("instance (priority :=\n  17)\n  named : Marker Nat := foo\n"
                 "instance (priority := 42) : Marker Bool := foo\ndef next : Nat := 1\n")
        split_rows = scanner.scan(root / "C.lean", root, split.encode())
        self.assertEqual([r["name"] for r in split_rows], ["named", "<anonymous>", "next"])
        self.assertEqual(split_rows[0]["reject_reason"], "unsupported-instance-priority")
        fixture = ROOT / "tests/h62/item6/migrate-yul/DeclarationMetadataFixture.lean"
        fixture_rows = scanner.scan(fixture, ROOT)
        names = {r["name"]: r for r in fixture_rows}
        for name in ("global17", "global63", "private11", "scoped41", "local97"):
            self.assertEqual(names[name]["reject_reason"], "unsupported-instance-priority")
            self.assertEqual(names[name]["body_reject_reason"], "unsupported-instance-priority")

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

    def test_multiline_context_and_literal_boundaries(self):
        root = Path("/virtual")
        def row(source):
            return scanner.scan(root / "A.lean", root, source.encode())[0]
        prefix = "namespace N\nvariable\n  (T : "
        suffix = ")\ntheorem same (x : T) : x = x := by rfl\nend N\n"
        a, b = row(prefix + "Type" + suffix), row(prefix + "Type 1" + suffix)
        self.assertEqual(a["statement"], b["statement"])
        self.assertNotEqual(a["context_hash"], b["context_hash"])
        self.assertEqual(a["context_hash"], row(prefix + "Type" + suffix)["context_hash"])
        open_a = 'open scoped\n  A\nvariable (T : Type)\ntheorem same (x : T) : x = x := by rfl\n'
        open_b = open_a.replace("  A\n", "  B\n")
        self.assertNotEqual(row(open_a)["context_hash"], row(open_b)["context_hash"])
        literal_a = 'variable (s : String := "x\nnamespace Fake\ny")\ntheorem same : True := by trivial\n'
        literal_b = literal_a.replace('namespace Fake', 'namespace Other')
        self.assertNotEqual(row(literal_a)["context_hash"], row(literal_b)["context_hash"])
        comment = '/- variable\nnamespace Fake -/\n'
        self.assertEqual(row(comment + prefix + "Type" + suffix)["context_hash"], a["context_hash"])

    def test_notation_after_declaration_contributes_to_context(self):
        root = Path("/virtual")
        template = ('namespace N\ndef marker : Nat := 0\n'
                    'local notation \"MyT\" => {typ}\n'
                    'theorem same ({binder} : MyT) : {binder} = {binder} := by rfl\nend N\n')
        def theorem(typ, binder):
            source = template.format(typ=typ, binder=binder).encode()
            return scanner.scan(root / "A.lean", root, source)[1]
        nat, integer, renamed = theorem("Nat", "x"), theorem("Int", "x"), theorem("Nat", "y")
        self.assertEqual(nat["statement"], integer["statement"])
        self.assertNotEqual(nat["context_hash"], integer["context_hash"])
        self.assertEqual(nat["context_hash"], renamed["context_hash"])
        self.assertEqual(nat["statement"], renamed["statement"])
        full = scanner.scan(root / "A.lean", root, template.format(typ="Nat", binder="x").encode())
        self.assertEqual(full[0]["body"], ["0"])
        indented = ('def outer : Nat := by\n  local notation \"x\" => Nat\n'
                    '  exact 0\ndef next : Nat := 1\n')
        rows = scanner.scan(root / "C.lean", root, indented.encode())
        self.assertEqual(rows[0]["body_reject_reason"], "indented-command-boundary")
        for keyword in ("notation", "infixl", "infixr", "infix", "prefix", "postfix"):
            source = f'def marker : Nat := 0\nscoped {keyword}:50 \"##\" => Nat\ntheorem same : True := by trivial\n'
            changed = source.replace('=> Nat', '=> Int')
            a = scanner.scan(root / "A.lean", root, source.encode())[1]
            b = scanner.scan(root / "B.lean", root, changed.encode())[1]
            self.assertNotEqual(a["context_hash"], b["context_hash"], keyword)

    def test_set_option_context_and_body_boundaries(self):
        root = Path("/virtual")
        template = ("def marker : Nat := 0\nset_option autoImplicit {value}\n"
                    "theorem same (x : Nat) : x = x := by rfl\n")
        def rows(value):
            return scanner.scan(root / "A.lean", root, template.format(value=value).encode())
        a, b = rows("true"), rows("false")
        self.assertEqual(a[0]["body"], ["0"])
        self.assertNotEqual(a[1]["context_hash"], b[1]["context_hash"])
        scoped = b"set_option autoImplicit false in\ntheorem next : True := by trivial\n"
        self.assertEqual(scanner.scan(root / "B.lean", root, scoped)[0]["name"], "next")
        nested = b"def outer : Nat := by\n  set_option autoImplicit false in\n  exact 0\ndef next : Nat := 1\n"
        self.assertEqual(scanner.scan(root / "C.lean", root, nested)[0]["body_reject_reason"], "indented-command-boundary")
        with self.assertRaisesRegex(ValueError, "unsupported same-line scoped set_option declaration"):
            scanner.scan(root / "D.lean", root, b"set_option autoImplicit false in theorem hidden : True := by trivial\n")
        multiline = b"set_option autoImplicit\n  false in theorem hidden : True := by trivial\ndef visible : Nat := 0\n"
        with self.assertRaisesRegex(ValueError, "unsupported same-line scoped set_option declaration"):
            scanner.scan(root / "F.lean", root, multiline)
        modified = b"set_option autoImplicit\n  false in @[foo [bar]] public theorem hidden : True := by trivial\n"
        with self.assertRaisesRegex(ValueError, "unsupported same-line scoped set_option declaration"):
            scanner.scan(root / "H.lean", root, modified)
        split_modifier = b"set_option autoImplicit false in public\n  theorem hidden : True := by trivial\n"
        with self.assertRaisesRegex(ValueError, "unsupported same-line scoped set_option declaration"):
            scanner.scan(root / "J.lean", root, split_modifier)
        split_attribute = b"set_option autoImplicit false in @[foo]\n  private def hidden : Nat := 0\n"
        with self.assertRaisesRegex(ValueError, "unsupported same-line scoped set_option declaration"):
            scanner.scan(root / "K.lean", root, split_attribute)
        other = b"set_option autoImplicit false\n#guard_msgs in #eval 1\ndef next : Nat := 0\n"
        self.assertEqual(scanner.scan(root / "I.lean", root, other)[0]["name"], "next")
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            (temp / "A.lean").write_bytes(multiline)
            (temp / "B.lean").write_text("def visible : Nat := 0\n")
            report = subprocess.run([sys.executable, "-B", str(SCRIPT), str(temp), "*.lean"], capture_output=True, text=True)
            self.assertNotEqual(report.returncode, 0)
            self.assertEqual(json.loads(report.stdout)["incremental"]["comparison_status"], "current-incomplete")
        clean = b'def a : String := "set_option x in theorem fake"\ndef b : Nat := 0\n'
        self.assertEqual(len(scanner.scan(root / "E.lean", root, clean)), 2)

    def test_scoped_open_inline_declarations_fail_closed(self):
        root = Path("/virtual")
        cases = (
            b"open Nat in theorem hidden : True := by trivial\ndef visible : Nat := 0\n",
            b"open Nat\n  in private\n  def hidden : Nat := 0\ndef visible : Nat := 0\n",
            b"open scoped Foo in @[simp]\n  theorem hidden : True := by trivial\n",
        )
        for source in cases:
            with self.subTest(source=source):
                with self.assertRaisesRegex(ValueError, "unsupported same-line scoped open declaration"):
                    scanner.scan(root / "A.lean", root, source)
        following = b"open Nat in\ntheorem visible : True := by trivial\n"
        self.assertEqual(scanner.scan(root / "B.lean", root, following)[0]["name"], "visible")
        ordinary = b'open Nat\ndef str : String := "open Nat in theorem fake"\n'
        self.assertEqual(scanner.scan(root / "C.lean", root, ordinary)[0]["name"], "str")
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            (temp / "A.lean").write_bytes(cases[0])
            (temp / "B.lean").write_bytes(following)
            report = subprocess.run([sys.executable, "-B", str(SCRIPT), str(temp), "*.lean"], capture_output=True, text=True)
            self.assertNotEqual(report.returncode, 0)
            value = json.loads(report.stdout)
            self.assertEqual(value["incremental"]["comparison_status"], "current-incomplete")
            self.assertIsNone(value["incremental"]["removed"])

    def test_equal_context_does_not_prove_local_definition_equivalence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, typ in (("A.lean", "Nat"), ("B.lean", "Int")):
                (root / name).write_text("namespace N\ndef T := " + typ + "\ntheorem same (x : T) : x = x := by rfl\nend N\n")
            data = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            group = next(g for g in data["candidates"] if {m["path"] for m in g["members"]} == {"A.lean", "B.lean"} and all(m["name"] == "same" for m in g["members"]))
            self.assertIn("intrinsic-signature-unresolved", group["reject_reasons"])
            self.assertIn("ownership-requires-live-verification", group["reject_reasons"])

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

    def test_late_candidate_serialization_failure_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text("theorem a (x : Nat) : x = x := by rfl\ntheorem b (y : Nat) : y = y := by rfl\n")
            base_cmd = [sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]
            previous = root / "previous.json"
            previous.write_bytes(subprocess.check_output(base_cmd))
            args = [str(SCRIPT), str(root), "*.lean"] + pinned(previous)
            original = json.dumps
            def checked_dumps(value, *pos, **kwargs):
                if isinstance(value, dict) and "lexical_key" in value and kwargs.get("sort_keys"):
                    raise RecursionError("simulated late nesting")
                return original(value, *pos, **kwargs)
            errors = io.StringIO()
            with mock.patch.object(sys, "argv", args), mock.patch.object(scanner.json, "dumps", side_effect=checked_dumps), contextlib.redirect_stderr(errors):
                with self.assertRaises(SystemExit) as outcome:
                    scanner.main()
            self.assertNotEqual(outcome.exception.code, 0)
            self.assertIn("previous candidate comparison", errors.getvalue())
            self.assertNotIn("Traceback", errors.getvalue())

    def test_internal_aliases_keep_paths_owners_and_shared_source_warning(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Target.lean").write_text("theorem same : True := by trivial\n")
            for name in ("A.lean", "B.lean"):
                (root / name).symlink_to("Target.lean")
            owners = {name: name for name in ("A.lean", "B.lean", "Target.lean")}
            config = root / "owners.json"
            config.write_text(json.dumps(owners))
            cmd = [sys.executable, "-B", str(SCRIPT), str(root), "*.lean", "A.*", "--owners", str(config)]
            report = json.loads(subprocess.check_output(cmd))
            self.assertEqual([x["path"] for x in report["inputs"]], sorted(owners))
            self.assertEqual({row["path"]: row["owner"] for row in report["inventory"]}, owners)
            self.assertEqual(report["input_aliases"], [{"path": name, "resolved_path": "Target.lean"} for name in ("A.lean", "B.lean")])
            self.assertIn("shared-resolved-source", report["candidates"][0]["reject_reasons"])
            self.assertIn("shared-resolved-source", report["body_candidates"][0]["reject_reasons"])
            self.assertEqual(subprocess.check_output(cmd), subprocess.check_output(cmd))

    def test_alias_selection_uses_alias_extension(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Backing.txt").write_text("theorem actual : True := by trivial\n")
            (root / "Selected.lean").symlink_to("Backing.txt")
            report = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"]))
            self.assertEqual([row["path"] for row in report["inventory"]], ["Selected.lean"])
            self.assertEqual(report["input_aliases"], [{"path": "Selected.lean", "resolved_path": "Backing.txt"}])

    def test_bad_selected_links_are_errors_not_silent_omissions(self):
        for kind in ("broken", "outside", "loop", "directory"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                parent = Path(directory)
                root = parent / "root"
                root.mkdir()
                (root / "Good.lean").write_text("theorem good : True := by trivial\n")
                (parent / "Outside.lean").write_text("theorem outside : True := by trivial\n")
                bad = root / "Bad.lean"
                if kind == "directory":
                    bad.mkdir()
                else:
                    target = {"broken": "Missing.lean", "outside": "../Outside.lean", "loop": "Bad.lean"}[kind]
                    bad.symlink_to(target)
                result = subprocess.run([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"], capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                report = json.loads(result.stdout)
                self.assertEqual([row["path"] for row in report["inventory"]], ["Good.lean"])
                self.assertEqual([row["path"] for row in report["errors"]], [str(bad)])
                self.assertEqual(report["unmatched_patterns"], [])
                self.assertEqual(report["incremental"]["comparison_status"], "current-incomplete")
                self.assertIsNone(report["incremental"]["added"])

    def test_explicit_directory_alias_keeps_selected_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "real").mkdir()
            (root / "real" / "A.lean").write_text("theorem a : True := by trivial\n")
            (root / "alias").symlink_to("real", target_is_directory=True)
            report = json.loads(subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "alias/*.lean"]))
            self.assertEqual([row["path"] for row in report["inputs"]], ["alias/A.lean"])
            self.assertEqual(report["input_aliases"], [{"path": "alias/A.lean", "resolved_path": "real/A.lean"}])

    def test_unreadable_selected_subtree_is_explicit_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Good.lean").write_text("theorem good : True := by trivial\n")
            locked = root / "locked"
            locked.mkdir()
            (locked / "Hidden.lean").write_text("theorem hidden : True := by trivial\n")
            locked.chmod(0)
            try:
                result = subprocess.run([sys.executable, "-B", str(SCRIPT), str(root), "**/*.lean"], capture_output=True)
            finally:
                locked.chmod(0o700)
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(result.stdout)
            self.assertTrue(report["errors"])
            self.assertEqual({row["path"] for row in report["errors"]}, {str(locked)})
            self.assertEqual(report["incremental"]["comparison_status"], "current-incomplete")
            self.assertIsNone(report["incremental"]["candidate_groups"])
            self.assertEqual([row["path"] for row in report["inventory"]], ["Good.lean"])

    def test_selector_matches_supported_path_globs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("A.lean", ".Hidden.lean", "sub/B.lean", "sub/deep/C.lean", "sub/Other.txt"):
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text("theorem ok : True := by trivial\n")
            (root / "alias").symlink_to("sub", target_is_directory=True)
            for pattern in ("*.lean", "**/*.lean", "sub/**/*.lean", "*/B.lean", "alias/*.lean", "[A-Z].lean", "missing/*.lean", "sub/**/C.lean"):
                with self.subTest(pattern=pattern):
                    errors=[]
                    actual={p.relative_to(root).as_posix() for p in scanner.selected_paths(root,pattern,errors)}
                    expected={p.relative_to(root).as_posix() for p in root.glob(pattern)}
                    self.assertEqual(actual,expected)
                    if pattern == "**/*.lean":
                        self.assertEqual([e["path"] for e in errors], [str(root / "alias")])
                        self.assertIn("skips directory symlink", errors[0]["reason"])
                    else:
                        self.assertEqual(errors,[])

    def test_recursive_directory_alias_reports_incomplete(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "real").mkdir()
            (root / "real" / "A.lean").write_text("def a : Nat := 0\n")
            cmd = [sys.executable, "-B", str(SCRIPT), str(root), "**/*.lean"]
            baseline = root / "prior.json"
            baseline.write_bytes(subprocess.check_output(cmd))
            (root / "alias").symlink_to("real", target_is_directory=True)
            result = subprocess.run(cmd + pinned(baseline), capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(result.stdout)
            self.assertTrue(any("skips directory symlink" in e["reason"] for e in report["errors"]))
            self.assertEqual(report["incremental"]["comparison_status"], "current-incomplete")
            self.assertIsNone(report["incremental"]["removed"])
            self.assertIsNone(report["incremental"]["candidate_groups"])
            explicit = subprocess.check_output([sys.executable, "-B", str(SCRIPT), str(root), "alias/*.lean"])
            self.assertEqual(json.loads(explicit)["inputs"][0]["path"], "alias/A.lean")
            (root / "alias").unlink()
            (root / "dangling").symlink_to("missing", target_is_directory=True)
            result = subprocess.run(cmd, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads(result.stdout)["incremental"]["comparison_status"], "current-incomplete")

    def test_finite_dangling_directory_alias_is_incomplete(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "good").mkdir()
            (root / "good" / "Target.lean").write_text("def good : Nat := 0\n")
            cmd = [sys.executable, "-B", str(SCRIPT), str(root), "*/Target.lean"]
            baseline = root / "prior.json"
            baseline.write_bytes(subprocess.check_output(cmd))
            (root / "dangling").symlink_to("missing", target_is_directory=True)
            result = subprocess.run(cmd + pinned(baseline), capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(result.stdout)
            self.assertTrue(any(Path(e["path"]).name == "dangling" for e in report["errors"]))
            self.assertEqual(report["incremental"]["comparison_status"], "current-incomplete")
            self.assertIsNone(report["incremental"]["removed"])
            explicit = subprocess.run([sys.executable, "-B", str(SCRIPT), str(root), "good/Target.lean", "dangling/*.lean"], capture_output=True, text=True)
            self.assertNotEqual(explicit.returncode, 0)
            self.assertTrue(any(Path(e["path"]).name == "dangling" for e in json.loads(explicit.stdout)["errors"]))

    def test_external_directory_alias_is_not_enumerated(self):
        with tempfile.TemporaryDirectory() as directory, tempfile.TemporaryDirectory() as outside:
            root, foreign = Path(directory), Path(outside)
            (root / "good").mkdir()
            (root / "good" / "Target.lean").write_text("def good : Nat := 0\n")
            (foreign / "Target.lean").write_text("def foreign : Nat := 0\n")
            (root / "external").symlink_to(foreign, target_is_directory=True)
            for pattern in ("external/*.lean", "*/Target.lean"):
                result = subprocess.run([sys.executable, "-B", str(SCRIPT), str(root), pattern], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                report = json.loads(result.stdout)
                self.assertTrue(any("resolves outside root" in e["reason"] for e in report["errors"]))
                self.assertFalse(any(r["path"].startswith("external/") for r in report["inputs"]))
                self.assertEqual(report["incremental"]["comparison_status"], "current-incomplete")
            original = scanner.os.scandir
            def guarded(path):
                if Path(path) == root / "external":
                    raise AssertionError("outside alias must not be enumerated")
                return original(path)
            errors = []
            with mock.patch.object(scanner.os, "scandir", guarded):
                list(scanner.selected_paths(root, "external/*.lean", errors))
            self.assertTrue(any("resolves outside root" in e["reason"] for e in errors))

    def test_nonrecursive_selection_does_not_read_unselected_subtree(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root / "Good.lean").write_text("theorem good : True := by trivial\n")
            locked=root/"locked";locked.mkdir();locked.chmod(0)
            try:
                report=json.loads(subprocess.check_output([sys.executable,"-B",str(SCRIPT),str(root),"*.lean"]))
            finally:
                locked.chmod(0o700)
            self.assertEqual(report["errors"],[])
            self.assertEqual([row["path"] for row in report["inputs"]],["Good.lean"])

    def test_trailing_separator_is_directory_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root / "File.lean").write_text("theorem file : True := by trivial\n")
            (root / "Dir.lean").mkdir()
            for pattern in ("*.lean/", "File.lean/", "Dir.lean/", "**/*.lean/"):
                with self.subTest(pattern=pattern):
                    errors=[]
                    actual={p.relative_to(root).as_posix() for p in scanner.selected_paths(root,pattern,errors)}
                    expected={p.relative_to(root).as_posix() for p in root.glob(pattern)}
                    self.assertEqual(actual,expected)
                    self.assertEqual(errors,[])

    def test_exact_path_needs_execute_permission_not_directory_listing(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            locked=root/"execute-only";locked.mkdir()
            source=locked/"A.lean";source.write_text("theorem a : True := by trivial\n")
            locked.chmod(0o100)
            try:
                report=json.loads(subprocess.check_output([sys.executable,"-B",str(SCRIPT),str(root),"execute-only/A.lean"]))
                wildcard=subprocess.run([sys.executable,"-B",str(SCRIPT),str(root),"execute-only/*.lean"],capture_output=True)
            finally:
                locked.chmod(0o700)
            self.assertEqual(report["errors"],[])
            self.assertEqual([row["path"] for row in report["inputs"]],["execute-only/A.lean"])
            self.assertNotEqual(wildcard.returncode,0)
            self.assertEqual(json.loads(wildcard.stdout)["incremental"]["comparison_status"],"current-incomplete")

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
            stable_bytes = subprocess.check_output(cmd + pinned(previous))
            self.assertEqual(stable_bytes, subprocess.check_output(cmd + pinned(previous)))
            stable = json.loads(stable_bytes)
            self.assertEqual(stable["incremental"]["previous_provenance"], "caller-pin-unverified")
            self.assertEqual(stable["incremental"]["previous_sha256"], hashlib.sha256(first).hexdigest())
            self.assertNotEqual(subprocess.run(cmd + ["--previous", str(previous)], capture_output=True).returncode, 0)
            self.assertNotEqual(subprocess.run(cmd + ["--previous-sha256", "0" * 64], capture_output=True).returncode, 0)
            bad_pin = subprocess.run(cmd + ["--previous", str(previous), "--previous-sha256", "0" * 64], capture_output=True)
            self.assertNotEqual(bad_pin.returncode, 0)
            self.assertIn(b"SHA256 mismatch", bad_pin.stderr)
            original_pin = hashlib.sha256(first).hexdigest()
            previous.write_bytes(first + b" ")
            changed_bytes = subprocess.run(cmd + ["--previous", str(previous), "--previous-sha256", original_pin], capture_output=True)
            self.assertNotEqual(changed_bytes.returncode, 0)
            self.assertIn(b"SHA256 mismatch", changed_bytes.stderr)
            previous.write_bytes(first)
            malformed_pin = subprocess.run(cmd + ["--previous", str(previous), "--previous-sha256", "G" * 64], capture_output=True)
            self.assertNotEqual(malformed_pin.returncode, 0)
            self.assertIn(b"64 lowercase hexadecimal", malformed_pin.stderr)
            with mock.patch.object(scanner, "MAX_PREVIOUS_BYTES", 16):
                with self.assertRaisesRegex(ValueError, "byte limit"):
                    scanner.load_previous(previous, hashlib.sha256(first).hexdigest())
            invalid = root / "invalid.json"
            invalid.write_bytes(b"null")
            null_result = subprocess.run(cmd + pinned(invalid), capture_output=True)
            self.assertNotEqual(null_result.returncode, 0)
            self.assertIn(b"incompatible version or selection", null_result.stderr)
            duplicate_json = first.replace(b'"version": 2', b'"version": 2, "version": 2', 1)
            invalid.write_bytes(duplicate_json)
            duplicate_result = subprocess.run(cmd + pinned(invalid), capture_output=True)
            self.assertNotEqual(duplicate_result.returncode, 0)
            self.assertIn(b"duplicate previous JSON key", duplicate_result.stderr)
            nonfinite_json = first.replace(b'"version": 2', b'"version": NaN', 1)
            invalid.write_bytes(nonfinite_json)
            nonfinite_result = subprocess.run(cmd + pinned(invalid), capture_output=True)
            self.assertNotEqual(nonfinite_result.returncode, 0)
            self.assertIn(b"non-integer previous JSON number", nonfinite_result.stderr)
            invalid.write_bytes(b"[" * 2000 + b"]" * 2000)
            deep_result = subprocess.run(cmd + pinned(invalid), capture_output=True)
            self.assertNotEqual(deep_result.returncode, 0)
            self.assertNotIn(b"Traceback", deep_result.stderr)
            malformed_group = json.loads(first)
            malformed_group["candidates"][0]["members"] = "not-a-list"
            invalid.write_text(json.dumps(malformed_group))
            malformed_result = subprocess.run(cmd + pinned(invalid), capture_output=True)
            self.assertNotEqual(malformed_result.returncode, 0)
            self.assertIn(b"malformed previous statement candidate", malformed_result.stderr)
            malformed_group["candidates"][0]["members"] = [None, None]
            invalid.write_text(json.dumps(malformed_group))
            malformed_result = subprocess.run(cmd + pinned(invalid), capture_output=True)
            self.assertNotEqual(malformed_result.returncode, 0)
            self.assertIn(b"malformed previous statement candidate", malformed_result.stderr)
            malformed_group["candidates"][0]["members"] = copy.deepcopy(data["candidates"][0]["members"])
            malformed_group["candidates"][0]["members"][0]["line"] = True
            invalid.write_text(json.dumps(malformed_group))
            malformed_result = subprocess.run(cmd + pinned(invalid), capture_output=True)
            self.assertNotEqual(malformed_result.returncode, 0)
            self.assertIn(b"malformed previous statement candidate", malformed_result.stderr)
            forged = json.loads(first)
            forged["inventory"][0]["name"] = "caller-fabricated"
            invalid.write_text(json.dumps(forged))
            forged_result = json.loads(subprocess.check_output(cmd + pinned(invalid)))
            self.assertEqual(forged_result["incremental"]["previous_provenance"], "caller-pin-unverified")
            self.assertEqual(stable["incremental"]["candidate_groups"]["statements"]["changed"], [])
            mismatch = subprocess.run([sys.executable, "-B", str(SCRIPT), str(root), "*.lean"] + pinned(previous), capture_output=True)
            self.assertNotEqual(mismatch.returncode, 0)
            self.assertIn(b"incompatible version or selection", mismatch.stderr)
            corrupt = json.loads(first)
            corrupt["inputs"].append(corrupt["inputs"][0])
            bad = root / "bad.json"
            bad.write_text(json.dumps(corrupt))
            self.assertNotEqual(subprocess.run(cmd + pinned(bad), capture_output=True).returncode, 0)
            owner.write_text(json.dumps({"A.lean": "lane-b"}))
            changed_owner = json.loads(subprocess.check_output(cmd + pinned(previous)))
            self.assertTrue(changed_owner["incremental"]["owner_config_changed"])
            self.assertEqual(len(changed_owner["incremental"]["candidate_groups"]["statements"]["changed"]), 1)
            self.assertEqual(len(changed_owner["incremental"]["candidate_groups"]["bodies"]["changed"]), 1)
            corrupt["inputs"].pop()
            corrupt["errors"] = [{"path": "A.lean", "reason": "unreadable"}]
            bad.write_text(json.dumps(corrupt))
            bad_result = subprocess.run(cmd + pinned(bad), capture_output=True)
            self.assertNotEqual(bad_result.returncode, 0)
            self.assertIn(b"previous report is incomplete", bad_result.stderr)
            corrupt["errors"] = []
            corrupt["unmatched_patterns"] = ["missing/*.lean"]
            bad.write_text(json.dumps(corrupt))
            bad_result = subprocess.run(cmd + pinned(bad), capture_output=True)
            self.assertNotEqual(bad_result.returncode, 0)
            self.assertIn(b"previous report is incomplete", bad_result.stderr)
            (root / "B.lean").write_text("/- unterminated")
            incomplete = subprocess.run(cmd + pinned(previous), capture_output=True)
            self.assertNotEqual(incomplete.returncode, 0)
            self.assertEqual(json.loads(incomplete.stdout)["incremental"]["comparison_status"], "current-incomplete")
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["candidate_groups"])
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["removed"])
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["added"])
            self.assertIsNone(json.loads(incomplete.stdout)["incremental"]["changed"])
            (root / "B.lean").write_text("theorem b (y : Nat) : y = y := by rfl\n")
            registry.write_text(json.dumps({"items": []}))
            changed_registry = json.loads(subprocess.check_output(cmd + pinned(previous)))
            self.assertTrue(changed_registry["incremental"]["registry_changed"])
            (root / "A.lean").unlink()
            (root / "B.lean").write_text("theorem b : True := by trivial\n")
            (root / "D.lean").write_text("def d : Int := 0\ndef e : Int := 0\n")
            data = json.loads(subprocess.check_output(cmd + pinned(previous)))
            self.assertEqual(data["incremental"]["removed"], ["A.lean"])
            self.assertEqual(data["incremental"]["changed"], ["B.lean"])
            self.assertTrue(data["incremental"]["candidate_groups"]["statements"]["removed"])
            self.assertTrue(data["incremental"]["candidate_groups"]["statements"]["added"])
            self.assertTrue(data["incremental"]["candidate_groups"]["bodies"]["removed"])
            self.assertTrue(data["incremental"]["candidate_groups"]["bodies"]["added"])

if __name__ == "__main__":
    unittest.main()
