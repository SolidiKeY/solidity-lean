#!/usr/bin/env python3
"""Meaningful lexical regressions: strings/comments must not invent controls."""
import unittest
from census import declarations, mask, inventory
from pathlib import Path

class CensusTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        s = '-- theorem fake : False := nope\n/- outer /- inner -/ theorem fake2 -/\n' + 'def text := "theorem fake3 := \\"x"\nexample : text = text := rfl\n'
        self.assertEqual([d['kind'] for d in declarations(s)], ['def', 'example'])
    def test_header_ignores_literal_assignment(self):
        s = 'theorem t : "x:=y" = "x:=y" := rfl\n'
        self.assertEqual(declarations(s)[0]['source_header'], 'theorem t : "x:=y" = "x:=y"')
    def test_prime_char_and_raw(self):
        s = "def x' := 'a'\ndef raw := r##\"theorem hidden := \"##\nexample : x' = x' := rfl\n"
        self.assertEqual(len(declarations(s)), 3)
        self.assertEqual(len(mask(s)), len(s))
    def test_refuses_truncated_input(self):
        with self.assertRaises(ValueError):
            mask('/- unclosed')
    def test_named_argument_and_default_binder(self):
        for s in ['theorem t (n : Nat := 0) : n = n := rfl',
                  'theorem t : P (x := true) = True := proof',
                  'theorem t : (let x := 0; x = 0) := proof']:
            self.assertEqual(declarations(s)[0]['source_header'], s.rsplit(' := ', 1)[0])
        a = declarations('theorem t : P (x := true) = True := proof')[0]
        b = declarations('theorem t : P (x := false) = False := proof')[0]
        self.assertNotEqual(a['source_header_sha256'], b['source_header_sha256'])
    def test_attributes_and_opaque(self):
        self.assertEqual(len(declarations('@[simp] theorem t : True := proof')), 1)
        self.assertEqual(declarations('opaque t : Nat := 0')[0]['kind'], 'opaque')
    def test_equation_boundary(self):
        self.assertEqual(declarations('def f : Nat → Nat\n | 0 => 1\n | n+1 => n')[0]['source_header'], 'def f : Nat → Nat')
    def test_keywords_operators_and_unparenthesized_let(self):
        for s in ['theorem somewhere : True := proof',
                  'theorem t : a || b = true := proof',
                  'theorem t : let x := 0; x = 0 := proof']:
            self.assertEqual(declarations(s)[0]['source_header'], s.rsplit(' := ', 1)[0])
    def test_missing_scope(self):
        with self.assertRaises(ValueError):
            inventory(Path('/nonexistent-h62-scope'))
    def test_statement_drift_changes_hash(self):
        a = declarations('theorem t : True := True.intro')[0]
        b = declarations('theorem t : False := nope')[0]
        self.assertNotEqual(a['source_header_sha256'], b['source_header_sha256'])

if __name__ == '__main__':
    unittest.main()
