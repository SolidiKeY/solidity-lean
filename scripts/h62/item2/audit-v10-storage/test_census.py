#!/usr/bin/env python3
"""Regression checks for actual review findings; no theorem verification claim."""
import unittest
import census

class SignatureTests(unittest.TestCase):
    def signature(self, source):
        code = census.mask(source)
        m = census.COMMAND.search(code)
        return source[m.start():census.signature_end(code, m.end())].strip()

    def test_let_result_retained(self):
        signature = "theorem witness (n : Nat) : let after := n + 1; after > n"
        self.assertEqual(self.signature(signature + " := by omega"), signature)

    def test_match_conclusion_retained(self):
        signature = "theorem f (n : Nat) : n = match n with\n | 0 => 0\n | k+1 => k+1"
        self.assertEqual(self.signature(signature + " := by rfl"), signature)

    def test_equation_body_excluded(self):
        signature = "theorem slot_self : (n : Nat) → n = n"
        self.assertEqual(self.signature(signature + "\n | n => rfl\ndef next := 1"), signature)

    def test_nested_defaults_and_comments(self):
        signature = "theorem f (n : Nat := 1) : n = n"
        source = signature + ' := by /- outer /- theorem bad : False := -/ -/ rfl'
        self.assertEqual(self.signature(source), signature)

    def test_strings_do_not_create_declarations(self):
        source = 'def fake := "theorem fake : False :="\n/- theorem bad : False := by -/\ntheorem real : True := True.intro'
        self.assertEqual([m.group(2) for m in census.COMMAND.finditer(census.mask(source))], ['real'])

if __name__ == '__main__': unittest.main()
