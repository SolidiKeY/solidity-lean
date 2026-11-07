#!/usr/bin/env python3
"""Textual drift check only; this does not prove a Lean correspondence."""
import hashlib
import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parents[3]
SOURCE = ROOT / "Solidity/Source/Observe.lean"
FIXTURE = ROOT / "tests/h62/item1/packet-panic/PanicBytesFixture.lean"


class FixtureShapeTest(unittest.TestCase):
    def test_reviewed_source_and_local_recurrence(self):
        data = SOURCE.read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(),
                         "82db004513511e206ee57eb7437831d8908df9cab29b18271092406ccb166212")
        source = data.decode("utf-8")
        fixture_data = FIXTURE.read_bytes()
        self.assertEqual(hashlib.sha256(fixture_data).hexdigest(),
                         "60c0c6e2c1747b48384421bba6009ba1360a9f40387012b74864e004681f94f0")
        fixture = fixture_data.decode("utf-8")
        def recurrence(text, name):
            match = re.search(rf"(?m)^def {name} : Nat → Nat → List UInt8\n  \| 0, _ => \[\]\n  \| k \+ 1, n => .*?$", text)
            self.assertIsNotNone(match)
            return match.group().replace(name, "beBytes")
        self.assertEqual(recurrence(source, "beBytes"), recurrence(fixture, "fixtureBeBytes"))
        for fragment in (
            "def toWord (n : Nat) : Word := ⟨n % 2 ^ 256, Nat.mod_lt _ (by decide)⟩",
            "def wordBytes (w : Word) : Bytes := beBytes 32 w.val",
            "def panicSelector : Bytes := [0x4e, 0x48, 0x7b, 0x71]",
            "  | .arithmetic => 0x11",
            "  | .divZero => 0x12",
            "def panicData (c : PanicCode) : Bytes := panicSelector ++ wordBytes (toWord c.code)",
        ):
            self.assertIn(fragment, source)
        self.assertIn("[0x4e,0x48,0x7b,0x71] ++ fixtureBeBytes 32 (code % 2 ^ 256)", fixture)


if __name__ == "__main__":
    unittest.main()
