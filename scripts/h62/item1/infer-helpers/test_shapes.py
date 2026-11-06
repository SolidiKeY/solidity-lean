#!/usr/bin/env python3
"""Exercise acceptance and semantic-change rejection of the shape census."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
import check_shapes

ROOT = Path(__file__).resolve().parents[4]

class ShapeTest(unittest.TestCase):
    def test_snapshots_and_mutations(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            originals = {}
            for path in check_shapes.EXPECTED:
                originals[path] = (ROOT / path).read_text()
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(originals[path])
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(check_shapes.check(root), 0)
                for path, names in check_shapes.EXPECTED.items():
                    for name in names:
                        with self.subTest(path=path, name=name):
                            text = originals[path]
                            start = text.index("def " + name + " ")
                            if "Mapping" in name:
                                pos = text.index(".mapping _ _", start)
                                mutated = text[:pos] + text[pos:].replace(".mapping _ _", ".mapping _ .bool", 1)
                            elif "ayable" in name:
                                pos = text.index("=> true", start)
                                mutated = text[:pos] + text[pos:].replace("=> true", "=> false", 1)
                            else:
                                pos = text.index("=> .memory", start)
                                mutated = text[:pos] + text[pos:].replace("=> .memory", "=> .storage", 1)
                            (root / path).write_text(mutated)
                            self.assertEqual(check_shapes.check(root), 1)
                            (root / path).write_text(text)
                path = next(iter(originals))
                target = root / path
                original = originals[path]
                declaration = "def STy.isMapping (τ : STy) : Bool := τ matches .mapping _ _"
                target.write_text(original.replace(declaration, "/- " + declaration + " -/", 1))
                self.assertEqual(check_shapes.check(root), 1)
                target.write_text("/- outer /- nested -/\ndef STy.isMapping (τ : STy) : Bool := false\n-/\n" + original)
                self.assertEqual(check_shapes.check(root), 0)
                target.write_text(original + "\n/- unclosed")
                self.assertEqual(check_shapes.check(root), 1)
                target.write_text(original)
                target.write_text(originals[path] + "\ndef STy.isMapping (τ : STy) : Bool := false\n")
                self.assertEqual(check_shapes.check(root), 1)
                target.write_text(originals[path].replace("=> true", "=> tr ue", 1))
                self.assertEqual(check_shapes.check(root), 1)
                target.unlink()
                self.assertEqual(check_shapes.check(root), 1)

if __name__ == "__main__":
    unittest.main()
