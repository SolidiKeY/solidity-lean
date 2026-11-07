import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("vector_census", ROOT / "scripts/h55/vectors-tables/vector_census.py")
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)

class CensusTests(unittest.TestCase):
    def test_full_inventory(self):
        expected = json.loads(c.MANIFEST.read_text())["files"]
        self.assertEqual(c.census(ROOT), expected)
        self.assertEqual(sum(row["count"] for row in expected.values()), 6903)
        self.assertEqual(len(expected), 9)

    def test_negative_controls(self):
        path = c.PATHS[0]
        original = (ROOT / path).read_bytes()
        lines = original.splitlines(keepends=True)
        positions = [i for i, line in enumerate(lines) if line.startswith(b"theorem ")]
        expected = c.audit(path, original)
        def rejected(changed):
            try:
                return c.audit(path, b"".join(changed)) != expected
            except (ValueError, UnicodeDecodeError):
                return True
        missing = lines.copy(); missing.pop(positions[5])
        extra = lines.copy(); extra.insert(positions[5], lines[positions[5]])
        order = lines.copy(); order[positions[5]], order[positions[6]] = order[positions[6]], order[positions[5]]
        schema = lines.copy(); schema[positions[5]] = schema[positions[5]].replace(b"decide +kernel", b"rfl")
        changed_output = lines.copy(); changed_output[positions[0]] = changed_output[positions[0]].replace(b".val = 0", b".val = 1")
        for label, mutation in [("missing", missing), ("extra", extra), ("order", order), ("schema", schema), ("output", changed_output)]:
            with self.subTest(label=label): self.assertTrue(rejected(mutation))

if __name__ == "__main__": unittest.main()
