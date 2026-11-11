import importlib.util
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
spec = importlib.util.spec_from_file_location("vector_census_v2", ROOT / "scripts/h55/vectors-tables/vector_census_v2.py")
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)

class CensusV2Tests(unittest.TestCase):
    def test_full_inventory(self):
        expected = json.loads(c.MANIFEST.read_text())
        self.assertEqual(expected["v1_base"], c.V1_BASE)
        self.assertEqual(c.census(ROOT), expected["families"])
        self.assertEqual(sum(row["count"] for row in expected["families"].values()), 6903)
        self.assertEqual(expected["families"]["shifts"]["count"], 3885)

    def test_layouts_agree(self):
        theorem = "theorem v0007 : (Pure.eval .«shl» (fun i => if i.val = 0 then word 1 else word 57)).val = 114 := by decide +kernel"
        row = "  ⟨.«shl», 1, 57, 114⟩,"
        self.assertEqual(c.tuples("t", theorem), c.tuples("t", row))
        unary = "theorem v0001 : (Pure.eval .«not» (fun _ => word 0)).val = 5 := by decide +kernel"
        self.assertEqual(c.tuples("t", unary), [("not", ["0"], "5")])

    def test_negative_controls(self):
        paths = c.FAMILIES["shifts"]
        texts = {p: (ROOT / p).read_text(encoding="utf-8") for p in paths}
        expected = c.census(ROOT)["shifts"]
        def family(changed):
            rows = [r for p in paths for r in c.tuples(p, changed.get(p, texts[p]))]
            return {"count": len(rows), "sha256": c.digest(rows)}
        path = next(p for p in paths if "  ⟨" in texts[p])
        lines = texts[path].splitlines(keepends=True)
        pos = [i for i, line in enumerate(lines) if line.startswith("  ⟨")]
        def rejected(new_lines):
            try:
                return family({path: "".join(new_lines)}) != expected
            except ValueError:
                return True
        missing = lines.copy(); missing.pop(pos[5])
        extra = lines.copy(); extra.insert(pos[5], lines[pos[5]])
        order = lines.copy(); order[pos[5]], order[pos[6]] = order[pos[6]], order[pos[5]]
        schema = lines.copy(); schema[pos[5]] = schema[pos[5]].replace("⟩", ", 0⟩")
        output = lines.copy(); output[pos[0]] = output[pos[0]].replace(", 0⟩", ", 1⟩")
        operand = lines.copy(); operand[pos[1]] = operand[pos[1]].replace(", 1, ", ", 2, ", 1)
        for label, mutation in [("missing", missing), ("extra", extra), ("order", order),
                                ("schema", schema), ("output", output), ("operand", operand)]:
            with self.subTest(label=label):
                self.assertNotEqual(mutation, lines)
                self.assertTrue(rejected(mutation))

if __name__ == "__main__": unittest.main()
