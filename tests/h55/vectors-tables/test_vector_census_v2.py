import importlib.util
import json
import shutil
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("vector_census_v2", ROOT / "scripts/h55/vectors-tables/vector_census_v2.py")
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
ASSEMBLY, ASSEMBLY_LINE, TABLE = c.TABLES["shifts"]

class CensusV2Tests(unittest.TestCase):
    def test_full_inventory(self):
        expected = json.loads(c.MANIFEST.read_text())
        self.assertEqual(expected["v1_base"], c.V1_BASE)
        self.assertEqual(c.census(ROOT), expected["families"])
        self.assertEqual(sum(row["count"] for row in expected["families"].values()), 6903)
        self.assertEqual(expected["families"]["shifts"]["count"], 3885)

    def test_layouts_agree(self):
        theorem = "theorem v0007 : (Pure.eval .«shl» (fun i => if i.val = 0 then word 1 else word 57)).val = 114 := by decide +kernel"
        table = "noncomputable def t : List Row := [\n  ⟨.«shl», 1, 57, 114⟩\n]"
        self.assertEqual(c.tuples("t", theorem), c.tuples("t", table, "t"))
        unary = "theorem v0001 : (Pure.eval .«not» (fun _ => word 0)).val = 5 := by decide +kernel"
        self.assertEqual(c.tuples("t", unary), [("not", ["0"], "5")])

    def test_negative_controls(self):
        paths = [*c.FAMILIES["shifts"], ASSEMBLY]
        texts = {p: (ROOT / p).read_text(encoding="utf-8") for p in paths}
        expected = c.census(ROOT)["shifts"]
        path = next(iter(TABLE))
        lines = texts[path].splitlines(keepends=True)
        pos = [i for i, line in enumerate(lines) if line.startswith("  ⟨")]
        opening = next(i for i, line in enumerate(lines) if c.OPEN.fullmatch(line.rstrip("\n")))
        closing = next(i for i, line in enumerate(lines) if line == "]\n")
        def edit(i, old, new):
            changed = lines.copy(); changed[i] = changed[i].replace(old, new, 1)
            return {path: "".join(changed)}
        def rows(changed): return {path: "".join(changed)}
        missing = lines.copy(); missing.pop(pos[5])
        extra = lines.copy(); extra.insert(pos[5], lines[pos[5]])
        order = lines.copy(); order[pos[5]], order[pos[6]] = order[pos[6]], order[pos[5]]
        commented = lines[:pos[-2]] + ["/-\n"] + lines[pos[-2]:pos[-1] + 1] + ["-/\n"] + lines[pos[-1] + 1:]
        indented = lines.copy(); indented.insert(pos[3], "   " + lines[pos[3]].lstrip())
        second = lines[:closing + 1] + ["noncomputable def unused : List Row := [\n", lines[pos[-1]], "]\n"] + lines[closing + 1:]
        line_comment = lines.copy(); line_comment.insert(pos[2], "  -- ⟨.«shl», 9, 9, 9⟩,\n")
        mutations = {
            "missing": rows(missing), "extra": rows(extra), "order": rows(order),
            "schema": edit(pos[5], "⟩", ", 0⟩"), "output": edit(pos[0], ", 0⟩", ", 1⟩"),
            "operand": edit(pos[1], ", 1, ", ", 2, "),
            "block comment": rows(commented), "indented row": rows(indented),
            "second list": rows(second), "line comment": rows(line_comment),
            "list wrapper": edit(opening, ":= [", ":= List.drop 3 ["),
            "list suffix": edit(closing, "]", "].take 5"),
            "assembly": {ASSEMBLY: texts[ASSEMBLY].replace(ASSEMBLY_LINE, ASSEMBLY_LINE.replace("shlRows ++ shrRows", "shrRows ++ shlRows"))},
            "renamed list": edit(opening, TABLE[path], TABLE[path] + "X"),
        }
        for label, changed in mutations.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                for p in [q for qs in c.FAMILIES.values() for q in qs] + [ASSEMBLY]:
                    (Path(tmp) / p).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / p, Path(tmp) / p)
                for p, text in changed.items():
                    self.assertNotEqual(text, texts[p])
                    (Path(tmp) / p).write_text(text, encoding="utf-8")
                try:
                    self.assertNotEqual(c.census(Path(tmp))["shifts"], expected)
                except ValueError:
                    pass

if __name__ == "__main__": unittest.main()
