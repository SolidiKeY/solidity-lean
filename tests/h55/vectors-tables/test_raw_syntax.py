import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import raw_census as raw
import raw_syntax as syntax

class RawSyntaxTests(unittest.TestCase):
    def test_log_inventory_and_mutations(self):
        names = list(raw.collect(ROOT))
        node = "NODE Lean.Parser.Tactic.case some { byteIdx := 0 } some { byteIdx := 1 }"
        lines = []
        for name in names:
            path = "Solidity/Yul/" + name
            lines.extend(["FILE " + path, node, "END " + path])
        baseline = syntax.parse_log("\n".join(lines))
        self.assertEqual(len(baseline), 102)
        self.assertEqual(sum(map(len, baseline.values())), 102)
        variants = {}
        x=lines.copy(); x.pop(1); variants["missing"] = x
        x=lines.copy(); x.insert(1,node); variants["extra"] = x
        x=lines[3:6]+lines[:3]+lines[6:]; variants["order"] = x
        x=lines.copy(); x[1]=node.replace("byteIdx", "position"); variants["schema"] = x
        x=lines.copy(); x[1]=node.replace(":= 1", ":= 99999999"); variants["span"] = x
        expected=syntax.summary(baseline)
        for label, value in variants.items():
            with self.subTest(label=label):
                try: actual = syntax.summary(syntax.parse_log("\n".join(value)))
                except ValueError: continue
                self.assertNotEqual(actual, expected)

if __name__ == "__main__": unittest.main()
