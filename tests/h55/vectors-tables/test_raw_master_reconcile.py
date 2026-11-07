import json
import sys
import tempfile
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import raw_master_reconcile as r

class RawMasterReconcileTests(unittest.TestCase):
    def test_snapshot_and_parser_negative_controls(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); directory=root / "Solidity/Yul"; directory.mkdir(parents=True)
            a="Solidity/Yul/RawA.lean"; b="Solidity/Yul/RawB.lean"
            (root/a).write_bytes(b"abc\n"); (root/b).write_bytes(b"xyz\n")
            meta={"commit":"a"*40,"files":{a:r.sha((root/a).read_bytes()),b:r.sha((root/b).read_bytes())}}
            (root/"SOURCE.json").write_text(json.dumps(meta))
            _,paths=r.snapshot(root, meta); self.assertEqual(paths,[a,b])
            node="NODE Lean.Parser.Tactic.case some { byteIdx := 0 } some { byteIdx := 1 }"
            lines=["FILE "+a,node,"END "+a,"FILE "+b,node,"END "+b]
            expected=r.parse("\n".join(lines),root,paths); self.assertEqual(len(expected),2)
            for label, mutated in [("missing",lines[:-1]),("extra",lines+[node]),("order",lines[3:]+lines[:3]),("schema",lines[:1]+[node.replace("byteIdx","offset")]+lines[2:]),("span",lines[:1]+[node.replace(":= 1",":= 99")]+lines[2:])]:
                with self.subTest(label=label):
                    with self.assertRaises(ValueError): r.parse("\n".join(mutated),root,paths)
            (root/a).write_bytes(b"changed")
            with self.assertRaises(ValueError): r.snapshot(root, meta)
            (root/a).write_bytes(b"abc\n"); (root/"Solidity/Yul/RawC.lean").write_text("")
            with self.assertRaises(ValueError): r.snapshot(root, meta)

if __name__ == "__main__": unittest.main()
