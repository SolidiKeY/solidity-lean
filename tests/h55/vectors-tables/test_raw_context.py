import hashlib
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import raw_context as c

class RawContextTests(unittest.TestCase):
    def test_context_inventory_and_negative_controls(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); path="Solidity/Yul/RawA.lean"; source=b"theorem a : True := by\n  cases h\n"
            target=root/path; target.parent.mkdir(parents=True); target.write_bytes(source)
            start=source.index(b"cases h"); end=start+len(b"cases h")
            kind="Lean.Parser.Tactic.cases"
            node={"kind":kind,"start":start,"end":end,"source_sha256":hashlib.sha256(source[start:end]).hexdigest()}
            decl=f"DECL some {{ byteIdx := 0 }} some {{ byteIdx := {len(source)} }}"
            line=f"NODE {kind} some {{ byteIdx := {start} }} some {{ byteIdx := {end} }}"
            original=["FILE "+path,decl,line,"ENDDECL","END "+path]
            context=root/"context.log"; reference=root/"reference.log"; reference.write_text("")
            meta={"commit":"a"*40}
            with patch.object(c.master,"snapshot",return_value=(meta,[path])), patch.object(c.master,"parse",return_value={"RawA.lean":[node]}):
                context.write_text("\n".join(original)); data=c.parse(root,context,reference)
                self.assertEqual(len(data["files"]["RawA.lean"]),1)
                self.assertEqual(data["files"]["RawA.lean"][0]["nodes"],[node])
                for label,bad in [("missing",original[:2]+original[3:]),("extra",original[:3]+[line]+original[3:]),("order",[original[0],line,decl,*original[3:]]),("schema",original[:2]+[line.replace("byteIdx","offset")]+original[3:]),("span",original[:2]+[line.replace(str(end),"99999")]+original[3:])]:
                    with self.subTest(label=label):
                        context.write_text("\n".join(bad))
                        with self.assertRaises(ValueError): c.parse(root,context,reference)

if __name__ == "__main__": unittest.main()
