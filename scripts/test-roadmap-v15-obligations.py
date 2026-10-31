#!/usr/bin/env python3
"""Mutation controls for accounting completeness/integrity, not EVM tests."""
import copy
import importlib.util
from pathlib import Path
import unittest

def load(name):
    spec=importlib.util.spec_from_file_location(name, Path(__file__).with_name(name+".py"))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
m=load("roadmap-v15-obligations"); d=load("roadmap-v15-doc-findings")

def log(lines):
    n=sum(line.startswith("missing:") for line in lines.splitlines())
    return lines + (f"FAIL: {n} reference(s) name a file that does not exist.\nEXIT: 1\n" if n else
                    "OK: every backticked *.lean reference resolves.\nEXIT: 0\n")

class Accounting(unittest.TestCase):
    def setUp(self):
        self.ops=m.canonical_opcodes((m.ROOT/"Solidity/Backend/Opcode.lean").read_text())
        self.rows=m.build_rows(self.ops)
    def row(self,name): return next(r for r in self.rows if r["opcode"]==name)
    def test_original(self):
        m.validate_rows(self.rows,self.ops)
        self.assertEqual(len(self.rows),150)
        self.assertEqual(self.row("CLZ")["byte"],"0x1e")
        self.assertEqual(self.row("PUSH32")["byte"],"0x7f")
    def test_missing(self):
        self.rows.pop();self.assertRaises(ValueError,m.validate_rows,self.rows,self.ops)
    def test_duplicate(self):
        self.rows[-1]=copy.deepcopy(self.rows[0]);self.assertRaises(ValueError,m.validate_rows,self.rows,self.ops)
    def test_wrong_bytes_without_duplicate(self):
        self.row("ADD")["byte"],self.row("MUL")["byte"]="0x02","0x01"
        self.assertRaises(ValueError,m.validate_rows,self.rows,self.ops)
    def test_omitted_secondary(self):
        for name,clause in [("RETURN","return-range"),("REVERT","memory-read"),
             ("EXTCODECOPY","code-source"),("RETURNDATACOPY","returndata-source"),
             ("CALL","call-calldata"),("STATICCALL","call-returndata"),
             ("DELEGATECALL","rollback"),("CALLCODE","call-resources"),
             ("CREATE2","create-hash"),("KECCAK256","hash-bytes")]:
            with self.subTest(name=name,clause=clause):
                rows=copy.deepcopy(self.rows);row=next(r for r in rows if r["opcode"]==name)
                row["obligations"]=[c for c in row["obligations"] if c["id"]!=clause]
                self.assertRaises(ValueError,m.validate_rows,rows,self.ops)
    def test_secondary_combinations(self):
        for name in ["CALL","CALLCODE","DELEGATECALL","STATICCALL"]:
            ids={c["id"] for c in self.row(name)["obligations"]}
            self.assertTrue({"memory-read","memory-write","memory-expansion","call-calldata",
                "call-returndata","account","rollback","precompile","stack","resources",
                "call-resources","static-permission","session"} <= ids)
        for name in ["EXTCODECOPY","RETURNDATACOPY"]:
            self.assertIn("memory-write",{c["id"] for c in self.row(name)["obligations"]})
    def test_discharge_rejected(self):
        self.row("CALL")["v15Status"]="done";self.assertRaises(ValueError,m.validate_rows,self.rows,self.ops)
    def test_duplicate_clause(self):
        self.row("RETURN")["obligations"].append(self.row("RETURN")["obligations"][0])
        self.assertRaises(ValueError,m.validate_rows,self.rows,self.ops)
    def test_doc_ambiguity_regression(self):
        result=d.compare(log("missing: old\nambiguous: old\n"), log("missing: old\nambiguous: old\nambiguous: new\n"))
        self.assertEqual(result["added"],{"ambiguous: new":1})
    def test_doc_multiplicity_and_removal(self):
        self.assertEqual(d.compare(log("missing: x\n"), log("missing: x\nmissing: x\n"))["added"],{"missing: x":1})
        self.assertEqual(d.compare(log("ambiguous: x\n"), log(""))["removed"],{"ambiguous: x":1})
    def test_family_source_drift(self):
        source=(m.ROOT/"Solidity/Backend/Opcode.lean").read_text()
        for old,new in [("DUP (n : Fin 16)","DUP (n : Fin 15)"),
                        ("0x80 + n.val","0x81 + n.val"),
                        ("SWAP (n : Fin 16)","SWAP (n : Fin 17)"),
                        ("LOG (n : Fin 5)","LOG (n : Fin 4)"),
                        ("0x5f + n.val","0x60 + n.val")]:
            with self.subTest(old=old):
                self.assertIn(old,source)
                self.assertRaises(ValueError,m.canonical_opcodes,source.replace(old,new))
    def test_incomplete_doc_logs(self):
        for bad in ["", "fatal: cannot read checkout\nEXIT: 1\n",
                    "missing: x\n", "missing: x\nFAIL: 2 reference(s) name a file that does not exist.\nEXIT: 1\n"]:
            self.assertRaises(ValueError,d.compare,log("missing: x\n"),bad)
            self.assertRaises(ValueError,d.compare,bad,log("missing: x\n"))
if __name__=="__main__": unittest.main()
