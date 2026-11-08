import copy
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"scripts/h55/vectors-tables"))
import vector_generator as g
import vector_census as census

class VectorGeneratorTests(unittest.TestCase):
    def test_integer_oracle_boundaries(self):
        m=g.MOD; high=1<<255
        cases=[("div",["7","0"],0),("sdiv",[str(m-7),"3"],m-2),
               ("smod",[str(m-7),"3"],m-1),("sdiv",[str(high),str(m-1)],high),
               ("sar",["256",str(high)],m-1),("sar",["256","1"],0),
               ("shl",["256","1"],0),("byte",["31","4660"],52),
               ("byte",["32","4660"],0),("signextend",["0","128"],m-128),
               ("addmod",[str(m-1),"1","3"],1),("mulmod",[str(m-1),"2","3"],0),
               ("clz",["0"],256),("exp",["0","0"],1)]
        for op,args,expected in cases:
            with self.subTest(op=op,args=args): self.assertEqual(g.oracle(op,args),str(expected))
        for op,args in [("unknown",["1"]),("add",["1"]),("not",["-1"])]:
            with self.assertRaises(ValueError): g.oracle(op,args)
    def test_full_inventory_and_determinism(self):
        inputs=g.inputs_from_sources(); outputs=g.generate(inputs)
        self.assertEqual(sum(map(len,inputs["files"].values())),6903)
        self.assertEqual({r["op"] for rows in inputs["files"].values() for r in rows},set(g.codec.ARITY))
        for path in census.PATHS: self.assertEqual(outputs[path],(ROOT/path).read_bytes())
        self.assertEqual(outputs,g.generate(copy.deepcopy(inputs)))
    def test_file_inventory_mutations(self):
        original = g.inputs_from_sources()
        missing = copy.deepcopy(original)
        del missing["files"][census.PATHS[0]]
        extra = copy.deepcopy(original)
        extra["files"]["Solidity/Yul/Checks/Extra.lean"] = []
        reordered = copy.deepcopy(original)
        reordered["files"] = dict(reversed(list(reordered["files"].items())))
        for label, data in [("missing", missing), ("extra", extra), ("order", reordered)]:
            with self.subTest(label=label), self.assertRaises(ValueError):
                g.generate(data)

    def test_inventory_and_schema_mutations(self):
        original=g.inputs_from_sources(); expected=g.generate(original)
        variants={}
        x=copy.deepcopy(original); x["files"][census.PATHS[0]].pop(0); variants["missing"]=x
        x=copy.deepcopy(original); x["files"][census.PATHS[0]].append(copy.deepcopy(x["files"][census.PATHS[0]][0])); variants["extra"]=x
        x=copy.deepcopy(original); x["files"][census.PATHS[0]][:2]=reversed(x["files"][census.PATHS[0]][:2]); variants["order"]=x
        x=copy.deepcopy(original); x["files"][census.PATHS[0]][0]["result"]="0"; variants["schema"]=x
        x=copy.deepcopy(original); x["files"][census.PATHS[0]][0]["args"][1]="7"; variants["operand"]=x
        for label,data in variants.items():
            with self.subTest(label=label):
                try: actual=g.generate(data)
                except ValueError: continue
                self.assertNotEqual(actual,expected)

if __name__=="__main__": unittest.main()
