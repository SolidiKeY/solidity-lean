#!/usr/bin/env python3
import copy,importlib.util,unittest,tempfile
from pathlib import Path
p=Path(__file__).with_name("roadmap-v15-memory-publication.py")
spec=importlib.util.spec_from_file_location("v15_memory",p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class PublicationControls(unittest.TestCase):
 def setUp(self):
  self.sources=m.published_sources();self.consumer=(m.ROOT/"Bridge/SolidityBridge/RoadmapV15/ReferenceEncoding.lean").read_text()
  self.report=m.classify_sources(self.sources,self.consumer)
 def test_actual_sources_and_open_report(self):m.verify_blobs(self.sources);m.validate_report(self.report)
 def test_published_blob_drift(self):
  self.sources["MemoryBytes"]+="\n"
  with self.assertRaises(ValueError):m.verify_blobs(self.sources)
 def test_missing_module(self):
  del self.sources["MemoryComposition"]
  with self.assertRaises(ValueError):m.verify_blobs(self.sources)
 def test_pure_encoding_cannot_gain_padding_hypothesis(self):
  self.sources["MemoryBytes"]=self.sources["MemoryBytes"].replace("theorem encoding_spec (v", "theorem encoding_spec (hp : PaddingCorrect 32) (v",1)
  with self.assertRaises(ValueError):m.classify_sources(self.sources,self.consumer)
 def test_serialize_cannot_lose_padding_hypothesis(self):
  self.sources["MemoryBytes"]=self.sources["MemoryBytes"].replace("theorem serialize_eq (bound : Nat) (hp : PaddingCorrect bound)","theorem serialize_eq (bound : Nat)",1)
  with self.assertRaises(ValueError):m.classify_sources(self.sources,self.consumer)
 def test_zero_allocator_equation_cannot_be_omitted(self):
  self.sources["MemoryBytes"]=self.sources["MemoryBytes"].replace("(hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)","(hz : True)",1)
  with self.assertRaises(ValueError):m.classify_sources(self.sources,self.consumer)
 def test_representation_cannot_lose_numeric_capacity(self):
  self.sources["MemoryRefinement"]=self.sources["MemoryRefinement"].replace("physical : s.memory.size = 32 * cells","physical : True",1)
  with self.assertRaises(ValueError):m.classify_sources(self.sources,self.consumer)
 def test_runner_scope_drift(self):
  self.sources["Memory"]=self.sources["Memory"].replace("EvmYul.EVM.step 1 0 (some op)","EvmYul.EVM.step 1 1 (some op)",1)
  with self.assertRaises(ValueError):m.classify_sources(self.sources,self.consumer)
 def test_full_bytes_cannot_be_weakened(self):
  self.consumer=self.consumer.replace("(encoding v).toList = (toBytesBE 32 v.toNat).toList","ofBytesBE (encoding v).toList = v.toNat",1)
  with self.assertRaises(ValueError):m.classify_sources(self.sources,self.consumer)
 def test_no_source_only_kernel_pass(self):
  self.report["consumers"][0]["localKernel"]="pass"
  with self.assertRaises(ValueError):m.validate_report(self.report)
 def test_no_allocator_witness_invention(self):
  self.report["allocatorWitness"]="assumed"
  with self.assertRaises(ValueError):m.validate_report(self.report)
 def test_no_driver_or_osaka_parent_closure(self):
  for field in ["driverDischarged","osakaDischarged","transactionDischarged"]:
   report=copy.deepcopy(self.report);report[field]=True
   with self.assertRaises(ValueError):m.validate_report(report)
 def test_missing_or_duplicate_conditional_clause(self):
  for rows in [self.report["conditionalResults"][:-1],self.report["conditionalResults"]+[self.report["conditionalResults"][0]]]:
   report=copy.deepcopy(self.report);report["conditionalResults"]=rows
   with self.assertRaises(ValueError):m.validate_report(report)
 def test_empty_allocator_clause(self):
  self.report["conditionalResults"][0]["allocatorClause"]=""
  with self.assertRaises(ValueError):m.validate_report(self.report)
 def test_wrong_allocator_clause(self):
  self.report["conditionalResults"][0]["allocatorClause"]="True"
  with self.assertRaises(ValueError):m.validate_report(self.report)
 def test_missing_or_duplicate_consumer(self):
  for rows in [self.report["consumers"][:-1],self.report["consumers"]+[self.report["consumers"][0]]]:
   report=copy.deepcopy(self.report);report["consumers"]=rows
   with self.assertRaises(ValueError):m.validate_report(report)
 def test_capacity_bound_cannot_be_weakened(self):
  self.sources["Memory"]=self.sources["Memory"].replace("32 * cells < 2 ^ 64","True",1)
  with self.assertRaises(ValueError):m.classify_sources(self.sources,self.consumer)
 def test_loader_preserves_crlf_blob_drift(self):
  with tempfile.TemporaryDirectory(prefix="v15-published-byte-control-") as temporary:
   root=Path(temporary);directory=root/"Bridge/SolidityBridge/ExternalEvm";directory.mkdir(parents=True)
   for name,text in self.sources.items():
    raw=text.encode("utf-8")
    if name=="MemoryBytes":raw=raw.replace(b"\n",b"\r\n")
    (directory/(name+".lean")).write_bytes(raw)
   loaded=m.published_sources(root)
   self.assertIn("\r\n",loaded["MemoryBytes"])
   with self.assertRaises(ValueError):m.verify_blobs(loaded)
if __name__=="__main__":unittest.main()
