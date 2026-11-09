"""Guarded regression: wrong format/fork or partial publication cannot be accepted as execution conformance."""
import importlib.util
import sys
import unittest
import tempfile
import tarfile
import io
import json
import gzip
from unittest.mock import patch
from pathlib import Path
S=Path(__file__).resolve().parents[4]/"scripts/h62/item3/g52-differential";sys.path.insert(0,str(S));spec=importlib.util.spec_from_file_location("exporter",S/"eest_export.py");m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Export(unittest.TestCase):
 def test_exact_input_identity_and_no_pass(self):
  row={"path":"p","case":"c"};fixture={"network":"Osaka","_info":{"fixture-format":"blockchain_test"},"blocks":[]};out=m.blockchain_record(2,row,fixture,"digest")
  self.assertEqual(out["index"],2);self.assertEqual(out["fixture"],fixture);self.assertEqual(out["status"],"input-only-not-executed")
 def test_wrong_fork_and_format_rejected(self):
  for fork,fmt in [("Prague","blockchain_test"),("PragueToOsakaAtTime15k","blockchain_test"),("Osaka","blockchain_test_engine")]:
   with self.assertRaises(ValueError):m.blockchain_record(0,{"path":"p","case":"c"},{"network":fork,"_info":{"fixture-format":fmt}},"digest")
 def test_failed_export_preserves_completed_stream_and_receipt(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory);(root/"upstream").mkdir();(root/"evidence").mkdir()
   archive=root/"upstream/fixtures_develop-v5.3.0.tar.gz";name="fixtures/blockchain_tests/f.json"
   payload=json.dumps({"case":{"network":"Prague","_info":{"fixture-format":"blockchain_test"}}}).encode()
   with tarfile.open(archive,"w:gz") as tar:
    member=tarfile.TarInfo(name);member.size=len(payload);tar.addfile(member,io.BytesIO(payload))
   inventory=root/"archive-inventory.jsonl.gz"
   with gzip.open(inventory,"wt") as f:f.write(json.dumps({"path":name,"case":"case","role":"fixture","format":"blockchain_test","selection":"exact-osaka","variants":1})+"\n")
   real_sha=m.file_sha
   (root/"evidence/archive-census.json").write_text(json.dumps({"archive_sha256":m.EEST_SHA,"inventory_sha256":real_sha(inventory)}))
   output=root/"blockchain-inputs.jsonl.gz";output.write_bytes(b"prior completed stream")
   receipt=root/"evidence/blockchain-export.json";receipt.write_text("prior receipt")
   with patch.object(m,"file_sha",side_effect=lambda p:m.EEST_SHA if p==archive else real_sha(p)):
    with self.assertRaisesRegex(ValueError,"format/fork"):m.export(root,"blockchain_test")
   self.assertEqual(output.read_bytes(),b"prior completed stream");self.assertEqual(receipt.read_text(),"prior receipt")
class Allocations(unittest.TestCase):
 def binding(self):
  import hashlib
  group={"network":"Osaka","testIds":["case"],"pre":{},"environment":{},"genesis":{}}
  raw=(json.dumps({"path":"group","source_sha256":"archive-sha","allocation":group},sort_keys=True)+"\n").encode()
  ref={"path":"group","source_sha256":"archive-sha","offset":0,"length":len(raw),"record_sha256":hashlib.sha256(raw).hexdigest()}
  return raw,{"pre":ref}
 def test_each_nonstate_format_is_preserved_and_not_executed(self):
  for kind in m.FORMATS:
   if kind in ("state_test","transaction_test"):continue
   fixture={"network":"Osaka","_info":{"fixture-format":kind},"payload":"preserved"}
   self.assertEqual(m.blockchain_record(0,{"path":"p","case":"c"},fixture,"sha",kind)["fixture"],fixture)
   self.assertEqual(m.blockchain_record(0,{"path":"p","case":"c"},fixture,"sha",kind)["status"],"input-only-not-executed")
   for fork in ["Prague","PragueToOsakaAtTime15k","OsakaToBPO1AtTime15k"]:
    with self.assertRaisesRegex(ValueError,"format/fork"):m.blockchain_record(0,{"path":"p","case":"c"},{**fixture,"network":fork},"sha",kind)
 def test_valid_allocation_ref_retains_exact_provenance(self):
  raw,groups=self.binding();ref=m.allocation_reference({"preHash":"pre","network":"Osaka"},"case",groups,io.BytesIO(raw))
  self.assertEqual(ref["stream"],"engine-x-allocations.jsonl");self.assertEqual(ref["pre_hash"],"pre");self.assertEqual(ref["source_sha256"],"archive-sha")
 def test_missing_pre_hash_and_wrong_membership_refuse(self):
  raw,groups=self.binding()
  with self.assertRaisesRegex(ValueError,"missing"):m.allocation_reference({"network":"Osaka"},"case",groups,io.BytesIO(raw))
  for fork,case in [("Prague","case"),("Osaka","unlisted")]:
   with self.assertRaisesRegex(ValueError,"membership"):m.allocation_reference({"preHash":"pre","network":fork},case,groups,io.BytesIO(raw))
 def test_tampered_bytes_offset_and_index_provenance_refuse(self):
  raw,groups=self.binding();fixture={"preHash":"pre","network":"Osaka"}
  for data,changes in [(raw+b"extra",{"length":len(raw)+5}),(raw,{"offset":1}),(raw,{"source_sha256":"different"}),(raw,{"path":"different"})]:
   with self.assertRaises(ValueError):m.allocation_reference(fixture,"case",{"pre":{**groups["pre"],**changes}},io.BytesIO(data))
 def test_bad_engine_x_membership_preserves_all_published_artifacts(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory);(root/"upstream").mkdir();(root/"evidence").mkdir();archive=root/"upstream/fixtures_develop-v5.3.0.tar.gz"
   name="fixtures/blockchain_tests_engine_x/f.json";group_name="fixtures/blockchain_tests_engine_x/pre_alloc/key.json"
   group={"network":"Osaka","testIds":["different"],"testCount":1,"pre":{},"preAccountCount":0,"environment":{},"genesis":{}}
   fixture={"case":{"network":"Osaka","_info":{"fixture-format":"blockchain_test_engine_x"},"preHash":"key"}}
   with tarfile.open(archive,"w:gz") as tar:
    for path,data in [(group_name,group),(name,fixture)]:
     payload=json.dumps(data).encode();member=tarfile.TarInfo(path);member.size=len(payload);tar.addfile(member,io.BytesIO(payload))
   inventory=root/"archive-inventory.jsonl.gz"
   with gzip.open(inventory,"wt") as stream:stream.write(json.dumps({"path":name,"case":"case","role":"fixture","format":"blockchain_test_engine_x","selection":"exact-osaka","variants":1})+"\n")
   real_sha=m.file_sha;(root/"evidence/archive-census.json").write_text(json.dumps({"archive_sha256":m.EEST_SHA,"inventory_sha256":real_sha(inventory)}))
   published=[root/"engine-x-inputs.jsonl.gz",root/"engine-x-allocations.jsonl",root/"engine-x-allocations-index.json",root/"evidence/engine-x-export.json"]
   for path in published:path.write_bytes(b"prior completed artifact")
   with patch.object(m,"file_sha",side_effect=lambda path:m.EEST_SHA if path==archive else real_sha(path)):
    with self.assertRaisesRegex(ValueError,"membership"):m.export(root,"blockchain_test_engine_x")
   for path in published:self.assertEqual(path.read_bytes(),b"prior completed artifact")

class Transactions(unittest.TestCase):
 def test_selects_only_actual_osaka_expectation_without_execution(self):
  f={"_info":{"fixture-format":"transaction_test"},"txbytes":"0x04","result":{"Osaka":{"exception":"x"},"Prague":{"exception":"different"}}}
  r=m.transaction_record(3,{"path":"p","case":"c"},f,"sha")
  self.assertEqual(r["expected"],{"exception":"x"});self.assertEqual(r["fixture"],f);self.assertEqual(r["selected_fork"],"Osaka");self.assertEqual(r["status"],"input-only-not-executed")
 def test_missing_fork_or_wrong_format_cannot_supply_an_expectation(self):
  for fmt,result in [("state_test",{"Osaka":{}}),("transaction_test",{"Prague":{}}),("transaction_test",{"OsakaToBPO1AtTime15k":{}}),("transaction_test",{"Osaka":None})]:
   with self.assertRaisesRegex(ValueError,"format/fork"):m.transaction_record(0,{"path":"p","case":"c"},{"_info":{"fixture-format":fmt},"txbytes":"0x04","result":result},"sha")

if __name__=="__main__":unittest.main()
