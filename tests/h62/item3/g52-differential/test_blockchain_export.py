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
if __name__=="__main__":unittest.main()
