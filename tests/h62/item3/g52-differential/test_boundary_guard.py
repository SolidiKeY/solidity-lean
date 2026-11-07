"""Guarded regression: a resource-stopped witness emitter exiting zero must not save a success receipt. Synthetic control; no Lean execution."""
import contextlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
P=Path(__file__).resolve().parents[4]/"scripts/h62/item3/g52-differential/serial_semantics.py"
spec=importlib.util.spec_from_file_location("serial_boundary",P);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Guard(unittest.TestCase):
 def test_stopped_zero_exit_rejected(self):
  with tempfile.TemporaryDirectory() as directory:
   root=Path(directory);repo=root/"repo";repo.mkdir();bulk=root/"bulk";logs=bulk/"evidence/lean";logs.mkdir(parents=True)
   (logs/"results.json").write_text(json.dumps({"complete":True,"modules":[{"exit":0,"stopped":None}]}))
   (bulk/"evidence/producer-sources.json").write_text(json.dumps({"source_sha256":{}}))
   args=["runner","--boundary-only","--repo",str(repo),"--bulk",str(bulk),"--lean-bin",str(root/"bin")]
   with patch("sys.argv",args),patch.object(m.subprocess,"check_output",return_value="Lean version 4.24.0"),patch.object(m,"run",return_value={"exit":0,"stopped":"resource/time guard"}),contextlib.redirect_stdout(io.StringIO()):
    with self.assertRaises(SystemExit) as raised:m.main()
   self.assertEqual(raised.exception.code,1);self.assertFalse((bulk/"evidence/boundary-generator.json").exists())
if __name__=="__main__":unittest.main()
