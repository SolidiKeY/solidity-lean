"""Guard saved source-binding promotion, mode confusion and receipt substitution."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4]
SCRIPT=ROOT/"scripts/h62/item1/duplication-scanner/scan.py"
spec=importlib.util.spec_from_file_location("source_scan",SCRIPT)
scan=importlib.util.module_from_spec(spec);spec.loader.exec_module(scan)
spec=importlib.util.spec_from_file_location("source_scan_binder",SCRIPT.with_name("bind_signature_fixture.py"))
binder=importlib.util.module_from_spec(spec);spec.loader.exec_module(binder)
FIXTURE="tests/h62/item1/duplication-scanner/SignatureFingerprint.lean"


class SourceScannerControls(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.directory=Path(self.temp.name)

    def invoke(self,root,pattern,*options):
        return subprocess.run([sys.executable,"-B",str(SCRIPT),str(root),pattern,*map(str,options)],capture_output=True,timeout=15)

    def test_modes_cannot_be_combined(self):
        output=self.directory/"new"
        result=self.invoke(ROOT,FIXTURE,"--source-binding-output",output,"--fixture-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"not allowed with argument",result.stderr)
        self.assertFalse(output.exists())

    def test_foreign_root_cannot_request_source_binding(self):
        result=self.invoke(self.directory,"*.lean","--source-binding-output",self.directory/"new")
        self.assertNotEqual(result.returncode,0);self.assertIn(b"real checkout",result.stderr)

    def test_selected_scope_without_pinned_source_is_rejected_before_build(self):
        output=self.directory/"new"
        result=self.invoke(ROOT,"tests/h62/item1/duplication-scanner/SignatureEnvironment.lean","--source-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"pinned source fixture",result.stderr)
        self.assertFalse(output.exists())

    def test_replayed_or_broken_symlink_output_is_rejected(self):
        output=self.directory/"old";output.mkdir();(output/"receipt.json").write_text('{"status":"pass"}')
        result=self.invoke(ROOT,FIXTURE,"--source-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"saved receipts are not accepted",result.stderr)
        broken=self.directory/"broken";broken.symlink_to("missing")
        result=self.invoke(ROOT,FIXTURE,"--source-binding-output",broken)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"saved receipts are not accepted",result.stderr)

    def test_unbound_baseline_cannot_be_compared_as_source_bound(self):
        previous=self.directory/"previous.json";unbound=self.invoke(ROOT,FIXTURE);self.assertEqual(unbound.returncode,0)
        previous.write_bytes(unbound.stdout);output=self.directory/"new"
        result=self.invoke(ROOT,FIXTURE,"--source-binding-output",output,"--previous",previous,
                           "--previous-sha256",hashlib.sha256(unbound.stdout).hexdigest())
        self.assertNotEqual(result.returncode,0);self.assertIn(b"incompatible version or selection",result.stderr)
        self.assertFalse(output.exists())

    def test_receipt_hash_is_tied_to_live_object_not_latest_sidecar(self):
        live={"status":"pass","seconds":1.25};path=self.directory/"receipt.json"
        raw=(json.dumps(live,indent=2)+"\n").encode();path.write_bytes(raw)
        self.assertEqual(scan.live_receipt_hash(binder,self.directory,live),hashlib.sha256(raw).hexdigest())
        path.write_text('{"status":"pass","seconds":0}')
        with self.assertRaisesRegex(ValueError,"receipt hash mismatch"):
            scan.live_receipt_hash(binder,self.directory,live)
        path.unlink();target=self.directory/"target";target.write_bytes(raw);path.symlink_to(target)
        with self.assertRaisesRegex(ValueError,"symlink"):
            scan.live_receipt_hash(binder,self.directory,live)


if __name__=="__main__":unittest.main()
