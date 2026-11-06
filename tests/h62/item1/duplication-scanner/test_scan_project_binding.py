"""Guard project-mode scope confusion, alias promotion and incomplete joins."""
import copy
import hashlib
import importlib.util
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4];SCRIPT=ROOT/"scripts/h62/item1/duplication-scanner/scan.py"
spec=importlib.util.spec_from_file_location("project_scan",SCRIPT);scan=importlib.util.module_from_spec(spec);spec.loader.exec_module(scan)
SOURCE="Solidity/KeySort.lean"


def inputs():
    rows=[{"path":SOURCE,"line":1,"name":"named","kind":"theorem","reject_reason":None},
          {"path":SOURCE,"line":2,"name":"<anonymous>","kind":"example","reject_reason":None},
          {"path":"tests/alias.lean","line":1,"name":"named","kind":"theorem","reject_reason":None}]
    data=[{"path":SOURCE,"sha256":"hash"}]
    linked={"source_sha256":"hash","linked":1,"rows":[dict(rows[0],status="direct-source-signature-link",declaration=["str",["anonymous"],"named"],signature=[],selection={}),dict(rows[1],status="no-direct-location-match")]}
    live={"source_sha256":"hash","linked":1}
    return rows,data,linked,live


class ProjectScannerControls(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.directory=Path(self.temp.name)

    def invoke(self,root,pattern,*options):
        return subprocess.run([sys.executable,"-B",str(SCRIPT),str(root),pattern,*map(str,options)],capture_output=True,timeout=15)

    def test_project_mode_cannot_be_combined_with_other_modes(self):
        for other in ("--source-binding-output","--fixture-binding-output"):
            output=self.directory/"new"
            result=self.invoke(ROOT,SOURCE,"--project-binding-output",output,other,output)
            self.assertNotEqual(result.returncode,0);self.assertIn(b"not allowed with argument",result.stderr)
            self.assertFalse(output.exists())

    def test_foreign_root_and_missing_project_selection_refused(self):
        output=self.directory/"new"
        result=self.invoke(self.directory,"*.lean","--project-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"real checkout",result.stderr)
        result=self.invoke(ROOT,"tests/h62/item1/duplication-scanner/SignatureFingerprint.lean","--project-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"pinned project source",result.stderr)
        self.assertFalse(output.exists())

    def test_saved_project_packet_or_symlink_output_refused(self):
        output=self.directory/"old";output.mkdir();(output/"receipt.json").write_text('{"status":"pass"}')
        result=self.invoke(ROOT,SOURCE,"--project-binding-output",output)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"saved receipts are not accepted",result.stderr)
        link=self.directory/"link";link.symlink_to("missing")
        result=self.invoke(ROOT,SOURCE,"--project-binding-output",link)
        self.assertNotEqual(result.returncode,0);self.assertIn(b"saved receipts are not accepted",result.stderr)

    def test_unbound_project_baseline_cannot_be_promoted(self):
        previous=self.directory/"old.json";raw=self.invoke(ROOT,SOURCE);self.assertEqual(raw.returncode,0);previous.write_bytes(raw.stdout)
        output=self.directory/"new"
        result=self.invoke(ROOT,SOURCE,"--project-binding-output",output,"--previous",previous,
                           "--previous-sha256",hashlib.sha256(raw.stdout).hexdigest())
        self.assertNotEqual(result.returncode,0);self.assertIn(b"incompatible version or selection",result.stderr)
        self.assertFalse(output.exists())

    def test_only_canonical_named_rows_receive_project_annotation(self):
        rows,data,linked,live=inputs();scan.attach_source_bindings(rows,data,linked,live,SOURCE,"project_signature")
        self.assertIn("project_signature",rows[0]);self.assertNotIn("project_signature",rows[1]);self.assertNotIn("project_signature",rows[2])
        self.assertFalse(any("fixture_signature" in row for row in rows))
        coverage=scan.signature_coverage(rows,"project_signature","local-project-linkage")
        self.assertEqual(coverage["counts"],{"local-project-linkage":1,"unresolved":2})
        self.assertFalse(coverage["complete_signature_coverage"])

    def test_partial_or_duplicate_coverage_refused_before_annotation(self):
        for change in (lambda rows,linked:linked["rows"].pop(),lambda rows,linked:linked["rows"].append(copy.deepcopy(linked["rows"][0])),
                       lambda rows,linked:rows.append(copy.deepcopy(rows[0]))):
            rows,data,linked,live=inputs();change(rows,linked)
            with self.assertRaisesRegex(ValueError,"coverage mismatch"):scan.attach_source_bindings(rows,data,linked,live,SOURCE,"project_signature")
            self.assertFalse(any("project_signature" in row for row in rows))

    def test_drift_or_inconsistent_link_count_refused(self):
        rows,data,linked,live=inputs();linked["source_sha256"]="changed"
        with self.assertRaisesRegex(ValueError,"source differs"):scan.attach_source_bindings(rows,data,linked,live,SOURCE,"project_signature")
        rows,data,linked,live=inputs();live["linked"]=2
        with self.assertRaisesRegex(ValueError,"linkage count mismatch"):scan.attach_source_bindings(rows,data,linked,live,SOURCE,"project_signature")

    def test_stale_annotation_not_reused(self):
        rows,data,linked,live=inputs();rows[0]["project_signature"]={"forged":True}
        with self.assertRaisesRegex(ValueError,"stale source annotation"):scan.attach_source_bindings(rows,data,linked,live,SOURCE,"project_signature")


if __name__=="__main__":unittest.main()
