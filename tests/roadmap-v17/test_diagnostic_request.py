import copy
import gzip
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
import tarfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("diagnostic_request",ROOT/"scripts/roadmap-v17-diagnostic-request.py")
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)


def wire(files,head):
    data=io.BytesIO()
    with tarfile.open(fileobj=data,mode="w",format=tarfile.USTAR_FORMAT) as t:
        for path,body in files.items():
            item=tarfile.TarInfo(path);item.size=len(body);t.addfile(item,io.BytesIO(body))
    packet=gzip.compress(data.getvalue())
    return packet,{"schema":1,"producerHead":head,"packetSha256":hashlib.sha256(packet).hexdigest(),
                   "members":{p:hashlib.sha256(b).hexdigest() for p,b in files.items()}}


@unittest.skipUnless(os.environ.get("V17_REVIEWED_INBOX"),"reviewed external inputs not supplied")
class ReviewedRequests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inbox=Path(os.environ["V17_REVIEWED_INBOX"]);cls.receipts=Path(os.environ["V17_REVIEWED_RECEIPTS"])
        de=json.loads((cls.receipts/"dependencies-expected.json").read_text())
        bindings=json.loads((cls.receipts/"a-bindings.json").read_text())
        cls.provider=g.x.dependency_archive((cls.inbox/"v09-exact-committed-dependencies.tar.gz").read_bytes(),de,bindings)
        cls.tools=json.loads((cls.receipts/"request-a/LOCAL-DIAGNOSTIC-REQUEST.json").read_text())["observedWorkerTools"]
        lib=Path(cls.tools["lean"]["path"]).parent.parent/"lib/lean/libInit_shared.so"
        cls.tools["installedInputs"]={"lib/lean/libInit_shared.so":hashlib.sha256(lib.read_bytes()).hexdigest()}

    def inputs(self,suffix="a"):
        return (self.inbox/("v09-draft-"+suffix+"-reviewed.tar.gz")).read_bytes(),json.loads((self.receipts/(suffix+"-expected.json")).read_text())

    def mutate(self,fn):
        raw,expected=self.inputs();_,bodies=g.p._inspect(raw,expected);fn(bodies)
        return wire(bodies,expected["producerHead"])

    def plan(self,raw,expected):return g.make_plan(raw,expected,self.provider,self.tools)

    def test_actual_reviewed_both(self):
        for suffix,count in (("a",18),("b",9)):
            plan,files=self.plan(*self.inputs(suffix))
            self.assertEqual(sum(len(q["request"]["declarations"]) for q in plan["queries"]),count)
            self.assertTrue(all(len(q["request"]["declarations"])<=16 for q in plan["queries"]))
            self.assertEqual(plan["limits"]["expressionNodes"],100000)
            self.assertEqual(plan["limits"]["expressionDepth"],512)
            self.assertEqual(plan["limits"]["componentCumulativeSeconds"],300)
            self.assertFalse(plan["kernelValidated"]);self.assertFalse(plan["releaseClosed"])
            for q in plan["queries"]:
                self.assertEqual(files[q["query"]],g.k.query_bytes(q["request"]))
                self.assertEqual(files[q["axioms"]],g.k.axiom_query(q["request"]))
            compile(files["verify-inputs.py"],"verify-inputs.py","exec")
            compile(files["collect-inputs.py"],"collect-inputs.py","exec")

    def test_missing_reviewed_pair(self):
        raw,expected=self.mutate(lambda bodies:bodies.pop("COMPLETE-SIGNATURES.json"))
        with self.assertRaisesRegex(ValueError,"metadata pair"):self.plan(raw,expected)

    def test_wrong_final_head(self):
        def change(bodies):
            m=json.loads(bodies["FINAL-MANIFEST.json"]);m["head"]="f"*40;bodies["FINAL-MANIFEST.json"]=json.dumps(m).encode()
        with self.assertRaisesRegex(ValueError,"source identity contradiction"):self.plan(*self.mutate(change))

    def test_truncated_signature_document(self):
        def change(bodies):
            m=json.loads(bodies["COMPLETE-SIGNATURES.json"]);m["candidate_signatures"][0]["signature_source"]="theorem truncated"
            bodies["COMPLETE-SIGNATURES.json"]=json.dumps(m).encode()
        with self.assertRaisesRegex(ValueError,"signature document contradiction"):self.plan(*self.mutate(change))

    def test_coherent_truncation_of_nested_record_header(self):
        def change(bodies):
            c=json.loads(bodies["COMPLETE-SIGNATURES.json"])
            row=next(row for row in c["candidate_signatures"] if ":=" in row["signature_source"])
            row["signature_source"]=row["signature_source"].split(":=",1)[0]
            f=json.loads(bodies["FINAL-MANIFEST.json"]);f["signature_inventory"]=c["candidate_signatures"]
            bodies["COMPLETE-SIGNATURES.json"]=json.dumps(c).encode();bodies["FINAL-MANIFEST.json"]=json.dumps(f).encode()
        with self.assertRaisesRegex(ValueError,"truncated nested"):self.plan(*self.mutate(change))

    def test_wrong_module_and_duplicate_names(self):
        for mode in ("module","duplicate"):
            def change(bodies):
                c=json.loads(bodies["COMPLETE-SIGNATURES.json"]);rows=c["candidate_signatures"]
                if mode=="module":rows[0]["module"]="Solidity.KeySort"
                else:rows[1]["name"]=rows[0]["name"]
                f=json.loads(bodies["FINAL-MANIFEST.json"]);f["signature_inventory"]=rows
                bodies["COMPLETE-SIGNATURES.json"]=json.dumps(c).encode();bodies["FINAL-MANIFEST.json"]=json.dumps(f).encode()
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.plan(*self.mutate(change))

    def test_wrong_tool_version(self):
        tools=copy.deepcopy(self.tools);tools["lean"]["version"]="Lean version 0"
        with self.assertRaisesRegex(ValueError,"version mismatch"):
            g.make_plan(*self.inputs(),self.provider,tools)

    def test_missing_installed_inputs(self):
        tools=copy.deepcopy(self.tools);tools["installedInputs"]={}
        with self.assertRaisesRegex(ValueError,"installed tool inputs missing"):
            g.make_plan(*self.inputs(),self.provider,tools)

    def test_missing_source_provider(self):
        provider=copy.deepcopy(self.provider);provider["bodies"]["Solidity/Backend/Passes/ReframedSequence.lean"]+=b"corrupt"
        with self.assertRaisesRegex(ValueError,"source bytes changed"):
            g.make_plan(*self.inputs(),provider,self.tools)

    def test_sidecar_missing_output_remains_nonpass(self):
        plan,files=self.plan(*self.inputs())
        directory=Path(tempfile.mkdtemp(prefix="v17-request-sidecar-"))
        here=directory/"request";here.mkdir();out=directory/"result";out.mkdir()
        raw=json.dumps(plan).encode();(here/"LOCAL-DIAGNOSTIC-REQUEST.json").write_bytes(raw)
        (here/"collect-inputs.py").write_bytes(files["collect-inputs.py"])
        result=subprocess.run([sys.executable,"-I",str(here/"collect-inputs.py"),str(ROOT),
            str(Path(self.tools["lean"]["path"]).parent),str(out),hashlib.sha256(raw).hexdigest()],
            capture_output=True,timeout=10)
        self.assertEqual(result.returncode,2)
        record=json.loads((out/"object-inputs.json").read_text())
        self.assertTrue(record["errors"]);self.assertFalse(record["kernelValidated"])

    def test_finalizer_write_failure_preserves_original_exit(self):
        _,files=self.plan(*self.inputs())
        finalizer=next(line for line in files["payload.sh"].decode().splitlines() if line.startswith("finish()"))
        for original,expected in ((0,125),(7,7)):
            # Synthetic shell cleanup only; no payload, Lean, Lake or source build runs.
            shell=finalizer+"\nOUT=/dev/null; PYTHON=/bin/true; HERE=/unused; ROOT=/unused; TOOLS=/unused; EXPECTED=x; phaseCollection=0; last_status="+str(original)+"; trap finish EXIT; exit "+str(original)
            result=subprocess.run(["sh","-c",shell],capture_output=True,timeout=10)
            self.assertEqual(result.returncode,expected)

    def test_payload_is_unexecuted_outer_scope_contract(self):
        plan,files=self.plan(*self.inputs())
        self.assertEqual(plan["status"],"REQUEST_NOT_EXECUTED")
        self.assertIn("Bare payload does not enforce",plan["executionContract"])
        self.assertIn(b'trap finish EXIT',files["payload.sh"])
        self.assertIn(b'command.exit',files["payload.sh"])
        self.assertIn(b'postflight.exit',files["payload.sh"])
        self.assertIn("outer coordinator",plan["payloadBoundary"])
        self.assertIn(b'LEAN_NUM_THREADS=1',files["payload.sh"])
        self.assertIn(b'--tstack=131072',files["payload.sh"])


if __name__=="__main__":unittest.main()
