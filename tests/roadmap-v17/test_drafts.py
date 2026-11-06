import copy
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import tarfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("drafts",ROOT/"scripts/roadmap-v17-drafts.py")
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)


def packet(files,head="a"*40):
    out=io.BytesIO()
    with tarfile.open(fileobj=out,mode="w",format=tarfile.USTAR_FORMAT) as t:
        for path,body in files.items():
            i=tarfile.TarInfo(path);i.size=len(body);t.addfile(i,io.BytesIO(body))
    data=gzip.compress(out.getvalue())
    return data,{"schema":1,"packetSha256":hashlib.sha256(data).hexdigest(),"producerHead":head,
                 "members":{p:hashlib.sha256(b).hexdigest() for p,b in files.items()}}


class ArchiveControls(unittest.TestCase):
    def setUp(self):
        self.body=(ROOT/"Solidity/KeySort.lean").read_bytes();self.path="Solidity/KeySort.lean"
        self.raw,self.expected=packet({self.path:self.body})
        self.bindings={self.path:{"module":"Solidity.KeySort","sha256":hashlib.sha256(self.body).hexdigest(),
                                 "git_blob":x.blob(self.body),"bytes":len(self.body)}}

    def test_actual_intrinsic_bytes(self):
        provider=x.dependency_archive(self.raw,self.expected,self.bindings)
        self.assertEqual(provider["bodies"][self.path],self.body)
        self.assertFalse(provider["receipt"]["kernelValidated"])

    def test_blob_mismatch(self):
        self.bindings[self.path]["git_blob"]="0"*40
        with self.assertRaisesRegex(ValueError,"blob mismatch"):x.dependency_archive(self.raw,self.expected,self.bindings)

    def test_wrong_sha(self):
        self.bindings[self.path]["sha256"]="0"*64
        with self.assertRaisesRegex(ValueError,"SHA mismatch"):x.dependency_archive(self.raw,self.expected,self.bindings)

    def test_partial_archive(self):
        self.bindings["Solidity/Missing.lean"]={}
        with self.assertRaisesRegex(ValueError,"incomplete/extra"):x.dependency_archive(self.raw,self.expected,self.bindings)

    def test_wrong_module_size_head(self):
        for key,value in (("module","Solidity.Other"),("bytes",True),("bytes",0),("producer_head","b"*40)):
            b=copy.deepcopy(self.bindings);b[self.path][key]=value
            with self.subTest(key=key,value=value),self.assertRaises(ValueError):x.dependency_archive(self.raw,self.expected,b)

    def test_local_dependency_size_contradiction(self):
        self.bindings[self.path]["bytes"]=0
        with self.assertRaisesRegex(ValueError,"availability size mismatch"):
            x.availability(self.bindings,[ROOT],[])

    def test_availability_stops_before_unused_directory(self):
        # An exact archive match means no local descriptor is opened at all.
        provider=x.dependency_archive(self.raw,self.expected,self.bindings)
        with unittest.mock.patch.object(x.p,"stable_read",side_effect=AssertionError("unused local read")):
            rows=x.availability(self.bindings,[ROOT],[provider])
        self.assertEqual(rows[0]["status"],"byte-match-only")

    def test_forged_proof_receipt(self):
        provider=x.dependency_archive(self.raw,self.expected,self.bindings)
        provider["receipt"]["kernelValidated"]=True
        request={"schema":1,"producerHead":"a"*40,"producerBase":"b"*40,
                 "packetSha256":self.expected["packetSha256"],"roots":["Solidity.KeySort"],
                 "sources":{self.path:self.bindings[self.path]["sha256"]}}
        with self.assertRaisesRegex(ValueError,"proof promotion"):
            x.d.reconcile(self.raw,self.expected,request,[ROOT],[provider])

    def test_aggregate_bounds(self):
        provider=x.dependency_archive(self.raw,self.expected,self.bindings)
        request={"schema":1,"producerHead":"a"*40,"producerBase":"b"*40,
                 "packetSha256":self.expected["packetSha256"],"roots":["Solidity.KeySort"],
                 "sources":{self.path:self.bindings[self.path]["sha256"]}}
        for field,limit in (("rawBytes",x.p.RAW),("compressedBytes",x.p.COMPRESSED)):
            bad=copy.deepcopy(provider);bad["receipt"][field]=limit
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,"aggregate"):
                x.d.reconcile(self.raw,self.expected,request,[ROOT],[bad])


@unittest.skipUnless(os.environ.get("V17_DRAFT_INBOX"),"external draft inbox not supplied")
class ActualDrafts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inbox=Path(os.environ["V17_DRAFT_INBOX"])
        cls.work=Path(os.environ["V17_DRAFT_RECEIPTS"])
        expected=json.loads((cls.work/"dependency-archive-expected.json").read_text())
        bindings=json.loads((cls.work/"v11-bindings.json").read_text())
        cls.provider=x.dependency_archive((cls.inbox/"v11-exact-committed-dependencies.tar.gz").read_bytes(),expected,bindings)

    def inputs(self,family):
        name={"v09":"v09-compiler-passes-UNVALIDATED.tar.gz","v11":"v11-memory-operations-UNVALIDATED.tar.gz"}[family]
        return (self.inbox/name).read_bytes(),json.loads((self.work/(family+"-expected.json")).read_text())

    def test_all245_exact_dependency_blobs(self):
        self.assertEqual(len([p for p in self.provider["bodies"] if p.endswith(".lean")]),245)

    def test_v11_source_closure_not_kernel(self):
        raw,expected=self.inputs("v11");r=x.reconcile(raw,expected,"v11",[ROOT],[self.provider])
        self.assertEqual(r["status"],"lexical-source-match-only");self.assertEqual(len(r["modules"]),248)
        self.assertEqual(r["issues"],[])
        self.assertFalse(r["kernelValidated"]);self.assertFalse(r["replayValidated"])
        failed=json.loads((self.inbox/"local-check-result.json").read_text())
        self.assertEqual(failed["draftArchiveSha256"],expected["packetSha256"])
        self.assertEqual(failed["exitCode"],1)

    def test_v09_exact_missing_requests(self):
        raw,expected=self.inputs("v09");r=x.reconcile(raw,expected,"v09",[ROOT],[self.provider])
        self.assertEqual(r["status"],"NONPASS");self.assertEqual(len(r["allListedMissingSourceRequests"]),26)
        self.assertEqual(len(r["exactMissingSourceRequests"]),3)
        for row in r["allListedMissingSourceRequests"]:
            self.assertEqual(row["producerHead"],expected["producerHead"])
            self.assertEqual(len(row["sha256"]),64);self.assertEqual(len(row["gitBlob"]),40)

    def test_actual_wrong_producer(self):
        raw,expected=self.inputs("v09");expected["producerHead"]="c"*40
        with self.assertRaisesRegex(ValueError,"draft producer mismatch"):x.draft_request(raw,expected,"v09")

    def test_actual_promoted_manifest(self):
        raw,expected=self.inputs("v09")
        _,bodies=x.p._inspect(raw,expected)
        info=json.loads(bodies["MANIFEST.json"]);info["kernelValidated"]=True
        bodies["MANIFEST.json"]=json.dumps(info).encode()
        mutated,pinned=packet(bodies,expected["producerHead"])
        with self.assertRaisesRegex(ValueError,"proof promotion"):
            x.draft_request(mutated,pinned,"v09")

    def test_actual_claim_document_links(self):
        raw,expected=self.inputs("v09");_,_,claims=x.draft_request(raw,expected,"v09")
        self.assertEqual(claims["authenticatedClaimDocuments"]["MANIFEST.json"]["memberSha256"],expected["members"]["MANIFEST.json"])
        self.assertEqual(len(claims["fullSourceSignatureMembers"]),3)

    def test_actual_corrupt_dependency(self):
        bad=copy.deepcopy(self.provider);path="Solidity/KeySort.lean";bad["bodies"][path]+=b"corrupt"
        raw,expected=self.inputs("v11")
        with self.assertRaisesRegex(ValueError,"source bytes changed"):
            x.reconcile(raw,expected,"v11",[ROOT],[bad])

    def test_actual_partial_dependency_manifest(self):
        expected=json.loads((self.work/"dependency-archive-expected.json").read_text())
        bindings=json.loads((self.work/"v11-bindings.json").read_text());bindings.pop(next(iter(bindings)))
        with self.assertRaisesRegex(ValueError,"incomplete/extra"):
            x.dependency_archive((self.inbox/"v11-exact-committed-dependencies.tar.gz").read_bytes(),expected,bindings)


if __name__=="__main__":unittest.main()
