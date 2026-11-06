import copy
import gzip
import hashlib
import importlib.util
import io
import os
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("packet_dependencies", ROOT/"scripts/roadmap-v17-packet-dependencies.py")
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
sha=lambda b:hashlib.sha256(b).hexdigest()


def fixture(body=b"import Solidity.KeySort\n", deps=None):
    path="Solidity/Roadmap/V17/Client.lean"
    raw=io.BytesIO()
    with tarfile.open(fileobj=raw,mode="w",format=tarfile.USTAR_FORMAT) as t:
        info=tarfile.TarInfo(path);info.size=len(body);t.addfile(info,io.BytesIO(body))
    packet=gzip.compress(raw.getvalue())
    expected={"schema":1,"packetSha256":sha(packet),"producerHead":"a"*40,"members":{path:sha(body)}}
    request={"schema":1,"packetSha256":sha(packet),"producerHead":"a"*40,"producerBase":"b"*40,
             "roots":["Solidity.Roadmap.V17.Client"],"sources":{path:sha(body),**(deps or {})}}
    return packet,expected,request


class Dependencies(unittest.TestCase):
    def test_actual_intrinsic_source_positive(self):
        path="Solidity/KeySort.lean"; actual=(ROOT/path).read_bytes()
        a,b,c=fixture(deps={path:sha(actual)})
        result=d.reconcile(a,b,c,[ROOT])
        self.assertEqual(result["status"],"lexical-source-match-only")
        self.assertEqual(result["modules"]["Solidity.KeySort"]["sha256"],sha(actual))
        for flag in ("anchorValidated","kernelValidated","replayValidated","semanticPremisesDischarged","releaseClosed"):
            self.assertIs(result[flag],False)

    def test_missing_required_hash(self):
        a,b,c=fixture();result=d.reconcile(a,b,c,[ROOT])
        self.assertEqual(result["status"],"NONPASS")
        self.assertEqual(result["issues"][0]["status"],"missing-required-hash")
        self.assertNotIn("expectedSha256",result["issues"][0])

    def test_wrong_source_hash(self):
        a,b,c=fixture(deps={"Solidity/KeySort.lean":"0"*64})
        result=d.reconcile(a,b,c,[ROOT])
        self.assertEqual(result["issues"][0]["status"],"hash-mismatch")
        self.assertEqual(result["issues"][0]["expectedSha256"],"0"*64)

    def test_actual_missing_dependency(self):
        a,b,c=fixture(body=b"import Solidity.MissingDependency\n",deps={"Solidity/MissingDependency.lean":"0"*64})
        result=d.reconcile(a,b,c,[ROOT])
        self.assertEqual(result["issues"][0]["status"],"missing")

    def test_wrong_revision_or_packet_link(self):
        for field,value in (("producerHead","c"*40),("packetSha256","0"*64)):
            a,b,c=fixture();c[field]=value
            with self.assertRaisesRegex(ValueError,"request linkage"):d.reconcile(a,b,c,[ROOT])

    def test_packet_hash_contradiction(self):
        a,b,c=fixture();c["sources"][next(iter(b["members"]))]="0"*64
        self.assertEqual(d.reconcile(a,b,c,[ROOT])["issues"][0]["status"],"packet-source-mismatch")

    def test_cycle(self):
        a,b,c=fixture(body=b"import Solidity.Roadmap.V17.Client\n")
        with self.assertRaisesRegex(ValueError,"circular"):d.reconcile(a,b,c,[ROOT])

    def test_unreached_metadata(self):
        a,b,c=fixture(body=b"",deps={"Solidity/Unused.lean":"0"*64})
        self.assertEqual(d.reconcile(a,b,c,[ROOT])["issues"][0]["status"],"unreached-source-metadata")

    def test_source_receipt_is_not_replay_request(self):
        a,b,c=fixture()
        for bad in (d.p.inspect(a,b),dict(c,replayValidated=True),dict(c,kernelValidated=True)):
            with self.assertRaisesRegex(ValueError,"request shape"):d.reconcile(a,b,bad,[ROOT])

    def test_unsupported_header_and_bridge(self):
        for body in (b"import Solidity.KeySort Solidity.Syntax\n",b"public import Solidity.KeySort\n",
                     b"import SolidityBridge.RoadmapV15.PrefixTransport\n"):
            a,b,c=fixture(body)
            with self.assertRaises(ValueError):d.reconcile(a,b,c,[ROOT])

    def test_toolchain_explicitly_pending(self):
        a,b,c=fixture(b"import Lean\n")
        result=d.reconcile(a,b,c,[ROOT])
        self.assertEqual(result["toolchainImportsPendingBinding"],["Lean"])
        self.assertFalse(result["kernelValidated"])

    def test_dependency_changes_during_read(self):
        data=(ROOT/"Solidity/KeySort.lean").read_bytes()
        a,b,c=fixture(deps={"Solidity/KeySort.lean":sha(data)})
        with patch.object(d.p,"stable_read",side_effect=[data,data+b"changed"]):
            with self.assertRaisesRegex(ValueError,"changed during"):d.reconcile(a,b,c,[ROOT])

    def test_edge_limit(self):
        a,b,c=fixture(b"-- source\n")
        with patch.object(d,"imports",return_value=["Solidity.KeySort"]*16385):
            with self.assertRaisesRegex(ValueError,"edge bound"):d.reconcile(a,b,c,[ROOT])

    def test_symlinked_dependency(self):
        data=(ROOT/"Solidity/KeySort.lean").read_bytes()
        a,b,c=fixture(deps={"Solidity/KeySort.lean":sha(data)})
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/"Solidity").mkdir();(root/"Solidity/KeySort.lean").symlink_to(ROOT/"Solidity/KeySort.lean")
            with self.assertRaisesRegex(ValueError,"symlinked dependency"):d.reconcile(a,b,c,[root])


@unittest.skipUnless(os.environ.get("V17_REFERENCE_PACKET"), "external exact packet not supplied")
class ActualReference(unittest.TestCase):
    def setUp(self):
        directory=Path(os.environ["V17_REFERENCE_PACKET"])
        self.packet=(directory/"committed-interface.tar.gz").read_bytes()
        self.expected=json.loads((directory/"expected.json").read_text())
        self.request=d.interface_request(self.packet,self.expected)

    def test_actual_missing_dependencies(self):
        result=d.reconcile(self.packet,self.expected,self.request,[ROOT])
        missing={x["path"]:x["expectedSha256"] for x in result["issues"] if x["status"]=="missing"}
        self.assertEqual(missing,{
            "Solidity/Backend/MemoryOps/IntervalOverwrite.lean":"ce9bfeadd1f2118f90b085e32383ef75693f2dccc9b30645af1dfd7be5353da1",
            "Solidity/Backend/MemoryOps/SourceUintFixedDeclareAliasControls.lean":"f68c91f4512a884095b582fc5a526a2799ac632d240f4b84bff998d1b2985425",
            "Solidity/Backend/MemoryOps/SourceUintFixedIncrement.lean":"0b7263f26e8bd54c5fd5cebe375f9c70a2b83c85130c0d69178f1f834f1c74dd"})
        self.assertFalse(result["kernelValidated"])
        self.assertEqual(result["status"],"NONPASS")

    def test_actual_wrong_revision(self):
        self.request["producerHead"]="c"*40
        with self.assertRaisesRegex(ValueError,"request linkage"):
            d.reconcile(self.packet,self.expected,self.request,[ROOT])

    def test_actual_wrong_source(self):
        self.request["sources"]["Solidity/Evm/Correct.lean"]="0"*64
        with self.assertRaisesRegex(ValueError,"interface source mismatch"):
            d.reconcile(self.packet,self.expected,self.request,[ROOT])

    def test_actual_wrong_base(self):
        self.request["producerBase"]="c"*40
        with self.assertRaisesRegex(ValueError,"interface base contradiction"):
            d.reconcile(self.packet,self.expected,self.request,[ROOT])

    def test_actual_partial_roots(self):
        self.request["roots"]=self.request["roots"][:1]
        with self.assertRaisesRegex(ValueError,"interface roots contradiction"):
            d.reconcile(self.packet,self.expected,self.request,[ROOT])

    def test_actual_source_receipt_not_kernel_evidence(self):
        receipt=d.p.inspect(self.packet,self.expected)
        with self.assertRaisesRegex(ValueError,"request shape"):
            d.reconcile(self.packet,self.expected,receipt,[ROOT])


if __name__ == "__main__":unittest.main()
