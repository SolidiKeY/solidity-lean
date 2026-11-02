import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import tarfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("local_receipt",ROOT/"scripts/roadmap-v17-local-receipt.py")
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)


def wire(change=None):
    files={"payload"+str(i)+".json":b"{}\n" for i in range(15)}
    files["SHA256SUMS"]="".join(hashlib.sha256(data).hexdigest()+"  "+name+"\n" for name,data in files.items()).encode()
    if change:change(files)
    raw=io.BytesIO()
    with tarfile.open(fileobj=raw,mode="w",format=tarfile.USTAR_FORMAT) as t:
        for name,data in files.items():
            info=tarfile.TarInfo(name);info.size=len(data);t.addfile(info,io.BytesIO(data))
    return gzip.compress(raw.getvalue())


class CapsuleGuards(unittest.TestCase):
    def test_wire_only_integrity_not_proof(self):
        raw=wire();receipt,members=x.capsule(raw,hashlib.sha256(raw).hexdigest())
        self.assertEqual(len(members),16);self.assertTrue(receipt["byteIntegrityVerified"])
        self.assertFalse(receipt["kernelValidated"]);self.assertFalse(receipt["selectorsAuthenticated"])

    def test_wrong_whole_hash(self):
        with self.assertRaisesRegex(ValueError,"hash mismatch"):x.capsule(wire(),"0"*64)

    def test_payload_corruption_and_omission(self):
        for change in (lambda files:files.update({"payload1.json":b"corrupt"}),lambda files:files.pop("payload1.json")):
            raw=wire(change)
            with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_unsafe_payload_and_extra_member(self):
        for name in ("../outside","/outside","extra"):
            raw=wire(lambda files:files.update({name:b"x"}))
            with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_truncation_and_concatenated_gzip(self):
        for raw in (wire()[:-5],wire()+gzip.compress(b"")):
            with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_link_device_and_duplicate_members(self):
        valid=gzip.decompress(wire())
        with tarfile.open(fileobj=io.BytesIO(valid),mode="r:") as t:
            entries=[(member.name,t.extractfile(member).read()) for member in t]
        for kind in (tarfile.SYMTYPE,tarfile.LNKTYPE,tarfile.CHRTYPE,"duplicate"):
            out=io.BytesIO()
            with tarfile.open(fileobj=out,mode="w",format=tarfile.USTAR_FORMAT) as t:
                for index,(name,data) in enumerate(entries):
                    member=tarfile.TarInfo(name);member.size=len(data)
                    if index==0 and kind!="duplicate":
                        member.type=kind;member.linkname="/outside";member.size=0;t.addfile(member)
                    else:t.addfile(member,io.BytesIO(data))
                if kind=="duplicate":
                    member=tarfile.TarInfo(entries[0][0]);member.size=0;t.addfile(member,io.BytesIO())
            raw=gzip.compress(out.getvalue())
            with self.subTest(kind=kind),self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_zero_last_payload_without_end_blocks(self):
        files={"payload"+str(i)+".json":b"{}" for i in range(14)};files["payload14.json"]=bytes(1024)
        checks="".join(hashlib.sha256(data).hexdigest()+"  "+name+"\n" for name,data in files.items()).encode()
        out=io.BytesIO()
        with tarfile.open(fileobj=out,mode="w",format=tarfile.USTAR_FORMAT) as t:
            for name,data in [("SHA256SUMS",checks),*files.items()]:
                member=tarfile.TarInfo(name);member.size=len(data);t.addfile(member,io.BytesIO(data))
        raw=out.getvalue()
        with tarfile.open(fileobj=io.BytesIO(raw),mode="r:") as t:
            for _ in t:pass
            end=t.offset
        compressed=gzip.compress(raw[:end])
        with self.assertRaisesRegex(ValueError,"end blocks"):x.capsule(compressed,hashlib.sha256(compressed).hexdigest())

    def test_timestamp_only_pax_metadata_not_payload_or_proof(self):
        source=gzip.decompress(wire())
        with tarfile.open(fileobj=io.BytesIO(source),mode="r:") as t:
            entries=[(m.name,t.extractfile(m).read()) for m in t]
        for metadata,accepted in (({"mtime":"123.456"},True),({"path":"../outside"},False)):
            out=io.BytesIO()
            with tarfile.open(fileobj=out,mode="w",format=tarfile.PAX_FORMAT) as t:
                for name,data in entries:
                    item=tarfile.TarInfo(name);item.size=len(data);item.pax_headers=metadata;t.addfile(item,io.BytesIO(data))
            raw=gzip.compress(out.getvalue())
            if accepted:
                receipt,_=x.capsule(raw,hashlib.sha256(raw).hexdigest());self.assertFalse(receipt["kernelValidated"])
            else:
                with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_timestamp_cannot_hide_gnu_extension(self):
        base=gzip.decompress(wire());body=b"mtime=123.456\n";length=len(body)+3
        while True:
            record=str(length).encode()+b" "+body
            if len(record)==length:break
            length=len(record)
        def block(name,kind,data):
            info=tarfile.TarInfo(name);info.type=kind;info.size=len(data)
            return info.tobuf(format=tarfile.USTAR_FORMAT)+data+bytes((-len(data))%512)
        prefix=block("pax",tarfile.XHDTYPE,record)+block("longname",tarfile.GNUTYPE_LONGNAME,b"payload0.json\0")
        raw=gzip.compress(prefix+base)
        with self.assertRaisesRegex(ValueError,"non-PAX capsule extension"):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_payload_limit(self):
        raw=wire(lambda files:files.update({"payload1.json":bytes(201*1024)}))
        with self.assertRaisesRegex(ValueError,"bound"):x.capsule(raw,hashlib.sha256(raw).hexdigest())


@unittest.skipUnless(os.environ.get("V17_FAILURE_CAPSULE"),"exact external failure capsule not supplied")
class ActualFailure(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw=Path(os.environ["V17_FAILURE_CAPSULE"]).read_bytes()
        cls.integrity,cls.original=x.capsule(cls.raw)
        cls.request=Path(os.environ["V17_FAILURE_REQUEST"]).read_bytes()

    def setUp(self):self.members=dict(self.original)
    def mutate(self,name,change):
        value=json.loads(self.members[name]);change(value);self.members[name]=json.dumps(value).encode()
    def result(self):return x.account_members(self.members,self.request)
    def rejected(self):
        value=self.result();self.assertEqual(value["accountingStatus"],"REJECTED_INCOMPLETE")
        self.assertTrue(value["accountingErrors"])
        for key in x.FLAGS:self.assertIs(value[key],False)
        return value

    def test_actual_failure_and_missing_not_zero(self):
        value,_=x.normalize(self.raw,self.request)
        self.assertEqual(value["accountingStatus"],"CONSISTENT_FAILURE_ACCOUNTING")
        self.assertEqual(value["evidenceStatus"],"INCOMPLETE_FAILURE")
        self.assertEqual(value["reportedServiceExitCode"],125)
        self.assertEqual(value["reportedWrapperExitCode"],1)
        self.assertEqual(value["phaseExits"]["preflight"],0)
        for phase in ("build","postflight","metadata","axioms","replay"):
            self.assertIsNone(value["phaseExits"][phase])
        self.assertEqual(value["reportedElapsedIncludingCleanupSeconds"],300.3127422609832)
        self.assertTrue(value["intake"]["byteIntegrityVerified"])
        self.assertIsNone(value["originalPreExecutionRunnerSha256"])
        self.assertFalse(value["historicalRunnerAuthenticated"])
        self.assertFalse(value["processUsageAuthenticated"])
        self.assertFalse(value["configuredSwapLimitAuthenticated"])
        for key in x.FLAGS:self.assertIs(value[key],False)

    def test_corrupt_truncated_whole_capsule(self):
        for raw in (self.raw[:-1],self.raw[:30]+bytes([self.raw[30]^1])+self.raw[31:]):
            with self.assertRaisesRegex(ValueError,"hash mismatch"):x.normalize(raw,self.request)

    def test_wrong_request_bytes_and_command_binding(self):
        value=x.account_members(self.members,self.request+b" ")
        self.assertIn("wrong original request bytes",value["accountingErrors"])
        for name in ("v09-diagnostic-a-spec.json","v09-diagnostic-a-result.json"):
            self.mutate(name,lambda data:data["command"].__setitem__(-1,"0"*64))
        value=self.rejected();self.assertEqual(value["reportedServiceExitCode"],125)
        self.assertFalse(value["reportedSpecCommandMatchesOriginalPaths"])

    def test_malformed_request_shapes_preserve_known_failure(self):
        for raw in (b'{"generatedFiles": []}',b'[]',b'null',b'{'):
            value=x.account_members(self.members,raw)
            self.assertEqual(value["accountingStatus"],"REJECTED_INCOMPLETE")
            self.assertEqual(value["reportedServiceExitCode"],125)
            self.assertIsNone(value["expectedPayloadSha256"])

    def test_malformed_nested_digest_cannot_leak_promotion_flags(self):
        raw=b'{"generatedFiles":{"payload.sh":{"kernelValidated":true}}}'
        value=x.account_members(self.members,raw)
        self.assertIsNone(value["expectedPayloadSha256"])
        self.assertFalse(value["kernelValidated"])
        self.assertEqual(value["reportedServiceExitCode"],125)

    def test_huge_elapsed_does_not_crash_or_overwrite_exit(self):
        self.mutate("v09-diagnostic-a-result.json",lambda data:data.update(elapsedSeconds=10**1000))
        value=self.rejected();self.assertEqual(value["reportedServiceExitCode"],125)
        self.assertIsNone(value["reportedElapsedIncludingCleanupSeconds"])

    def test_wrong_budget_in_both_spec_and_outcome(self):
        for name in ("v09-diagnostic-a-spec.json","v09-diagnostic-a-result.json"):
            self.mutate(name,lambda data:data.update(timeout=600))
        value=self.rejected();self.assertEqual(value["reportedServiceExitCode"],125)

    def test_bool_budget_not_integer(self):
        self.mutate("v09-diagnostic-a-intent.json",lambda data:data.update(cumulativePriorExecutionSeconds=False))
        self.rejected()

    def test_wrong_ledger_historical_approval(self):
        self.mutate("v09-validation-budget-state.json",lambda data:data.update(additionalApproval="APPROVED",initialConsumedSeconds=0))
        self.rejected()

    def test_unsupported_success_never_accepted(self):
        self.mutate("v09-diagnostic-a-result.json",lambda data:data.update(exitCode=0,status="PASS",resourceStop=None))
        value=self.rejected();self.assertEqual(value["reportedServiceExitCode"],0)
        self.assertFalse(value["nativeReceiptAccepted"])

    def test_raw_exit_not_inferred_124_or_137(self):
        for code in (124,137):
            self.members=dict(self.original)
            self.mutate("v09-diagnostic-a-result.json",lambda data:data.update(exitCode=code))
            self.assertEqual(self.rejected()["reportedServiceExitCode"],code)

    def test_phase_omission_and_forged_zero(self):
        self.members.pop("phase-preflight.exit");value=self.rejected()
        self.assertIsNone(value["phaseExits"]["preflight"])
        self.members=dict(self.original);self.members["phase-build.exit"]=b"0\n"
        value=self.rejected();self.assertIsNone(value["phaseExits"]["build"])
        self.mutate("PROVENANCE.json",lambda data:data.update(missingPhaseMarkers=[]))
        self.assertEqual(self.rejected()["reportedMissingMarkers"],[])

    def test_truncated_json_does_not_lose_known_raw_failure(self):
        self.members["v09-diagnostic-a-intent.json"]=self.members["v09-diagnostic-a-intent.json"][:-5]
        self.assertEqual(self.rejected()["reportedServiceExitCode"],125)

    def test_missing_result_yields_unknown_exit(self):
        self.members.pop("v09-diagnostic-a-result.json")
        self.assertIsNone(self.rejected()["reportedServiceExitCode"])

    def test_tampered_current_runner_rejected_by_capsule_identity(self):
        self.members["observed-current-runner.py"]=b'raise RuntimeError("must never execute")\n'
        self.members["SHA256SUMS"]="".join(hashlib.sha256(body).hexdigest()+"  "+name+"\n"
            for name,body in self.members.items() if name!="SHA256SUMS").encode()
        out=io.BytesIO()
        with tarfile.open(fileobj=out,mode="w",format=tarfile.USTAR_FORMAT) as t:
            for name,body in self.members.items():
                info=tarfile.TarInfo(name);info.size=len(body);t.addfile(info,io.BytesIO(body))
        with self.assertRaisesRegex(ValueError,"hash mismatch"):x.normalize(gzip.compress(out.getvalue()),self.request)

    def test_no_historical_runner_promotion(self):
        self.mutate("PROVENANCE.json",lambda data:data.update(historicalRunnerAuthenticated=True))
        value=self.rejected();self.assertFalse(value["historicalRunnerAuthenticated"])

    def test_wrong_spec_path_even_when_outcome_agrees(self):
        for name in ("v09-diagnostic-a-spec.json","v09-diagnostic-a-result.json"):
            self.mutate(name,lambda data:data.update(cwd="/different/root"))
        self.rejected()

    def test_wrapper_exit_not_substituted_for_service_exit(self):
        self.members["v09-diagnostic-a.log"]=self.members["v09-diagnostic-a.log"].replace(b"status=1/FAILURE",b"status=0/FAILURE")
        value=self.rejected();self.assertEqual(value["reportedWrapperExitCode"],0)
        self.assertEqual(value["reportedServiceExitCode"],125)


if __name__=="__main__":unittest.main()
