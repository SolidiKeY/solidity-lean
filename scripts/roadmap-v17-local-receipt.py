#!/usr/bin/env python3
"""Bounded auditor-capsule intake. Failure accounting is not native proof authentication."""
import base64
import hashlib
import importlib.util
import io
import json
import math
import re
from pathlib import PurePosixPath
from pathlib import Path
import tarfile
import zlib

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("receipt_packets",ROOT/"scripts/roadmap-v17-packets.py")
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
CAPSULE_SHA="fa950fce1a634b69c5dc5d4ffb534b14542181bc9cdc8458fc2240aae6147c5d"
LIMIT=200*1024
FLAGS={"kernelValidated":False,"selectorsAuthenticated":False,"replayVerified":False,
       "semanticPremisesDischarged":False,"releaseClosed":False}
sha=lambda data:hashlib.sha256(data).hexdigest()


def physical_headers(raw):
    """Reject hidden GNU/link/sparse extensions before tarfile resolves metadata."""
    offset=0;count=0
    while offset<len(raw):
        block=raw[offset:offset+512]
        p.require(len(block)==512,"truncated physical header")
        if not any(block):
            p.require(len(raw)-offset>=1024 and not any(raw[offset:]),"bad physical end blocks")
            return
        header=tarfile.TarInfo.frombuf(block,"utf-8","strict")
        count+=1;p.require(count<=64,"physical header bound")
        p.require(header.type in (tarfile.REGTYPE,tarfile.AREGTYPE,tarfile.XHDTYPE,tarfile.XGLTYPE),
                  "non-PAX capsule extension")
        p.require(0<=header.size<=LIMIT,"physical member bound")
        data=raw[offset+512:offset+512+header.size]
        p.require(len(data)==header.size,"truncated physical body")
        if header.type in (tarfile.XHDTYPE,tarfile.XGLTYPE):
            cursor=0;seen=set()
            while cursor<len(data):
                end=data.find(b" ",cursor);p.require(end>cursor,"PAX length syntax")
                digits=data[cursor:end]
                p.require(digits.isdigit() and not digits.startswith(b"0"),"PAX length syntax")
                length=int(digits);record=data[cursor:cursor+length]
                p.require(length>len(digits)+2 and len(record)==length and record.endswith(b"\n"),"truncated PAX record")
                key,sep,_=record[len(digits)+1:-1].partition(b"=")
                p.require(sep and key in (b"mtime",b"atime",b"ctime") and key not in seen,"unsupported PAX key")
                seen.add(key);cursor+=length
        offset+=512+((header.size+511)//512)*512
    raise ValueError("missing physical end blocks")


def capsule(raw,expected_sha=CAPSULE_SHA):
    p.require(len(raw)<=LIMIT and sha(raw)==expected_sha,"capsule size/hash mismatch")
    decoder=zlib.decompressobj(16+zlib.MAX_WBITS);unpacked=decoder.decompress(raw,LIMIT+1)
    p.require(len(unpacked)<=LIMIT and decoder.eof and not decoder.unused_data
              and not decoder.unconsumed_tail,"capsule raw bound/truncation/trailing data")
    p.require(len(unpacked)%512==0,"truncated TAR blocks")
    physical_headers(unpacked)
    members={};total=0
    with tarfile.open(fileobj=io.BytesIO(unpacked),mode="r:") as archive:
        for member in archive:
            p.safe_path(member.name)
            p.require(member.isfile() and member.type in (tarfile.REGTYPE,tarfile.AREGTYPE)
                      and not member.issparse(),"nonregular capsule payload")
            p.require(set(member.pax_headers)<={"mtime","atime","ctime"},"unsupported PAX override")
            p.require(bool(member.pax_headers) or member.offset_data==member.offset+512,
                      "unsupported extended capsule header")
            p.require(member.name not in members and len(members)<16,"duplicate/extra capsule member")
            p.require(0<=member.size<=LIMIT,"member bound");total+=member.size
            p.require(total<=LIMIT,"total member bound")
            data=archive.extractfile(member).read(member.size+1)
            p.require(len(data)==member.size,"truncated capsule member")
            members[member.name]=data
        end=archive.offset
    p.require(len(unpacked)-end>=1024 and not any(unpacked[end:]),"missing end blocks/trailing TAR data")
    p.require(len(members)==16 and "SHA256SUMS" in members,"wrong capsule member set")
    manifest={}
    for line in members["SHA256SUMS"].decode("ascii").splitlines():
        p.require(len(line)>=67 and line[64:66] in ("  "," *"),"checksum manifest syntax")
        digest,name=line[:64],line[66:];p.safe_path(name)
        p.require(p.SHA.fullmatch(digest) and name not in manifest and name!="SHA256SUMS","duplicate/invalid checksum claim")
        manifest[name]=digest
    p.require(set(manifest)==set(members)-{"SHA256SUMS"},"checksum member set mismatch")
    for name,digest in manifest.items():p.require(sha(members[name])==digest,"corrupt capsule payload: "+name)
    return {"capsuleSha256":sha(raw),"memberSha256":{n:sha(b) for n,b in members.items()},
            "rawTarBytes":len(unpacked),"payloadBytes":total,"byteIntegrityVerified":True,**FLAGS},members


MEMBERS={"PROVENANCE.json","SHA256SUMS","observed-current-runner.py","phase-build.stderr",
    "phase-build.stdout","phase-postflight.stderr","phase-postflight.stdout","phase-preflight.exit",
    "phase-preflight.stderr","phase-preflight.stdout","v09-diagnostic-a-intent.json",
    "v09-diagnostic-a-result.json","v09-diagnostic-a-spec.json","v09-diagnostic-a-terminal-unit.txt",
    "v09-diagnostic-a.log","v09-validation-budget-state.json"}
REQUEST_SHA="694d1f2d597b2997f445d1bdd088e5ce3765434011bdb07e35a3fb8012c3f357"
SPEC_FIELDS={"unit","label","cwd","command","timeout","memoryMax","reserve","lease","result"}
RESULT_FIELDS=SPEC_FIELDS|{"exitCode","resourceStop","elapsedSeconds","minimumHostAvailableBytes",
    "peakMemoryBytes","swapCurrentBytes","remainingOwnedPids","cleanup","serviceHeldLeaseFds",
    "terminalCleanupBeforeLeaseRelease","status"}
PROV_FIELDS={"sourceDirectory","requestSha256","observation","missingPhaseMarkers","actualExitCode",
             "status","budgetApproval","proofBoundary"}
INTENT_FIELDS={"requestSha256","budgetSeconds","cumulativePriorExecutionSeconds","requestExecutedBefore",
               "originalWholeGoalsRemainOpen"}
BUDGET_FIELDS={"initialBudgetSeconds","initialConsumedSeconds","initialElapsedIncludingCleanupSeconds",
    "additionalRequestedSeconds","additionalApproval","additionalConsumedSeconds","originalAStatus","originalBStatus"}
MISSING=["build.exit","postflight.exit","metadata.stdout","axioms.stdout","replay.stdout"]


def account_members(members,request_raw):
    """Pure consistency checks for this failure schema; does not authenticate bytes or a process.

    Production calls this only through normalize(), after fixed capsule authentication.
    Semantic mutation tests use it directly and must not claim capsule integrity.
    """
    errors=[]
    def check(ok,message):
        if not ok:errors.append(message)
    def obj(name,fields):
        try:
            value=p.load(members[name]);check(isinstance(value,dict),name+": object required")
            if not isinstance(value,dict):return {}
            check(set(value)==fields,name+": unsupported/missing fields");return value
        except (KeyError,ValueError,TypeError,UnicodeError) as exc:
            errors.append(name+": malformed/missing JSON: "+str(exc));return {}
    check(set(members)==MEMBERS,"missing/extra capsule role members")
    result=obj("v09-diagnostic-a-result.json",RESULT_FIELDS)
    spec=obj("v09-diagnostic-a-spec.json",SPEC_FIELDS)
    prov=obj("PROVENANCE.json",PROV_FIELDS)
    intent=obj("v09-diagnostic-a-intent.json",INTENT_FIELDS)
    budget=obj("v09-validation-budget-state.json",BUDGET_FIELDS)
    check(sha(request_raw)==REQUEST_SHA,"wrong original request bytes")
    try:
        plan=p.load(request_raw)
        check(isinstance(plan,dict) and plan.get("status")=="REQUEST_NOT_EXECUTED"
              and plan.get("kernelValidated") is False and plan.get("releaseClosed") is False,
              "unsupported/promoted original request")
    except (ValueError,TypeError,UnicodeError):plan={};errors.append("malformed original request")
    for key in SPEC_FIELDS:
        check(key in spec and key in result and spec.get(key)==result.get(key),"spec/result mismatch: "+key)
    for key in ("timeout","memoryMax","reserve"):
        check(type(spec.get(key)) is int and type(result.get(key)) is int,"invalid numeric spec/result field: "+key)
    check(spec.get("timeout")==300 and spec.get("memoryMax")==12884901888
          and spec.get("reserve")==12884901888,"wrong original local budget/cap/reserve")
    root=prov.get("sourceDirectory")
    canonical=lambda value:isinstance(value,str) and PurePosixPath(value).is_absolute() and str(PurePosixPath(value))==value and ".." not in PurePosixPath(value).parts and not any(ord(c)<32 for c in value)
    check(canonical(root),"invalid reported source directory")
    root=root if canonical(root) else "/UNBOUND"
    check(spec.get("label")=="v09-diagnostic-a" and isinstance(spec.get("unit"),str)
          and re.fullmatch(r"solidity-local-v09-diagnostic-a-[0-9a-f]{8}",spec.get("unit","")) is not None,
          "wrong component/unit identity")
    check(spec.get("cwd")==root+"/compiler-pass-proofs","wrong command working-directory binding")
    check(spec.get("result")==root+"/v09-diagnostic-a-result.json","wrong result path binding")
    check(spec.get("lease")=="/tmp/solidity-lean-feature-groups-20261025/writer.lock","wrong reported lease path")
    command=spec.get("command")
    expected=["/usr/bin/env","V17_TRUSTED_PYTHON=/usr/bin/python3","/bin/sh",
              root+"/v17-local-requests/request-a-final/payload.sh",root+"/compiler-pass-proofs",
              "/home/guilherme/.elan/toolchains/leanprover--lean4---v4.24.0/bin",
              root+"/v09-diagnostic-a-output",REQUEST_SHA]
    check(command==expected,"wrong payload/request/tool/output command path binding")
    check(prov.get("requestSha256")==intent.get("requestSha256")==REQUEST_SHA,"wrong provenance/intent request binding")
    check(type(intent.get("budgetSeconds")) is int and intent.get("budgetSeconds")==300
          and type(intent.get("cumulativePriorExecutionSeconds")) is int
          and intent.get("cumulativePriorExecutionSeconds")==0
          and intent.get("requestExecutedBefore") is False and intent.get("originalWholeGoalsRemainOpen") is True,
          "wrong original execution intent/budget")
    code=result.get("exitCode");raw_code=code if type(code) is int else None
    check(type(code) is int and code==125,"unsupported outcome: only original raw125 failure is accounted")
    check(result.get("status")==prov.get("status")=="FAIL" and type(prov.get("actualExitCode")) is int
          and prov.get("actualExitCode")==code,"contradictory pass/failure/provenance exit")
    check(result.get("resourceStop")=="original time ceiling","wrong original resource stop")
    def number(value):
        try:return type(value) in (int,float) and math.isfinite(value) and value>=0
        except (OverflowError,TypeError):return False
    elapsed=result.get("elapsedSeconds")
    check(number(elapsed) and elapsed>=300,"invalid reported elapsed/deadline")
    for key in ("minimumHostAvailableBytes","peakMemoryBytes","swapCurrentBytes"):
        check(type(result.get(key)) is int and result.get(key)>=0,"invalid metric: "+key)
    check(result.get("swapCurrentBytes")==0,"contradictory swap observation")
    check(result.get("remainingOwnedPids")==[] and result.get("terminalCleanupBeforeLeaseRelease") is True,
          "contradictory reported cleanup")
    fds=result.get("serviceHeldLeaseFds")
    check(isinstance(fds,list) and bool(fds) and all(type(fd) is int and fd>=0 for fd in fds),"invalid reported lease fds")
    cleanup=result.get("cleanup")
    check(isinstance(cleanup,list) and all(isinstance(row,dict) and set(row)=={"pid","signal"}
          and type(row["pid"]) is int and row["pid"]>0 and type(row["signal"]) is int
          and row["signal"] in (15,9) for row in cleanup),"invalid cleanup observations")
    for key,value in (("initialBudgetSeconds",300),("initialConsumedSeconds",300),
                      ("additionalRequestedSeconds",300),("additionalConsumedSeconds",0)):
        check(type(budget.get(key)) is int and budget.get(key)==value,"wrong historical ledger: "+key)
    check(budget.get("initialElapsedIncludingCleanupSeconds")==elapsed,"ledger/outcome elapsed mismatch")
    check(budget.get("additionalApproval")=="PENDING" and prov.get("budgetApproval")=="PENDING; no execution authorized",
          "changed historical approval snapshot")
    check(budget.get("originalAStatus")=="FAIL: deadline and parse errors"
          and budget.get("originalBStatus")=="NOT_EXECUTED: automatic approval rejected","wrong historical A/B status")
    check(prov.get("missingPhaseMarkers")==MISSING,"changed/omitted missing-marker observations")
    check(isinstance(prov.get("observation"),str) and "no original pre-execution runner hash available" in prov.get("observation",""),
          "missing historical-runner uncertainty")
    marker=members.get("phase-preflight.exit")
    preflight=int(marker.strip()) if isinstance(marker,bytes) and re.fullmatch(rb"[0-9]+\n?",marker) else None
    check(preflight==0 and marker in (b"0",b"0\n"),"missing/invalid preflight marker")
    check(bool(members.get("phase-build.stdout")),"missing/truncated build output")
    for name in ("phase-build.stderr","phase-preflight.stdout","phase-preflight.stderr",
                 "phase-postflight.stdout","phase-postflight.stderr"):
        check(members.get(name)==b"","changed/missing original empty stream: "+name)
    log=members.get("v09-diagnostic-a.log",b"").decode("utf-8",errors="replace")
    wrapper=re.findall(r"Main processes terminated with: code=exited, status=([0-9]+)/FAILURE",log)
    wrapper_code=int(wrapper[0]) if len(wrapper)==1 else None
    check(wrapper_code==1,"missing/contradictory unit-wrapper exit")
    unit=spec.get("unit")
    check(isinstance(unit,str) and "Running as unit: "+unit+".service; invocation ID: " in log,"unit-log identity mismatch")
    lines=[line for line in log.splitlines() if line.startswith("{")]
    try:
        compact=p.load(lines[0]) if len(lines)==1 else {}
        check(set(compact)=={"status","exitCode","peak","remainingOwnedPids","stop"}
              and compact.get("status")=="FAIL" and type(compact.get("exitCode")) is int
              and compact.get("exitCode")==raw_code and compact.get("peak")==result.get("peakMemoryBytes")
              and compact.get("remainingOwnedPids")==[] and compact.get("stop")==result.get("resourceStop"),
              "unit-log/outcome contradiction")
    except (ValueError,TypeError):errors.append("malformed compact unit-log outcome")
    terminal=members.get("v09-diagnostic-a-terminal-unit.txt")
    check(terminal==b"ActiveState=inactive\nSubState=dead\nControlGroup=\n","missing/changed reported terminal unit state")
    generated=plan.get("generatedFiles") if isinstance(plan,dict) else None
    check(isinstance(generated,dict),"invalid original request generatedFiles shape")
    expected_payload=generated.get("payload.sh") if isinstance(generated,dict) else None
    if not isinstance(expected_payload,str) or not p.SHA.fullmatch(expected_payload):
        errors.append("invalid original request payload digest");expected_payload=None
    reported_missing=prov.get("missingPhaseMarkers")
    if not isinstance(reported_missing,list) or not all(isinstance(name,str) for name in reported_missing):
        reported_missing=None
    return {"schema":1,"accountingStatus":"CONSISTENT_FAILURE_ACCOUNTING" if not errors else "REJECTED_INCOMPLETE",
        "evidenceStatus":"INCOMPLETE_FAILURE","accountingErrors":errors,
        "reportedServiceExitCode":raw_code,"reportedWrapperExitCode":wrapper_code,
        "reportedResourceStop":result.get("resourceStop") if isinstance(result.get("resourceStop"),str) else None,
        "reportedElapsedIncludingCleanupSeconds":elapsed if number(elapsed) else None,
        "reportedMetrics":{key:result.get(key) if type(result.get(key)) is int else None
            for key in ("minimumHostAvailableBytes","peakMemoryBytes","swapCurrentBytes")},
        "reportedLocalLimits":{key:spec.get(key) if type(spec.get(key)) is int else None
            for key in ("timeout","memoryMax","reserve")},
        "reportedCleanupBeforeLeaseRelease":result.get("terminalCleanupBeforeLeaseRelease")
            if type(result.get("terminalCleanupBeforeLeaseRelease")) is bool else None,
        "phaseExits":{"preflight":preflight,"build":None,"postflight":None,"metadata":None,"axioms":None,"replay":None},
        "reportedMissingMarkers":reported_missing,"expectedMissingMarkers":MISSING,"completionNotEstablished":["build","postflight","metadata","axioms","replay"],
        "emptyPostflightStreamsAreNotCompletion":True,"originalBudgetExhausted":True,
        "historicalAdditionalApproval":budget.get("additionalApproval") if isinstance(budget.get("additionalApproval"),str) else None,
        "historicalApprovalIsNotCurrentAuthorization":True,"nativeExecutionAuthorized":False,
        "originalRequestSha256":REQUEST_SHA,"reportedSpecCommandMatchesOriginalPaths":command==expected,
        "expectedPayloadSha256":expected_payload,
        "observedCurrentRunnerSha256":sha(members["observed-current-runner.py"]) if "observed-current-runner.py" in members else None,
        "originalPreExecutionRunnerSha256":None,"historicalRunnerAuthenticated":False,
        "processUsageAuthenticated":False,"sourceObjectCacheEnvAuthenticated":False,"capsLeaseOwnershipAuthenticated":False,
        "configuredSwapLimitAuthenticated":False,"reportedSwapCurrentBytes":result.get("swapCurrentBytes") if type(result.get("swapCurrentBytes")) is int else None,
        "semanticCounterexampleEstablished":False,"nativeReceiptAccepted":False,
        "boundary":"Checks raw capsule-field consistency, not historical process usage, successful proof, original runner identity, source/object selectors or independent Solidity Source adequacy",**FLAGS}


def normalize(raw,request_raw):
    integrity,members=capsule(raw)
    result=account_members(members,request_raw)
    result["intake"]=integrity
    return result,members


def main():
    import argparse,fcntl,resource,signal
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
    resource.setrlimit(resource.RLIMIT_CPU,(60,60))
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("metadata deadline")))
    signal.alarm(60)
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--capsule",type=Path);group.add_argument("--base64",type=Path)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--request",type=Path,help="Original request bytes; enables narrow actual-failure accounting")
    args=parser.parse_args()
    try:
        lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        p.require(args.out.is_absolute() and args.out.resolve()==args.out and not args.out.exists()
                  and not args.out.is_relative_to(ROOT),"new external evidence directory")
        if args.base64:
            text=p.stable_read(args.base64,2*LIMIT)
            raw=base64.b64decode(b"".join(text.split()),validate=True)
        else:raw=p.stable_read(args.capsule,LIMIT)
        if args.request:
            receipt,members=normalize(raw,p.stable_read(args.request,32*1024**2))
        else:receipt,members=capsule(raw)  # Production has no self-derived expected hash.
        args.out.mkdir();payload=args.out/"payload";payload.mkdir()
        for name,body in members.items():
            path=payload/name;path.parent.mkdir(parents=True,exist_ok=True)
            p.require(path.resolve()==path and not path.exists(),"extraction collision")
            path.write_bytes(body)
        if not args.request:
            receipt.update(status="CAPSULE_BYTES_ONLY_NORMALIZER_PENDING",nativeReceiptAccepted=False,
                           historicalRunnerAuthenticated=False)
        (args.out/"INTAKE.json").write_text(json.dumps(receipt,indent=2)+"\n")
        print(json.dumps({key:receipt.get(key) for key in ("accountingStatus","evidenceStatus","reportedServiceExitCode",
              "reportedWrapperExitCode","accountingErrors","nativeReceiptAccepted")}));return 2
    except (ValueError,TypeError,OSError,EOFError,tarfile.TarError,zlib.error,MemoryError,TimeoutError) as error:
        print(json.dumps({"status":"NONPASS","error":str(error),"byteIntegrityVerified":False,**FLAGS}));return 2


if __name__=="__main__":raise SystemExit(main())
