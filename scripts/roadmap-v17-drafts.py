#!/usr/bin/env python3
"""Private draft source reconciliation; producer signatures and proof bodies remain unvalidated."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import resource
import signal

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("draft_dependencies",ROOT/"scripts/roadmap-v17-packet-dependencies.py")
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
p=d.p


def blob(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()


def binding(path, value, head):
    p.safe_path(path)
    p.require(isinstance(value,dict) and d.module_path(value.get("module")) == path, "dependency module/path")
    p.require(isinstance(value.get("sha256"),str) and p.SHA.fullmatch(value["sha256"]), "dependency SHA")
    p.require(isinstance(value.get("git_blob"),str) and re.fullmatch(r"[0-9a-f]{40}",value["git_blob"]), "dependency blob")
    p.require("producer_head" not in value or value["producer_head"] == head, "dependency producer mismatch")
    if "bytes" in value: p.require(type(value["bytes"]) is int and 0 <= value["bytes"] <= p.RAW,"dependency size")


def no_promotion(value):
    if isinstance(value,dict):
        for key,child in value.items():
            if key in ("kernelValidated","replayValidated","semanticPremisesDischarged","releaseClosed","anchorValidated"):
                p.require(child is False,"unvalidated producer proof promotion")
            no_promotion(child)
    elif isinstance(value,list):
        for child in value:no_promotion(child)


def draft_request(packet, expected, family):
    receipt,bodies=p._inspect(packet,expected)
    claim_links={}
    for path,body in bodies.items():
        if path.endswith(".json"):
            no_promotion(p.load(body))
            claim_links[path]={"packetSha256":expected["packetSha256"],"memberSha256":expected["members"][path],
                               "boundary":"exact authenticated producer claims, not verified declarations"}
    if family == "v09":
        info=p.load(bodies["MANIFEST.json"])
        reviewed = "FINAL-MANIFEST.json" in bodies or "COMPLETE-SIGNATURES.json" in bodies
        if reviewed:
            p.require("FINAL-MANIFEST.json" in bodies and "COMPLETE-SIGNATURES.json" in bodies,
                      "incomplete reviewed metadata pair")
            final=p.load(bodies["FINAL-MANIFEST.json"])
            for key in ("head","base","candidates","exact_committed_dependencies"):
                p.require(final[key]==info[key],"reviewed/legacy source identity contradiction")
            info=final
        head,base=info["head"],info["base"]
        candidates=info["candidates"]
        bindings=info["exact_committed_dependencies"]
        signatures=(p.load(bodies["COMPLETE-SIGNATURES.json"])["candidate_signatures"]
                    if reviewed else p.load(bodies["DRAFT-SIGNATURES.json"]))
        candidate_sources={path:v["sha256"] for path,v in candidates.items()}
        for path,value in candidates.items():
            p.require(d.module_path(value["module"]) == path,"draft module mapping")
    elif family == "v11":
        info=p.load(bodies["DRAFT-INTERFACE.json"])
        head,base=info["head"],info["base"]
        table=p.load(bodies["DEPENDENCY-BLOBS.json"])
        p.require(table["producer_head"] == head,"dependency table head")
        bindings=table["committed_transitive_lean_dependencies"]
        candidate_sources=info["source_hashes"]
        p.require(set(info["module_mapping"].values()) == set(candidate_sources),"draft module set")
        for name,path in info["module_mapping"].items():
            p.require(d.module_path(name)==path,"draft module mapping")
        signatures=info["expected_public_names"]
    else: raise ValueError("unsupported draft family")
    p.require(head==expected["producerHead"],"draft producer mismatch")
    p.require(isinstance(base,str) and re.fullmatch(r"[0-9a-f]{40}",base),"draft base")
    p.require(isinstance(candidate_sources,dict) and 0 < len(candidate_sources) <= 16,"draft source set")
    p.require(candidate_sources == {path:sha for path,sha in expected["members"].items() if path.endswith(".lean")},
              "draft source inventory mismatch")
    p.require(isinstance(bindings,dict) and 0 < len(bindings) <= 4096,"draft dependency count")
    for path,value in bindings.items(): binding(path,value,head)
    p.require(not set(candidate_sources)&set(bindings),"draft/committed source collision")
    roots=sorted(path[:-5].replace("/",".") for path in candidate_sources)
    request={"schema":1,"producerHead":head,"producerBase":base,"packetSha256":expected["packetSha256"],
             "roots":roots,"sources":{**candidate_sources,**{path:v["sha256"] for path,v in bindings.items()}}}
    return request,bindings,{"family":family,"signaturesClaimedOnly":signatures,
                             "selectedManifest": "FINAL-MANIFEST.json" if family=="v09" and reviewed else
                                 ("MANIFEST.json" if family=="v09" else "DRAFT-INTERFACE.json"),
                             "selectedSignatures": "COMPLETE-SIGNATURES.json" if family=="v09" and reviewed else
                                 ("DRAFT-SIGNATURES.json" if family=="v09" else "DRAFT-INTERFACE.json"),"sourceReceipt":receipt,
                             "authenticatedClaimDocuments":claim_links,
                             "fullSourceSignatureMembers":{path:sha for path,sha in expected["members"].items() if path.endswith(".lean")},
                             "boundary":"Full required-declaration/signature/constraint/premise claims remain in hash-linked documents/source; none kernel validated"}


def dependency_archive(packet, expected, bindings):
    receipt,bodies=p._inspect(packet,expected)
    lean={path for path in bodies if path.endswith(".lean")}
    p.require(lean==set(bindings),"dependency archive incomplete/extra Lean source")
    p.require(set(bodies)-lean <= {"lean-toolchain","lakefile.toml"},"unexpected dependency configuration")
    for path,value in bindings.items():
        binding(path,value,expected["producerHead"])
        data=bodies[path]
        p.require(hashlib.sha256(data).hexdigest()==value["sha256"],"dependency archive SHA mismatch")
        p.require(blob(data)==value["git_blob"],"dependency archive blob mismatch")
        if "bytes" in value: p.require(len(data)==value["bytes"],"dependency archive size mismatch")
    return {"receipt":receipt,"bodies":bodies}


def availability(bindings, directories, supplementary):
    """Inventory every producer-listed dependency, including blocked traversal descendants."""
    rows=[]; total=0
    for path,value in bindings.items():
        matched=None;seen=[]
        def candidates():
            for item in supplementary or []:
                if path in item["bodies"]:
                    yield "archive:"+item["receipt"]["packetSha256"],item["bodies"][path]
            for directory in directories:
                local=Path(directory)/path
                if local.exists() or local.is_symlink():
                    p.require(local.resolve()==local,"symlinked availability source")
                    data=p.stable_read(local,p.RAW)
                    p.require(local.resolve()==local,"availability source path changed")
                    yield str(local),data
        for origin,data in candidates():
            total+=len(data);p.require(total<=p.RAW,"availability byte bound")
            digest=hashlib.sha256(data).hexdigest();oid=blob(data)
            seen.append({"origin":origin,"sha256":digest,"gitBlob":oid})
            if digest==value["sha256"] and oid==value["git_blob"]:
                if "bytes" in value:p.require(len(data)==value["bytes"],"dependency availability size mismatch")
                matched=seen[-1];break
        rows.append({"path":path,"expectedSha256":value["sha256"],"expectedBlob":value["git_blob"],
                     "status":"byte-match-only" if matched else "missing-or-mismatched", "match":matched,
                     "candidates":seen})
    return rows


def reconcile(packet,expected,family,directories,supplementary=None):
    request,bindings,claims=draft_request(packet,expected,family)
    result=d.reconcile(packet,expected,request,directories,supplementary)
    blob_results=[]
    for name,record in result["modules"].items():
        path=record.get("path")
        if path not in bindings: continue
        origin=record["origin"]
        if origin.startswith("archive:"):
            items=[x for x in supplementary or [] if "archive:"+x["receipt"]["packetSha256"]==origin]
            p.require(len(items)==1,"ambiguous archive origin")
            body=items[0]["bodies"][path]
        else:
            body=p.stable_read(Path(origin),p.RAW)
            p.require(hashlib.sha256(body).hexdigest()==bindings[path]["sha256"],"source changed before blob check")
        if "bytes" in bindings[path]:
            p.require(len(body)==bindings[path]["bytes"],"resolved dependency size mismatch")
        actual=blob(body); expected_blob=bindings[path]["git_blob"]
        if actual != expected_blob:
            result["issues"].append({"path":path,"status":"git-blob-mismatch","expectedBlob":expected_blob,"actualBlob":actual})
        blob_results.append({"path":path,"gitBlob":actual,"matches":actual==expected_blob})
    if result["issues"]:result["status"]="NONPASS"
    result.update(draftClaims=claims,verifiedBlobBytes=blob_results,
                  diagnosticOnly=True,sourceAvailabilityOnly=True)
    required=[]
    for issue in result["issues"]:
        path=issue.get("path")
        if issue["status"] in ("missing","hash-mismatch") and path in bindings:
            required.append({"path":path,"sha256":bindings[path]["sha256"],
                             "gitBlob":bindings[path]["git_blob"],"producerHead":expected["producerHead"]})
    result["exactMissingSourceRequests"]=required
    inventory=availability(bindings,directories,supplementary)
    result["producerListedDependencyAvailability"]=inventory
    result["allListedMissingSourceRequests"]=[{"path":x["path"],"sha256":x["expectedSha256"],
        "gitBlob":x["expectedBlob"],"producerHead":expected["producerHead"]}
        for x in inventory if x["status"]!="byte-match-only"]
    return result


def main():
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("metadata deadline")))
    signal.alarm(60)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family",choices=("v09","v11"));parser.add_argument("packet",type=Path)
    parser.add_argument("expected",type=Path);parser.add_argument("sources",type=Path,nargs="+")
    parser.add_argument("--dependencies",type=Path)
    args=parser.parse_args()
    try:
        lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        packet=p.stable_read(args.packet,p.COMPRESSED);expected=p.load(p.stable_read(args.expected,1024**2))
        supplementary=[]
        if args.dependencies:
            cfg=p.load(p.stable_read(args.dependencies,1024**2))
            p.require(isinstance(cfg,dict) and set(cfg)=={"packet","expected","bindings","producerHead"},"dependency descriptor")
            dep_expected=p.load(p.stable_read(Path(cfg["expected"]),1024**2))
            p.require(dep_expected["producerHead"]==cfg["producerHead"],"dependency descriptor head")
            table=p.load(p.stable_read(Path(cfg["bindings"]),1024**2))
            supplementary=[dependency_archive(p.stable_read(Path(cfg["packet"]),p.COMPRESSED),dep_expected,table)]
        result=reconcile(packet,expected,args.family,args.sources,supplementary)
        print(json.dumps(result,sort_keys=True));return 2 if result["status"]=="NONPASS" else 0
    except (KeyError,TypeError,ValueError,OSError,EOFError,p.tarfile.TarError,p.zlib.error,TimeoutError,MemoryError) as exc:
        print(json.dumps({"status":"NONPASS","error":str(exc),"kernelValidated":False,
                          "replayValidated":False,"releaseClosed":False,"semanticPremisesDischarged":False}))
        return 2


if __name__=="__main__":raise SystemExit(main())
