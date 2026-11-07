#!/usr/bin/env python3
"""Render exact-input local diagnostic requests. No Lean proof/query/build is executed; tool-version probes only."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import re
import shlex
import signal
import subprocess

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("v17_request_drafts",ROOT/"scripts/roadmap-v17-drafts.py")
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)
p=x.p;k=x.d.k
sha=lambda data:hashlib.sha256(data).hexdigest()


def observe_tools(prefix):
    prefix=Path(prefix)
    result={}
    for name in ("lean","lake"):
        binary=prefix/name
        p.require(binary.is_file() and binary.resolve()==binary,"canonical tool binary")
        result[name]={"path":str(binary),"sha256":sha(p.stable_read(binary,256*1024**2)),
                      "version":subprocess.check_output([str(binary),"--version"],text=True,timeout=10).strip()}
    prefix_root=prefix.parent
    installed=k.tool_inputs({"runtime":{"lean":{"path":str(prefix/"lean")}}})
    result["installedInputs"]={str(Path(path).relative_to(prefix_root)):digest for path,digest in installed.items()}
    return result


def check_source_header(text,name,body):
    """Check a byte-exact, balanced source header; never elaborate its implicit context."""
    p.require(isinstance(text,str) and text,"missing source header")
    found=re.match(r"theorem\s+([A-Za-z_][A-Za-z0-9_.]*)",text)
    p.require(found and found[1] in (name,name.split(".")[-1]),"signature declaration name mismatch")
    header=k.uncomment(text)
    p.require('"' not in header,"unsupported quoted source header")
    stack=[];pairs={")":"(","]":"[","}":"{"}
    for index,char in enumerate(header):
        if char in "([{":stack.append(char)
        elif char in ")]}":
            p.require(stack and stack.pop()==pairs[char],"unbalanced source header")
        p.require(not (header.startswith(":=",index) and not stack),"proof assignment inside header claim")
    p.require(not stack,"truncated nested source header")
    source=body.decode("utf-8");position=source.find(text)
    p.require(position>=0 and source.find(text,position+1)<0,"header is not unique exact source bytes")
    suffix=k.uncomment(source[position+len(text):]).lstrip()
    p.require(suffix.startswith(":="),"header omitted source text before proof assignment")


def make_plan(packet,expected,provider,tools):
    request,bindings,claims=x.draft_request(packet,expected,"v09")
    p.require(claims["selectedSignatures"]=="COMPLETE-SIGNATURES.json","reviewed signatures required")
    result=x.reconcile(packet,expected,"v09",[ROOT],[provider])
    p.require(result["status"]=="lexical-source-match-only" and not result["allListedMissingSourceRequests"],
              "complete exact source inputs required")
    _,bodies=p._inspect(packet,expected)
    info=p.load(bodies["FINAL-MANIFEST.json"])
    signatures=claims["signaturesClaimedOnly"]
    p.require(isinstance(signatures,list) and signatures,"complete signature list")
    p.require(info["signature_inventory"]==signatures,"reviewed signature document contradiction")
    groups={};seen=set()
    for claim in signatures:
        name=claim["name"];module=claim["module"];text=claim["signature_source"]
        p.require(name not in seen,"duplicate requested declaration");seen.add(name)
        p.require(module in request["roots"],"wrong defining module claim")
        p.require(isinstance(text,str) and text.lstrip().startswith("theorem "),"unsupported signature kind")
        check_source_header(text,name,bodies[x.d.module_path(module)])
        groups.setdefault(module,[]).append({"name":name,"kind":"theorem"})
    p.require(set(tools)=={"lean","lake","installedInputs"},"tool pair/import bindings")
    for tool in (tools["lean"],tools["lake"]):
        p.require(set(tool)=={"path","sha256","version"} and isinstance(tool["sha256"],str)
                  and p.SHA.fullmatch(tool["sha256"]),"tool binding")
    p.require(isinstance(tools["installedInputs"],dict) and tools["installedInputs"],"installed tool inputs missing")
    for rel,digest in tools["installedInputs"].items():
        p.safe_path(rel)
        p.require(rel.startswith("lib/") and isinstance(digest,str) and p.SHA.fullmatch(digest),"installed tool input binding")
    installed_sources=info["exact_installed_stdlib_source_dependency_hashes"]
    p.require(isinstance(installed_sources,dict) and installed_sources,"installed source claims missing")
    for rel,claim in installed_sources.items():
        p.safe_path(rel)
        p.require(rel.endswith(".lean") and rel.split("/")[0].split(".")[0] in ("Lean","Init","Std")
                  and isinstance(claim,dict) and isinstance(claim.get("sha256"),str)
                  and p.SHA.fullmatch(claim["sha256"]),"unsafe toolchain source claim")
    toolchain=provider["bodies"]["lean-toolchain"].decode().strip()
    p.require(toolchain=="leanprover/lean4:v4.24.0" and "version 4.24.0," in tools["lean"]["version"]
              and "Lean version 4.24.0" in tools["lake"]["version"],"source/toolchain version mismatch")
    config=provider["bodies"]["lakefile.toml"]
    p.require(b'weakLeanArgs = ["--tstack=131072"]' in config,"unsupported serial configuration")
    serial=config.replace(b'weakLeanArgs = ["--tstack=131072"]',b'weakLeanArgs = ["--tstack=131072", "-j1"]')
    files={};queries=[]
    for index,module in enumerate(sorted(groups)):
        req=k.request({"schema":1,"module":module,"declarations":groups[module]})
        prefix="Query"+str(index)
        files[prefix+".lean"]=k.query_bytes(req)
        files[prefix+"Axioms.lean"]=k.axiom_query(req)
        files[prefix+"-request.json"]=k.canonical(req)
        queries.append({"request":req,"query":prefix+".lean","axioms":prefix+"Axioms.lean"})
    files["roadmap-v17-diagnostic.lakefile.toml"]=serial
    source_files={**{path:expected["members"][path] for path in bodies if path.endswith(".lean")},
                  **{path:value["sha256"] for path,value in bindings.items()},
                  "lean-toolchain":sha(provider["bodies"]["lean-toolchain"]),"lakefile.toml":sha(config)}
    plan={"schema":1,"status":"REQUEST_NOT_EXECUTED","producerHeadClaim":expected["producerHead"],
          "producerBaseClaim":request["producerBase"],
          "headerBoundary":"Byte-exact named balanced headers end at source proof assignment; implicit contexts and types remain unelaborated producer claims until kernel extraction.","draftArchiveSha256":expected["packetSha256"],
          "dependencyArchiveSha256":provider["receipt"]["packetSha256"],"sourceFiles":source_files,
          "observedWorkerTools":{name:tools[name] for name in ("lean","lake")},
          "observedInstalledInputs":tools["installedInputs"],"sourceToolchain":toolchain,"producerClaimDocuments":claims["authenticatedClaimDocuments"],
          "producerInstalledStdlibSourceClaims":info["exact_installed_stdlib_source_dependency_hashes"],
          "queries":queries,"buildTargets":request["roots"],"templateSha256":sha(k.TEMPLATE.read_bytes()),
          "generatedFiles":{path:sha(body) for path,body in files.items()},
          "limits":{"memoryMaxBytes":12884901888,"swapMaxBytes":0,"componentCumulativeSeconds":300,
                    "leanJobs":1,"leanNumThreads":1,"expressionNodes":100000,"expressionDepth":512},
          "executionContract":"Run payload only inside coordinator's existing approved hard scope, local lock, native-launcher serialization and fresh admission. One300s cumulative boundary covers build+all queries+axioms for this component. Bare payload does not enforce cap/headroom or certify a gate.",
          "cacheBoundary":"Reuse only exact-source/toolchain/settings prerequisite objects; retain all object/setup hashes. Not a fresh/cold whole-target or cache-equivalence gate.",
          "requiredOuterAttachments":["pre-admission and hard-cap/no-swap/deadline/native-worker receipts",
              "actual Lake import selectors and loaded-object path/SHA256/source binding; findOLean lookup hashes are not selection evidence",
              "raw full structural output, axiom output and each phase exit",
              "independent mandatory live replay through existing consumer; no normalization assumed here"],
          "payloadBoundary":"Raw diagnostic payload with observed lookup/setup sidecars only. The outer coordinator must independently authenticate actual import selection and source/object correspondence; this is not the complete original kernel collector/normalization/replay receipt.",
          "acceptance":"Raw command exits, full structural types AND values/dependencies, loaded-object/source bindings and actual axiom output required. Independent live replay remains mandatory; no promotion from names or producer text.",
          "kernelValidated":False,"replayValidated":False,"anchorValidated":False,
          "semanticPremisesDischarged":False,"releaseClosed":False}
    more=payload_files(plan)
    files.update(more)
    plan["generatedFiles"].update({path:sha(body) for path,body in more.items()})
    plan["payloadUsage"]=["sh","payload.sh","<existing-private-source-root>","<exact-toolchain-bin>","<new-absolute-results-directory>","<request-SHA256-from-authenticated-handoff>"]
    plan["verifierRuntimeContract"]="Outer coordinator must select an approved absolute V17_TRUSTED_PYTHON path and retain its executable hash/version; Python -I ignores optimization/environment injection. This runtime is not authenticated by the payload itself."
    plan["requestDigestContract"]="Pass the exact request JSON SHA256 from the independently verified handoff/SHA256SUMS, not a digest supplied by the plan itself."
    plan["requiredPreparation"]="Verify/stage exact source archives in the existing private tree, preserve original config, install only the new hash-bound serial config beside it. Use existing source/toolchain cache; no branch adoption/cache deletion."
    return plan,files



def payload_files(plan):
    verifier = r'''import hashlib,json,sys
from pathlib import Path
root,tools=map(Path,sys.argv[1:3]);here=Path(__file__).resolve().parent
raw=(here/"LOCAL-DIAGNOSTIC-REQUEST.json").read_bytes()
assert hashlib.sha256(raw).hexdigest()==sys.argv[3],"request digest mismatch"
plan=json.loads(raw)
assert root.is_absolute() and root.resolve()==root and tools.is_absolute() and tools.resolve()==tools
for rel,digest in plan["sourceFiles"].items():
    path=root/rel
    assert path.resolve()==path and path.is_file(), "source path: "+rel
    assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,"source changed: "+rel
for name,claim in plan["observedWorkerTools"].items():
    path=tools/name
    assert path.resolve()==path and hashlib.sha256(path.read_bytes()).hexdigest()==claim["sha256"],"tool mismatch: "+name
for rel,digest in plan["observedInstalledInputs"].items():
    path=tools.parent/rel
    assert path.resolve()==path and path.is_file(),"installed input missing: "+rel
    assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,"installed input mismatch: "+rel
for rel,claim in plan["producerInstalledStdlibSourceClaims"].items():
    path=tools.parent/"src/lean"/rel
    assert path.resolve()==path and path.is_file(),"toolchain source missing: "+rel
    assert hashlib.sha256(path.read_bytes()).hexdigest()==claim["sha256"],"toolchain source mismatch: "+rel
for rel,digest in plan["generatedFiles"].items():
    path=here/rel
    assert path.resolve()==path and hashlib.sha256(path.read_bytes()).hexdigest()==digest,"request changed: "+rel
cfg=root/"roadmap-v17-diagnostic.lakefile.toml"
assert cfg.resolve()==cfg and hashlib.sha256(cfg.read_bytes()).hexdigest()==plan["generatedFiles"][cfg.name],"serial configuration mismatch"
assert plan["status"]=="REQUEST_NOT_EXECUTED" and plan["kernelValidated"] is False and plan["releaseClosed"] is False
'''
    collector=r'''import hashlib,json,sys,re
from pathlib import Path
root,tools,out=map(Path,sys.argv[1:4]);here=Path(__file__).resolve().parent
raw=(here/"LOCAL-DIAGNOSTIC-REQUEST.json").read_bytes()
assert hashlib.sha256(raw).hexdigest()==sys.argv[4],"request digest changed"
plan=json.loads(raw);objects={};setups={};errors=[]
def digest(path):
    before=path.stat()
    with path.open("rb") as f:value=hashlib.file_digest(f,"sha256").hexdigest()
    after=path.stat()
    assert (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns),"object changed while hashing"
    return value
for index,query in enumerate(plan["queries"]):
    try:
        text=(out/("metadata"+str(index)+".stdout")).read_text()
        assert text.startswith("V17_KERNEL_BEGIN\n") and text.endswith("\nV17_KERNEL_END\n"),"missing complete metadata output"
        data=json.loads(text[len("V17_KERNEL_BEGIN\n"):-len("\nV17_KERNEL_END\n")])
        assert data["releaseClosed"] is False and len(data["rows"])==len(query["request"]["declarations"]),"wrong query framing/count"
        for row in data["imports"]:
            name=row["module"];path=Path(row["olean"]).resolve()
            assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*",name),"module syntax"
            assert path.name.endswith(".olean") and (path.is_relative_to(root) or path.is_relative_to(tools.parent)),"unbound object root"
            binding={"module":name,"lookupPath":str(path),"sha256":digest(path),"variants":{},"selectionAuthenticated":False}
            for suffix in (".server",".private"):
                variant=Path(str(path)+suffix)
                if variant.exists():binding["variants"][str(variant)]=digest(variant)
            rel=name.replace(".","/")+".lean"
            if name.startswith("Solidity."):assert rel in plan["sourceFiles"],"unbound repository source"
            if rel in plan["sourceFiles"]:
                binding["source"]={"path":rel,"sha256":plan["sourceFiles"][rel]}
                setup=root/".lake/build/ir"/(name.replace(".","/")+".setup.json")
                if setup.is_file():setups[str(setup)]={"sha256":digest(setup)}
                else:errors.append("missing setup: "+str(setup))
            if name in objects:assert objects[name]==binding,"contradictory imported object"
            objects[name]=binding
    except (OSError,ValueError,KeyError,TypeError,AssertionError) as exc:errors.append(str(exc))
receipt={"schema":1,"objects":objects,"selectorsAuthenticated":False,"setups":setups,"errors":errors,"kernelValidated":False,"replayValidated":False,"releaseClosed":False,
         "boundary":"findOLean lookup/setup hashes only; actual loaded-object selection, cached source correspondence and full kernel normalization/replay remain independent obligations"}
(out/"object-inputs.json").write_text(json.dumps(receipt,indent=2)+"\n")
raise SystemExit(2 if errors else 0)
'''
    finalizer = 'finish() { original=$?; trap - EXIT; set +e; "$PYTHON" -I "$HERE/verify-inputs.py" "$ROOT" "$TOOLS" "$EXPECTED" > "$OUT/postflight.stdout" 2> "$OUT/postflight.stderr"; integrity=$?; "$PYTHON" -I "$HERE/collect-inputs.py" "$ROOT" "$TOOLS" "$OUT" "$EXPECTED" > "$OUT/objects.stdout" 2> "$OUT/objects.stderr"; objects=$?; collection=$phaseCollection; printf "%s\\n" "$objects" > "$OUT/objects.exit" || collection=125; printf "%s\\n" "$last_status" > "$OUT/command.exit" || collection=125; printf "%s\\n" "$original" > "$OUT/pipeline.exit" || collection=125; printf "%s\\n" "$integrity" > "$OUT/postflight.exit" || collection=125; final=$original; if [ "$final" -eq 0 ] && { [ "$integrity" -ne 0 ] || [ "$objects" -ne 0 ] || [ "$collection" -ne 0 ]; }; then final=125; fi; printf "%s\\n" "$final" > "$OUT/final.exit" || { [ "$final" -ne 0 ] || final=125; }; exit "$final"; }'
    bootstrap = r'''import hashlib,json,sys
from pathlib import Path
here,root,tools,out=map(Path,sys.argv[1:5]);expected=sys.argv[5]
assert all(p.is_absolute() and p.resolve()==p for p in (here,root,tools,out)),"noncanonical path"
assert root.is_dir() and tools.is_dir() and not out.exists() and out.parent.is_dir(),"output/input state"
assert not out.is_relative_to(root) and not out.is_relative_to(here),"output overlaps input tree"
raw=(here/"LOCAL-DIAGNOSTIC-REQUEST.json").read_bytes()
assert hashlib.sha256(raw).hexdigest()==expected,"externally pinned request mismatch"
plan=json.loads(raw)
for rel in ("verify-inputs.py","collect-inputs.py","payload.sh"):
    assert hashlib.sha256((here/rel).read_bytes()).hexdigest()==plan["generatedFiles"][rel],"payload changed"
'''
    lines=["#!/bin/sh","# PAYLOAD ONLY: run under the approved outer hard12GiB/no-swap scope, lock and fresh admission.",
           "# The outer300s deadline covers this ENTIRE component, not each phase.","set -eu",
           'ROOT=$1; TOOLS=$2; OUT=$3; EXPECTED=$4', 'PYTHON=${V17_TRUSTED_PYTHON:?approved coordinator Python runtime required}', 'case "$PYTHON" in /*) ;; *) exit 2 ;; esac', 'HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)',
           '"$PYTHON" -I -c '+shlex.quote(bootstrap)+' "$HERE" "$ROOT" "$TOOLS" "$OUT" "$EXPECTED"',
           'mkdir "$OUT"', 'phaseCollection=0; last_status=0', finalizer, 'trap finish EXIT', 'export LEAN_NUM_THREADS=1', 'export PATH="$TOOLS:$PATH"',
           'phase() { label=$1; shift; set +e; "$@" > "$OUT/$label.stdout" 2> "$OUT/$label.stderr"; status=$?; last_status=$status; printf "%s\\n" "$status" > "$OUT/$label.exit" || phaseCollection=125; [ "$status" -eq 0 ] || exit "$status"; [ "$phaseCollection" -eq 0 ] || exit 125; set -e; }',
           'phase preflight "$PYTHON" -I "$HERE/verify-inputs.py" "$ROOT" "$TOOLS" "$EXPECTED"',
           'cd "$ROOT"', 'phase build "$TOOLS/lake" -f "$ROOT/roadmap-v17-diagnostic.lakefile.toml" build '+
           ' '.join(shlex.quote(name) for name in plan["buildTargets"])]
    for index,query in enumerate(plan["queries"]):
        for label,filename in (("metadata",query["query"]),("axioms",query["axioms"])):
            lines.append('phase '+label+str(index)+' "$TOOLS/lake" -f "$ROOT/roadmap-v17-diagnostic.lakefile.toml" env "$TOOLS/lean" -j1 --tstack=131072 --root="$HERE" "$HERE/'+filename+'"')

    return {"verify-inputs.py":verifier.encode(),"collect-inputs.py":collector.encode(),"payload.sh":("\n".join(lines)+"\n").encode()}

def main():
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("metadata deadline")))
    signal.alarm(60)
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("packet","expected","dependency_packet","dependency_expected","dependency_bindings","toolchain_bin","output"):
        parser.add_argument(name,type=Path)
    args=parser.parse_args()
    try:
        lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        p.require(not args.output.exists() and args.output.is_absolute() and args.output.resolve()==args.output
                  and not args.output.is_relative_to(ROOT),"new absolute external request directory")
        component_spec=importlib.util.spec_from_file_location("request_components",ROOT/"scripts/roadmap-v17-components.py")
        components=importlib.util.module_from_spec(component_spec);component_spec.loader.exec_module(components)
        import os
        os.environ["PATH"]=str(args.toolchain_bin)+os.pathsep+os.environ.get("PATH", "")
        before=components.consumer_identity()
        consumer_sources={}
        for path in (Path(__file__),ROOT/"scripts/roadmap-v17-drafts.py",ROOT/"scripts/roadmap-v17-packet-dependencies.py"):
            rel=str(path.relative_to(ROOT));data=path.read_bytes()
            p.require(components.git(ROOT,"show",before["snapshot"]["revision"]+":"+rel)==data,"uncommitted request helper")
            consumer_sources[rel]=sha(data)
        provider=x.dependency_archive(p.stable_read(args.dependency_packet,p.COMPRESSED),
            p.load(p.stable_read(args.dependency_expected,1024**2)),p.load(p.stable_read(args.dependency_bindings,1024**2)))
        plan,files=make_plan(p.stable_read(args.packet,p.COMPRESSED),p.load(p.stable_read(args.expected,1024**2)),
                             provider,observe_tools(args.toolchain_bin))
        p.require(components.consumer_identity()==before,"consumer changed during request preparation")
        plan["consumerIdentity"]=before;plan["consumerSources"]=consumer_sources
        args.output.mkdir()
        for path,body in files.items():(args.output/path).write_bytes(body)
        (args.output/"LOCAL-DIAGNOSTIC-REQUEST.json").write_text(json.dumps(plan,indent=2)+"\n")
        print(json.dumps({"status":plan["status"],"declarations":sum(len(q["request"]["declarations"]) for q in plan["queries"]),
                          "kernelValidated":False,"releaseClosed":False}))
        return 0
    except (KeyError,TypeError,ValueError,OSError,EOFError,p.tarfile.TarError,p.zlib.error,subprocess.SubprocessError,MemoryError,TimeoutError) as exc:
        print(json.dumps({"status":"NONPASS","error":str(exc),"kernelValidated":False,"releaseClosed":False}));return 2


if __name__=="__main__":raise SystemExit(main())
