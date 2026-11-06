#!/usr/bin/env python3
"""Static peer-selector/replay contracts. Never authenticate native execution from metadata alone."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import signal

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("selector_drafts",ROOT/"scripts/roadmap-v17-drafts.py")
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)
p=x.p;k=x.d.k
sha=lambda data:hashlib.sha256(data).hexdigest()
FLAGS={"selectorsAuthenticated":False,"kernelValidated":False,"replayVerified":False,
       "semanticPremisesDischarged":False,"releaseClosed":False}
REPLAY_KEYS=("draftArchiveSha256","dependencyArchiveSha256","sourceFiles","observedWorkerTools",
             "observedInstalledInputs","sourceToolchain","queries","buildTargets","templateSha256",
             "generatedFiles","limits","producerHeadClaim","producerBaseClaim")


def pinned_plan(raw,digest):
    p.require(isinstance(digest,str) and p.SHA.fullmatch(digest) and sha(raw)==digest,"wrong request digest")
    plan=p.load(raw)
    p.require(type(plan.get("schema")) is int and plan["schema"]==1,"request schema")
    x.no_promotion(plan)
    p.require(all(type(v) is int for v in plan["limits"].values()),"invalid request budget types")
    p.require(plan["status"]=="REQUEST_NOT_EXECUTED" and plan["kernelValidated"] is False
              and plan["releaseClosed"] is False,"not an unpromoted request")
    p.require(plan["limits"]=={"memoryMaxBytes":12884901888,"swapMaxBytes":0,"componentCumulativeSeconds":300,
              "leanJobs":1,"leanNumThreads":1,"expressionNodes":100000,"expressionDepth":512},"changed request budgets")
    p.require(isinstance(plan["queries"],list) and 0<len(plan["queries"])<=16,"empty/oversized query groups")
    p.require(isinstance(plan["buildTargets"],list) and plan["buildTargets"],"missing defining module roots")
    seen_modules=set();seen_files=set();seen_names=set()
    for query in plan["queries"]:
        req=k.request(query["request"])
        p.require(req["module"] in plan["buildTargets"] and req["module"] not in seen_modules,"wrong/duplicate defining module coverage")
        seen_modules.add(req["module"])
        for filename in (query["query"],query["axioms"]):
            p.safe_path(filename)
            p.require(filename.endswith(".lean") and filename not in seen_files,"duplicate query/axiom filename")
            seen_files.add(filename)
        for row in req["declarations"]:
            p.require(row["name"] not in seen_names,"duplicate declaration coverage")
            seen_names.add(row["name"])
        p.require(plan["generatedFiles"][query["query"]]==sha(k.query_bytes(req)),"wrong original extractor query")
        p.require(plan["generatedFiles"][query["axioms"]]==sha(k.axiom_query(req)),"wrong original axiom query")
    p.require(plan["templateSha256"]==sha(k.TEMPLATE.read_bytes()),"changed kernel template")
    return plan


def query_closure(plan,graph,module):
    p.require(graph.get("status")=="lexical-source-match-only" and not graph.get("issues"),"incomplete source graph")
    x.no_promotion(graph)
    modules=graph["modules"];done={};active=set()
    def visit(name):
        p.require(name not in active,"cyclic source graph")
        if name in done:return
        p.require(len(active)<128 and len(done)<4096,"source graph bound")
        row=modules[name];rel=x.d.module_path(name)
        p.require(row["path"]==rel and row["sha256"]==plan["sourceFiles"][rel],"wrong source graph binding")
        active.add(name)
        for dep in row["imports"]:
            p.require(k.NAME.fullmatch(dep),"malformed dependency")
            if dep.startswith("Solidity."):visit(dep)
            else:p.require(dep.split(".")[0] in ("Init","Lean","Std"),"unsupported dependency")
        active.remove(name);done[name]={"path":rel,"sha256":row["sha256"]}
    visit(module)
    return done


def prepare(plan,graph,request_digest,graph_digest):
    source_apis={}
    prefix=Path(plan["observedWorkerTools"]["lean"]["path"]).parent.parent
    for rel in ("Lean/Setup.lean","Lean/Environment.lean","Lean/Elab/Import.lean","Lean/Util/Path.lean"):
        claim=plan["producerInstalledStdlibSourceClaims"][rel]
        path=prefix/"src/lean"/rel
        actual=sha(p.stable_read(path,1024**2))
        p.require(actual==claim["sha256"],"selector source API mismatch")
        source_apis[rel]={"sha256":actual,"path":str(path),"boundary":"observed source bytes, not execution authentication"}
    queries=[]
    for index,query in enumerate(plan["queries"]):
        closure=query_closure(plan,graph,query["request"]["module"])
        queries.append({"index":index,"request":query["request"],"requiredProjectSources":closure,
            "querySha256":plan["generatedFiles"][query["query"]],"axiomsSha256":plan["generatedFiles"][query["axioms"]],
            "setupCaptureArgv":["${LAKE}","-f","${PRIVATE_ROOT}/roadmap-v17-diagnostic.lakefile.toml",
                               "setup-file","${REQUEST_ROOT}/"+query["query"]],
            "explicitSelectionQueryArgv":["${LAKE}","-f","${PRIVATE_ROOT}/roadmap-v17-diagnostic.lakefile.toml","env",
                "${LEAN}","-j1","--tstack=131072","--root=${REQUEST_ROOT}","--setup=${ACTUAL_SETUP_"+str(index)+"}",
                "${REQUEST_ROOT}/"+query["query"]],
            "explicitSelectionAxiomArgv":["${LAKE}","-f","${PRIVATE_ROOT}/roadmap-v17-diagnostic.lakefile.toml","env",
                "${LEAN}","-j1","--tstack=131072","--root=${REQUEST_ROOT}","--setup=${ACTUAL_SETUP_"+str(index)+"}",
                "${REQUEST_ROOT}/"+query["axioms"]],
            "selectorModeChangeRequiresNewFirst":True,
            "appliesAsReplayOfOriginalNoSetupRun":False,
            "pending":"Actual setup stdout/exit/SHA, effective argv/env and process-bound selected input hashes not supplied. Adding --setup changes collection inputs and requires a new first observation, not a replay of the original no-setup request."})
    return {"schema":1,"status":"STATIC_PREPARATION_ONLY","requestSha256":request_digest,"sourceGraphSha256":graph_digest,
        "queries":queries,"limits":plan["limits"],"selectorSourceAPIs":source_apis,
        "declarationCoverageBoundary":"Exact names in externally pinned request and defining-module roots are retained. Full source/signature documents remain hash-linked producer claims, not an independently elaborated coverage theorem.",
        "invocationPolicy":"Templates only, not execution authority. Original DraftA failed at its300s ceiling. Additional shared300s for correctedA+B is awaiting human approval. No A/B/replay/setup-file invocation is authorized now, and no per-query/component/replay budget is newly granted. Future replay needs actual prerequisite success, exact unchanged input authentication and explicit remaining budget authority; corrected source needs a new first record.",
        "budgetHold":{"status":"PENDING_HUMAN_APPROVAL","originalLocalBudgetExhausted":True,
             "additionalSharedSecondsRequested":300,"additionalSharedSecondsApproved":False,
             "reportedBApprovalRejection":"Automatic review interpreted original300s as shared; no B run permitted",
             "allowedNow":["read/hash already-existing receipts, sources, objects and setup files under metadata bounds"],
             "forbiddenNow":["Lean/Lake proof/query/build/setup-file execution","retry or counter reset"]},
        "reportedFirstOutcome":{"source":"coordinator user update; raw receipt not yet received by worker","component":"DraftA; not a B execution outcome",
             "requestSha256":"694d1f2d597b2997f445d1bdd088e5ce3765434011bdb07e35a3fb8012c3f357",
             "status":"FAIL","deadlineSeconds":300,"elapsedIncludingCleanupSeconds":300.312742,
             "peakBytes":3256987648,"minimumHostAvailableBytes":35163959296,"swapBytes":0,
             "ownCgroupEmptyBeforeLeaseRelease":True,"completedBuild":False,"completedMetadata":False,
             "completedAxioms":False,"completedReplay":False,
             "diagnostic":"Reserved local identifier have prefix := at69/105 in ReframedFailureWitness; cascading parse errors; not a demonstrated semantic counterexample"},
        "foundationMetadataRequest":[{"module":path[:-5].replace("/","."),"source":path,"sha256":digest,
              "required":["actual existing source bytes/blob","completed module log and command/source binding",
                          "existing olean/IR/server/private and setup hashes","raw end-scope and before/after cache provenance"],
              "boundary":"Read/hash only; salvage exact prerequisite bytes without promoting the failed whole component"}
             for path,digest in plan["sourceFiles"].items()
             if path.startswith("Solidity/Backend/Passes/") and path.endswith(".lean")
             and path[:-5].replace("/",".") not in plan["buildTargets"]],
        "liveReplayPolicy":"After a genuinely successful fully authenticated first collection, repeat its exact actual argv/env/setup/source/tool/config/object inputs. No valid replay exists for the failed incomplete originalA. No replay is authorized by these templates.",
        "requiredFirstReceipt":["full public baseline HEAD/tree and complete private addition manifest before/after",
             "bound service command/env, writer lease, cap/no-swap/deadline/outcome and raw every-phase exits",
             "full untruncated metadata/axiom outputs and immutable request/query SHA bindings",
             "actual query setup/import selectors (or process-observed search-path/selection evidence); build setup or findOLean alone insufficient",
             "every selected olean/IR/server/private part and actual evaluator IR input hashes before/after; the existing installed olean/so manifest alone does not bind evaluator IR",
             "all project source/config/tool inputs before/after and source-to-object build/cache provenance"],
        "existingConsumerCompatibility":{"genericKernelVerify":False,"derived17Verify":False,
             "reason":"kernel.validate_record/verify requires its original fresh Docker/workspace/source/pipeline receipt; derived17 consumer accepts only its fixed ten declarations. Raw local diagnostics are neither format.",
             "unchangedGenericInvocation":["python3","scripts/roadmap-v17-kernel.py","verify","--record","<original-format-record>","--claims","<exact-claims>","--out","<new-workspace-replay-output>"],
             "reusableAPIs":["kernel.request","kernel.parse_output","kernel.validate_expr","kernel.ast_names","kernel.check_axiom_text","kernel.match_claims"],
             "pendingImplementation":"A separately reviewed supplemental local receipt consumer needs the actual first receipt/selector format. Do not alias warm paths to fresh or fabricate a Docker record to call generic verify."},
        **FLAGS}


def lint_setup(setup,closure,parts_before,parts_after):
    """Consistency lint of explicit selectors, not proof that a process used this setup."""
    p.require(all(isinstance(v,dict) for v in (setup,closure,parts_before,parts_after)),"selector input shapes")
    p.require(0<len(closure)<=4096,"empty/oversized project closure")
    for name,row in closure.items():
        p.require(isinstance(name,str) and name.startswith("Solidity.") and isinstance(row,dict)
                  and set(row)=={"path","sha256"} and row["path"]==x.d.module_path(name)
                  and isinstance(row["sha256"],str) and p.SHA.fullmatch(row["sha256"]),"wrong closure source binding")
    p.require(set(setup)=={"name","isModule","options","plugins","dynlibs","importArts"},"unsupported actual setup fields")
    p.require(setup["name"]=="_unknown" and setup["isModule"] is False and setup["options"]=={}
              and setup["plugins"]==[] and setup["dynlibs"]==[],"changed external query setup semantics")
    p.require(set(setup["importArts"])==set(closure),"missing/extra project selectors")
    p.require(parts_before==parts_after,"selected input changed before/after")
    selected={};all_parts=set()
    for name,parts in setup["importArts"].items():
        p.require(k.NAME.fullmatch(name) and isinstance(parts,list) and 1<=len(parts)<=4,"selector part shape")
        endings=(".olean",".ir",".olean.server",".olean.private")
        for index,path in enumerate(parts):
            p.require(isinstance(path,str) and Path(path).is_absolute() and str(Path(path))==path
                      and ".." not in Path(path).parts and path.endswith(endings[index]),"wrong selector part role/path")
            p.require(path in parts_before and isinstance(parts_before[path],str) and p.SHA.fullmatch(parts_before[path]),"unbound selected artifact")
            all_parts.add(path)
        # Lean4.24 Setup.ImportArtifacts slots:0 olean,1 IR,2 server,3 private.
        # External legacy setup isModule=false => Elab.processHeaderCore level.private.
        selected[name]={"oleanParts":[parts[i] for i in (0,2,3) if i<len(parts)],
                        "evaluatorIR":parts[1] if len(parts)>1 else None,"fallbackIRUnresolved":len(parts)==1}
    p.require(set(parts_before)==all_parts,"unmatched selected-part hash claim")
    return {"bindingsConsistent":True,"legacyPrivateLevelParts":selected,
            "boundary":"Raw setup/hash consistency only; actual command selector usage and evaluator fallback IR remain process-authentication obligations",**FLAGS}


def original_request_consistency(first,second):
    """Only compare complete original request documents, never native replay receipts."""
    p.require(isinstance(first,dict) and isinstance(second,dict) and
              all(key in first and key in second for key in REPLAY_KEYS),"missing original request fields")
    forbidden={"setup","actualSetup","argv","env","actualInputs","selectors","partsBefore","partsAfter",
               "sourceBefore","sourceAfter","setupSha256","actualRuntime","nativeReceipt"}
    p.require(not forbidden.intersection(first) and not forbidden.intersection(second),
              "runtime selector/evidence fields are not original requests")
    p.require(first.get("status")==second.get("status")=="REQUEST_NOT_EXECUTED","not original request documents")
    x.no_promotion(first);x.no_promotion(second)
    p.require(first==second,"changed complete original request/source/tool/config/query inputs")
    return {"originalRequestInputsConsistent":True,
            "boundary":"Exact original request document equality only; no native invocation/setup/selector/output receipt or replay is accepted",**FLAGS}


def main():
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("metadata deadline")));signal.alarm(60)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("plan",type=Path);parser.add_argument("request_sha256")
    parser.add_argument("graph",type=Path);parser.add_argument("graph_sha256");parser.add_argument("out",type=Path)
    args=parser.parse_args()
    try:
        import fcntl
        lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        raw=p.stable_read(args.plan,p.RAW);plan=pinned_plan(raw,args.request_sha256)
        raw_graph=p.stable_read(args.graph,p.RAW);p.require(sha(raw_graph)==args.graph_sha256,"wrong source graph digest")
        result=prepare(plan,p.load(raw_graph),args.request_sha256,args.graph_sha256)
        p.require(args.out.is_absolute() and args.out.resolve()==args.out and not args.out.exists()
                  and not args.out.is_relative_to(ROOT),"new external contract directory")
        args.out.mkdir();(args.out/"SELECTOR-REPLAY-CONTRACT.json").write_text(json.dumps(result,indent=2)+"\n")
        print(json.dumps({"status":result["status"],"queryGroups":len(result["queries"]),**FLAGS}));return 0
    except (KeyError,TypeError,ValueError,OSError,MemoryError,TimeoutError) as exc:
        print(json.dumps({"status":"NONPASS","error":str(exc),**FLAGS}));return 2


if __name__=="__main__":raise SystemExit(main())
