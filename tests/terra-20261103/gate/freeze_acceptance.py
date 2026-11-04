#!/usr/bin/env python3
"""Generate the reconciled control inventory and exact-source frozen contract."""
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
REL = HERE.relative_to(ROOT).as_posix()
BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
ARCHIVE_SHA = "d3c047d0346652e4abc5ef3d7570091d707f1b6d7872e3b1fb60c30c67498aba"
GENERATED = {"accept_repaired.py", "snapshot.json"}

def digest(data): return hashlib.sha256(data).hexdigest()
def git(*args):
    env = {k:v for k,v in os.environ.items() if not k.startswith("GIT_")}
    return subprocess.check_output(["git", "-c", "safe.directory=" + str(ROOT), "-C", str(ROOT), *args], env=env)
def assertions(text):
    result=[]
    for cls in ast.parse(text).body:
        if not isinstance(cls,ast.ClassDef): continue
        for method in cls.body:
            if not isinstance(method,ast.FunctionDef): continue
            for node in ast.walk(method):
                if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and node.func.attr.startswith("assert"):
                    result.append(dict(method=method.name,line=node.lineno,expression=ast.unparse(node),key=ast.dump(node,include_attributes=False)))
    return sorted(result,key=lambda x:x["line"])
def case_inventory(text):
    return sorted(cls.name+"."+m.name for cls in ast.parse(text).body if isinstance(cls,ast.ClassDef)
                  for m in cls.body if isinstance(m,ast.FunctionDef) and m.name.startswith("test_"))
def archive():
    path=HERE/"history/tf-gate-9cc85b14.tar.gz"
    assert digest(path.read_bytes())==ARCHIVE_SHA
    with tarfile.open(path) as t:
        members=t.getmembers()
        assert all(m.isfile() and not m.name.startswith("/") and ".." not in Path(m.name).parts for m in members)
        return {m.name:t.extractfile(m).read() for m in members}

# Each non-identical historical assertion has an explicit stronger replacement.
MANUAL = {
58: (["inspect"], "Exact file inventory retained; H21's named core flag is additionally required for build-touched, not a wildcard allowance."),
66: (["inspect"], "Exact stdout status/name/duration/path is compared to every TSV row, stronger than line count."),
155: (["all_gates"], "Real Node remains mandatory, with an explicit prerequisite diagnostic."),
156: (["all_gates","setUp"], "Reject backend escape by private HOME and exact private elan/lake path identity plus complete invocation vectors; host elan may safely exist."),
170: (["inspect","all_gates"], "Exact row count and each row's status/name, plus exact command vector."),
171: (["all_gates"], "Exact command vector retained; checkpoint uses published H21 library mode, while direct real run-lean refusal remains tested."),
172: (["inspect"], "Gate return code remains exactly 1 whenever a named negative gate fails."),
173: (["inspect"], "HEAD is checked against current actual fixture commit, including the populated negative catalogue."),
174: (["inspect"], "Exact log file inventory retained plus the mandatory H21 core flag."),
178: (["inspect","all_gates","audit"], "Every old audit has real positive and specific negative controls; old infrastructure FAILs and masked automatic PASS are strengthened, not blessed."),
182: (["all_gates"], "Membership is strengthened to exact ordered wrapped/backend call vectors and counts, including inline Node."),
184: (["inspect","all_gates"], "Every status must equal its exact named expectation, stronger than membership in PASS/FAIL."),
186: (["inspect"], "Exact receipt path retained for every gate."),
188: (["all_gates","audit"], "Every failure requires a specific substantive diagnostic and infrastructure errors are rejected; mock build failures have exact backend markers."),
190: (["all_gates"], "Exact full tail includes exactly one lake build Solidity.Corpus.Basic; duplicates/extras rejected."),
191: (["inspect"], "Exact stdout-to-TSV correspondence replaces line-count-only check.")}

GUARDS = {
9:"source hash mismatch; all copied tool dependencies also pinned",
11:"artifact inventory mismatch; complete reviewed set, no ignored cache files",
12:"artifact size guard, every artifact remains larger than 40 bytes",
16:"contract parent/change-set binding; exact repaired source commit/base scope and final two-file freeze commit",
17:"committed contract bytes binding for both generated files at the exact supplied acceptance HEAD",
27:"exact complete case inventory, including all 15 old names plus additions",
29:"exact testsRun and rejection of skips/expected failures/unexpected successes",
30:"result.wasSuccessful required before PASS"}

def inventory():
    old=archive(); old_test=old["fixture/test_cases.py"].decode(); current=(HERE/"test_cases.py").read_text()
    before=assertions(old_test); after=assertions(current); mapping=[]
    for a in before:
        exact=[b for b in after if b["key"]==a["key"]]
        if exact:
            refs=exact; reason="Historical assertion retained verbatim (AST-normalized)."
        else:
            assert a["line"] in MANUAL, ("unmapped historical assertion",a)
            methods,reason=MANUAL[a["line"]]; refs=[b for b in after if b["method"] in methods]
            assert refs
        mapping.append(dict(historical={k:v for k,v in a.items() if k!="key"},replacement=[{k:v for k,v in b.items() if k!="key"} for b in refs],reason=reason))
    old_accept=ast.parse(old["fixture/accept.py"].decode()); old_guards=[]
    for n in ast.walk(old_accept):
        if isinstance(n,ast.Assert):
            assert n.lineno in GUARDS
            old_guards.append(dict(line=n.lineno,expression=ast.unparse(n.test),replacement=GUARDS[n.lineno]))
    old_cases=case_inventory(old_test); new_cases=case_inventory(current); assert old_cases==new_cases and len(old_cases)==15
    data=dict(version=2,authority="Coordinator acceptance reconciliation 2026-11-04 12:49; historical evidence immutable",
              historical_commit="9cc85b14fa3f611e183379c257b10b19e1aa5325",historical_archive_sha256=ARCHIVE_SHA,
              historical_members={k:digest(v) for k,v in sorted(old.items())},
              historical_artifacts={name:dict(archive_member="fixture/"+name,sha256=digest(old["fixture/"+name]),replacement=("unchanged historical accept.py plus new accept_repaired.py" if name=="accept.py" else "reviewed repaired "+name)) for name in ["accept.py","test_cases.py","README.md"]},
              cases=[dict(historical=c,replacement=c,positive_negative_oracle="Original case and all helper assertions mapped below; no skip/xfail") for c in old_cases],
              assertions=mapping,rejection_conditions=sorted(old_guards,key=lambda x:x["line"]),
              additional_cases={f:case_inventory((HERE/f).read_text()) for f in ["test_targets.py","test_contract.py"]},
              audit_controls={
                  "trust":"populated inventory positive; forbidden-token negative",
                  "orphans":"valid library roots/reachability positive; real Loose orphan negative",
                  "layers":"core-safe positive; concrete Semantics to Syntax.Elab negative",
                  "roots":"generated-root positive; exact missing Loose import negative",
                  "documentation":"tracked valid reference positive; missing named reference negative",
                  "axiom-pins":"one standard pin/inventory positive; shrinking-inventory negative",
                  "testsuite":"one-parameter source/hash/AST/catalogue/derived report/parity positive; unsound Report negative",
                  "corpus":"actual generator/parity/scoreboard positive with mock Lake; explicit backend failure negative",
                  "automatic":"non-vacuous one automatic positive; exactly one manual proof negative",
                  "backend":"exact private Lake argv/counts and per-file failure propagation; no real Lean",
                  "receipt":"exact five-field TSV, stdout, HEAD and complete file/call inventory"},
              policy_boundaries={"H21":"2c79634c checkpoint library mode and bounded non-root closure preserved; direct changed root restored", "spaces":"dedicated per-file/log positives retained; real JS integration uses non-space paths, scoped-out production defect recorded", "budgets":"No production proof/time/resource/skip policy changed", "trust":"Mocks establish audit behavior, not Lean/kernel/corpus/EVM validity"})
    (HERE/"old_to_new.json").write_text(json.dumps(data,indent=2)+"\n")

TEMPLATE = r'''#!/usr/bin/env python3
# GENERATED FROZEN CONTRACT: regenerate with freeze_acceptance.py, never hand edit.
import argparse, ast, hashlib, importlib.util, json, os, pathlib, re, subprocess, sys, tarfile, unittest
sys.dont_write_bytecode = True
ROOT=pathlib.Path(__file__).resolve().parents[3]
HERE=pathlib.Path(__file__).resolve().parent
REL=HERE.relative_to(ROOT).as_posix()
SOURCE_COMMIT=@@SOURCE@@
BASE=@@BASE@@
ARCHIVE_SHA=@@ARCHIVE@@
GENERATED={REL+"/accept_repaired.py",REL+"/snapshot.json"}
def require(ok, message):
    if not ok: raise AssertionError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def git(*args):
    env={k:v for k,v in os.environ.items() if not k.startswith("GIT_")}
    return subprocess.check_output(["git","-c","safe.directory="+str(ROOT),"-C",str(ROOT),*args],env=env)
def verify_snapshot(head):
    require(re.fullmatch(r"[0-9a-f]{40}",head) is not None,"invalid exact head")
    require(git("rev-parse","HEAD").decode().strip()==head,"exact head mismatch")
    require(git("rev-parse",head+"^").decode().strip()==SOURCE_COMMIT,"contract parent mismatch")
    for path in sorted(GENERATED):
        require(git("show",head+":"+path)==(ROOT/path).read_bytes(),"snapshot commit mismatch" if path.endswith("snapshot.json") else "contract commit mismatch")
    snap=json.loads((HERE/"snapshot.json").read_text())
    require(snap["source_commit"]==SOURCE_COMMIT and snap["base"]==BASE,"source binding mismatch")
    changed=set(git("diff","--name-only",SOURCE_COMMIT,head).decode().splitlines())
    require(changed==GENERATED,"contract change-set mismatch")
    source_changed=git("diff","--name-only",BASE,SOURCE_COMMIT).decode().splitlines()
    require(source_changed==snap["source_changed_paths"],"source change-set mismatch")
    require(all(p=="scripts/coord-tools/gate.sh" or p.startswith(REL+"/") for p in source_changed),"source ownership mismatch")
    require(git("merge-base",BASE,SOURCE_COMMIT).decode().strip()==BASE,"base ancestry mismatch")
    actual={p.relative_to(ROOT).as_posix() for p in HERE.rglob("*") if p.is_file()}
    require(actual==set(snap["artifact_files"]),"artifact inventory mismatch")
    source=ROOT/"scripts/coord-tools/gate.sh"
    require(digest(source.read_bytes())==snap["source_sha256"],"source hash mismatch")
    require(digest(git("show",SOURCE_COMMIT+":scripts/coord-tools/gate.sh"))==snap["source_sha256"],"source committed hash mismatch")
    for path,h in snap["files"].items():
        require((ROOT/path).stat().st_size>40,"artifact size guard")
        require(digest((ROOT/path).read_bytes())==h,"artifact hash mismatch: "+path)
        if path not in GENERATED:
            require(digest(git("show",SOURCE_COMMIT+":"+path))==h,"artifact source binding mismatch")
    for path,h in snap["dependencies"].items():
        require(digest((ROOT/path).read_bytes())==h,"dependency hash mismatch: "+path)
        require(digest(git("show",SOURCE_COMMIT+":"+path))==h,"dependency committed hash mismatch")
    require(not git("status","--porcelain","--untracked-files=no").strip(),"dirty tracked tree")
    archive=HERE/"history/tf-gate-9cc85b14.tar.gz"
    require(digest(archive.read_bytes())==ARCHIVE_SHA,"historical archive mismatch")
    with tarfile.open(archive) as t:
        members=t.getmembers()
        require(all(m.isfile() and not m.name.startswith("/") and ".." not in pathlib.PurePosixPath(m.name).parts for m in members),"unsafe historical archive")
        old={m.name:t.extractfile(m).read() for m in members}
    mapping=json.loads((HERE/"old_to_new.json").read_text())
    require({k:digest(v) for k,v in sorted(old.items())}==mapping["historical_members"],"historical member mismatch")
    require((HERE/"accept.py").read_bytes()==old["fixture/accept.py"],"historical contract changed")
    contract_tree=ast.parse(old["fixture/accept.py"].decode())
    old_contract=next(ast.literal_eval(n.value) for n in contract_tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=="CONTRACT" for x in n.targets))
    historical_names=sorted("GateCases.test_"+name for name in old_contract["cases"])
    require(snap["case_inventory"]["test_cases.py"]==historical_names,"historical case inventory mismatch")
    expected_assertions=[]
    for cls in ast.parse(old["fixture/test_cases.py"].decode()).body:
        if not isinstance(cls,ast.ClassDef): continue
        for method in cls.body:
            if not isinstance(method,ast.FunctionDef): continue
            for node in ast.walk(method):
                if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and node.func.attr.startswith("assert"):
                    expected_assertions.append((method.name,node.lineno,ast.unparse(node)))
    actual_assertions=[(x["historical"]["method"],x["historical"]["line"],x["historical"]["expression"]) for x in mapping["assertions"]]
    require(sorted(actual_assertions)==sorted(expected_assertions),"historical assertion mapping incomplete")
    old_guards=sorted((n.lineno,ast.unparse(n.test)) for n in ast.walk(contract_tree) if isinstance(n,ast.Assert))
    new_guards=sorted((x["line"],x["expression"]) for x in mapping["rejection_conditions"])
    require(new_guards==old_guards,"historical rejection mapping incomplete")
    for file,expected in mapping["additional_cases"].items():
        require(snap["case_inventory"][file]==expected,"additional control inventory mismatch")
    return snap

def flatten(suite):
    for item in suite:
        if isinstance(item,unittest.TestSuite): yield from flatten(item)
        else: yield item

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--head",required=True,help="exact independently reviewed acceptance commit")
    args=parser.parse_args()
    snap=verify_snapshot(args.head)
    tests=[]; ids=[]
    for file,expected in snap["case_inventory"].items():
        spec=importlib.util.spec_from_file_location("frozen_"+pathlib.Path(file).stem,HERE/file)
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        selected=list(flatten(unittest.defaultTestLoader.loadTestsFromModule(module)))
        names=[type(t).__name__+"."+t._testMethodName for t in selected]
        require(sorted(names)==expected,"case inventory mismatch: "+file)
        require(len(set(names))==len(names),"duplicate cases")
        tests.extend(selected);ids.extend(names)
    result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(tests))
    require(result.testsRun==len(ids) and not result.skipped and not result.expectedFailures and not result.unexpectedSuccesses,"incomplete or masked tests")
    require(result.wasSuccessful(),"fixture failure")
    verify_snapshot(args.head)
    print(json.dumps({"item":"TF-gate-reconciled","head":args.head,"source_commit":SOURCE_COMMIT,"count":result.testsRun,"cases":ids,"status":"PASS","boundary":"mock Lake, no kernel/EVM validation"}))
if __name__=="__main__":
    try: main()
    except (AssertionError,OSError,ValueError,subprocess.CalledProcessError) as error:
        print("TF-gate acceptance REJECT: "+str(error),file=sys.stderr)
        sys.exit(1)
'''

def freeze():
    assert not git("status","--porcelain","--untracked-files=no").strip(), "commit repaired inputs before freezing"
    source=git("rev-parse","HEAD").decode().strip()
    program=TEMPLATE.replace("@@SOURCE@@",repr(source)).replace("@@BASE@@",repr(BASE)).replace("@@ARCHIVE@@",repr(ARCHIVE_SHA))
    (HERE/"accept_repaired.py").write_text(program)
    files=sorted(p for p in HERE.rglob("*") if p.is_file() and p.name!="snapshot.json")
    assert not any("__pycache__" in p.parts for p in files)
    # Exact copied production-tool closure, derived from the real fixture list.
    tree=ast.parse((HERE/"test_cases.py").read_text())
    needed=next(ast.literal_eval(n.value) for n in ast.walk(tree) if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=="needed" for x in n.targets) and isinstance(n.value,ast.List))
    dependencies={"run-lean.sh"}; stack=["scripts/"+x for x in needed]
    while stack:
        path=stack.pop()
        if path in dependencies: continue
        dependencies.add(path)
        text=(ROOT/path).read_text()
        if path.endswith(".mjs"):
            for rel in re.findall(r"from [\"'](\.[^\"']+)[\"']",text):
                target=(ROOT/path).parent/rel
                stack.append(target.resolve().relative_to(ROOT).as_posix())
    case_files=["test_cases.py","test_targets.py","test_contract.py"]
    artifacts=[p.relative_to(ROOT).as_posix() for p in files]+[REL+"/snapshot.json"]
    snapshot=dict(version=2,source_commit=source,base=BASE,
        source_sha256=digest((ROOT/"scripts/coord-tools/gate.sh").read_bytes()),
        source_changed_paths=git("diff","--name-only",BASE,source).decode().splitlines(),
        artifact_files=sorted(artifacts), files={p.relative_to(ROOT).as_posix():digest(p.read_bytes()) for p in files},
        dependencies={p:digest((ROOT/p).read_bytes()) for p in sorted(dependencies)},
        case_inventory={f:case_inventory((HERE/f).read_text()) for f in case_files},
        snapshot_binding="snapshot.json and accept_repaired.py are bound by the exact --head commit and their committed bytes; the external sealed manifest hashes every file including snapshot.json",
        historical_archive_sha256=ARCHIVE_SHA)
    (HERE/"snapshot.json").write_text(json.dumps(snapshot,indent=2)+"\n")
    print(json.dumps({"source_commit":source,"artifacts":len(artifacts),"cases":sum(map(len,snapshot["case_inventory"].values()))}))

if __name__=="__main__":
    assert sys.argv[1:] in (["inventory"],["freeze"]), "usage: freeze_acceptance.py inventory|freeze"
    inventory() if sys.argv[1]=="inventory" else freeze()
