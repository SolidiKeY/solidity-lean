#!/usr/bin/env python3
# GENERATED FROZEN CONTRACT: regenerate with freeze_acceptance.py, never hand edit.
import argparse, ast, hashlib, importlib.util, json, os, pathlib, re, subprocess, sys, tarfile, unittest
sys.dont_write_bytecode = True
ROOT=pathlib.Path(__file__).resolve().parents[3]
HERE=pathlib.Path(__file__).resolve().parent
REL=HERE.relative_to(ROOT).as_posix()
SOURCE_COMMIT='04bac54e1f52aebf8deb87095dcb3c3fa3399d59'
BASE='6f3eedf0788ee1f8a3bcf230558c712ecdca04d5'
ARCHIVE_SHA='d3c047d0346652e4abc5ef3d7570091d707f1b6d7872e3b1fb60c30c67498aba'
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
    require(all(p in ("scripts/coord-tools/gate.sh","scripts/check-doc-paths.sh") or p.startswith(REL+"/") for p in source_changed),"source ownership mismatch")
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
    override=os.environ.get("GATE_TOOL")
    require(override is None or pathlib.Path(override).resolve()==(ROOT/"scripts/coord-tools/gate.sh").resolve(),"gate tool override mismatch")
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
