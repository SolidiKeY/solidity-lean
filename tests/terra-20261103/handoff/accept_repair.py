#!/usr/bin/env python3
"""Frozen repair contract. Require the exact reviewed contract commit as argument."""
import hashlib, importlib.util, json, pathlib, subprocess, sys, tarfile, unittest
ROOT=pathlib.Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
HERE=pathlib.Path(__file__).resolve().parent
REL=HERE.relative_to(ROOT)
def git(*a): return subprocess.check_output(["git",*a])
def sha(b): return hashlib.sha256(b).hexdigest()
def require(ok,message):
    if not ok: raise AssertionError(message)
def main():
    require(len(sys.argv)==2,"supply exact reviewed full contract commit")
    head=git("rev-parse","HEAD").decode().strip()
    require(sys.argv[1]==head and len(head)==40,"exact current contract HEAD required")
    require(not git("status","--porcelain","--untracked-files=no").strip(),"clean tracked tree required")
    c=json.loads((HERE/"repair-contract.json").read_text())
    require(subprocess.run(["git","merge-base","--is-ancestor",c["production_commit"],head]).returncode==0,"production ancestry")
    actual={p.name for p in HERE.iterdir() if p.is_file()}
    require(actual==set(c["inventory"]),"complete artifact inventory")
    require(not any(p.is_dir() and p.name!="__pycache__" for p in HERE.iterdir()),"unexpected artifact directory")
    for name in c["inventory"]:
        p=HERE/name; data=p.read_bytes()
        require(len(data)>40,"artifact size: "+name)
        require(git("show",head+":"+str(REL/name))==data,"frozen committed bytes: "+name)
        if name in c["hashes"]: require(sha(data)==c["hashes"][name],"artifact hash: "+name)
    source=ROOT/c["source"]
    require(sha(source.read_bytes())==c["source_sha256"],"production source hash")
    require(git("show",c["production_commit"]+":"+c["source"])==source.read_bytes(),"exact repaired production commit")
    changed=set(git("diff","--name-only",c["base"],head).decode().splitlines())
    require(changed=={c["source"]}|{str(REL/n) for n in c["inventory"]},"complete cumulative changed paths")
    with tarfile.open(HERE/"historical.tar.gz") as archive:
        for n,h in c["historical_hashes"].items():
            require(sha(archive.extractfile(n).read())==h,"immutable historical member: "+n)
    results=[]
    for filename,expected in c["suites"].items():
        spec=importlib.util.spec_from_file_location(filename,HERE/filename)
        mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
        suite=unittest.defaultTestLoader.loadTestsFromModule(mod)
        def flatten(s):
            for t in s:
                if isinstance(t,unittest.TestSuite): yield from flatten(t)
                else: yield t
        tests=list(flatten(suite)); names=[t.id().rsplit(".",1)[-1] for t in tests]
        require(sorted(names)==sorted(expected),"exact case inventory: "+filename)
        result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(tests))
        require(result.testsRun==len(expected) and not result.skipped and not result.expectedFailures and not result.unexpectedSuccesses and result.wasSuccessful(),"complete successful suite: "+filename)
        results.append({"suite":filename,"cases":names,"count":result.testsRun})
    print(json.dumps({"status":"PASS","head":head,"production_commit":c["production_commit"],"source_sha256":c["source_sha256"],"suites":results,"boundary":"synthetic gate receipts; actual handoff executable; no Lean/kernel/EVM claim"}))
if __name__=="__main__": main()
