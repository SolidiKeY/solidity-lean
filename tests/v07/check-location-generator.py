#!/usr/bin/env python3
"""Check H15 generation and non-overwrite behavior on retained COPY cases."""
from pathlib import Path
import tempfile,shutil,subprocess,json,hashlib,sys
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(tempfile.mkdtemp(prefix="h15-generator-copies-",dir="/workspace/v07-evidence/restart-20261102"))
FILES=["Solidity.lean","Solidity/Lowering/V07/LocationGraphInterface.lean","Solidity/Lowering/V07/LocationGraphLaws.lean","tests/v07/generate-location-interface.py"]
results=[]
def case(name,mutate,args,expected):
    d=OUT/name
    for rel in FILES:
        p=d/rel;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,p)
    mutate(d)
    before={rel:hashlib.sha256((d/rel).read_bytes()).hexdigest() for rel in FILES}
    cmd=[sys.executable,str(d/"tests/v07/generate-location-interface.py"),*args]
    r=subprocess.run(cmd,capture_output=True,text=True)
    after={rel:hashlib.sha256((d/rel).read_bytes()).hexdigest() for rel in FILES}
    results.append(dict(case=name,command=cmd,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,before=before,after=after))
    (OUT/"results.json").write_text(json.dumps(results,indent=2)+"\n")
    assert (r.returncode==0)==expected,name
    assert before==after,"unexpected copied work overwritten: "+name

def unchanged(d):pass
def changed_interface(d):
    p=d/"Solidity/Lowering/V07/LocationGraphInterface.lean";p.write_text(p.read_text()+"\n-- retained unexpected copied work\n")
def extra_root_work(d):
    p=d/"Solidity.lean";p.write_text(p.read_text()+"\n-- retained unrelated copied work\n")
case("valid",unchanged,["--check","--register-laws"],True)
case("changed-check",changed_interface,["--check","--register-laws"],False)
case("changed-write",changed_interface,["--register-laws"],False)
case("wrong-update-hash",changed_interface,["--update-from","0"*64,"--register-laws"],False)
case("unrelated-root-work",extra_root_work,["--register-laws"],True)
print("H15 generator:5 retained copy cases pass; changed/unauthorized writes rejected; "+str(OUT))
