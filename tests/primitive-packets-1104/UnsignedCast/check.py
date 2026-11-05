#!/usr/bin/env python3
"""Pinned packet acceptance. --full also runs unchanged repository gates."""
if not __debug__:
    raise SystemExit("Optimized Python disables required checks")
import argparse,fcntl,hashlib,itertools,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
TASK=ROOT/"tests/primitive-packets-1104/UnsignedCast"
OUT=TASK/"evidence"
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def ensure_success(data):
    assert data["exit"]==0 and data.get("error") is None and data.get("process_started") is True,"failed/incomplete controller receipt"

def receipt(mode,target):
    found=[]
    for p in OUT.glob("*.log.json"):
        data=json.loads(p.read_text())
        if data["mode"]==mode and data["target"]==target:found.append((p.stat().st_mtime_ns,p,data))
    assert found,"missing gate "+target
    _,path,data=max(found)
    ensure_success(data)
    assert data["sources"]==source_hashes,"stale Lean sources "+target
    assert data["runner_sha256"]==sha(TASK/"run.py"),"stale runner "+target
    assert data["lakefile_sha256"]==sha(ROOT/"lakefile.toml"),"stale Lake config"
    assert data["minimum_available_bytes"]>=4*1024**3,"reserve failure"
    command=data["command"]
    assert "--memory=12g" in command and "--memory-swap=12g" in command
    assert data["log_sha256"]==sha(path.with_suffix("")),"changed raw log"
    return path.with_suffix(""),data

def validate_rows(rows):
    matrix=json.loads((TASK/"matrix.json").read_text())
    keys=[(r["bits"],r["pipeline"],r["checked"],r["case"])for r in rows]
    assert len(keys)==len(set(keys))==matrix["expected_rows"]==372,"row inventory"
    assert set(keys)==set(itertools.product(matrix["widths"],matrix["pipelines"],matrix["checked"],matrix["cases"]))
    for row in rows:
        bits=row["bits"];case=row["case"];n={"zero":0,"power":1<<bits,"max":(1<<256)-1}[case]
        result=n%(1<<bits)
        assert row["passed"] and row["input"]==str(n) and row["expected"]==row["source"]==str(result)
        assert row["stack"]==[str(result),"77","88"] and row["cells"]==["64","10","99"]
        expected=f"[Solidity.Evm.Instr.mload 1, Solidity.Evm.Instr.push (Solidity.Evm.Word.val {1<<bits}), Solidity.Evm.Instr.dup 1, Solidity.Evm.Instr.jumpi 1, Solidity.Evm.Instr.revert, Solidity.Evm.Instr.swap 1, Solidity.Evm.Instr.mod]"
        assert " ".join(row["code"].split())==expected,"wrong instructions"

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run",action="store_true");parser.add_argument("--full",action="store_true");args=parser.parse_args()
    modes=[("build","Solidity.Backend.PrimitivePackets.UnsignedCast.Controls"),("check","tests/primitive-packets-1104/UnsignedCast/Matrix.lean"),("check","tests/primitive-packets-1104/UnsignedCast/Audit.lean"),("tools","versions"),("keysort","keysort")]
    if args.run:
        for mode,target in modes:subprocess.run([sys.executable,str(TASK/"run.py"),mode,target],cwd=ROOT,check=True)
    lean_files=sorted((ROOT/"Solidity/Backend/PrimitivePackets/UnsignedCast").glob("*.lean"))
    assert {p.stem for p in lean_files}=={"Semantics","Compiler","Transport","Boundaries","Controls"}
    source_hashes={str(p.relative_to(ROOT)):sha(p)for directory in [ROOT/"Solidity/Backend/PrimitivePackets/UnsignedCast",TASK]for p in directory.glob("*.lean")}
    expected_names=set()
    for p in lean_files:
        text=p.read_text();code=re.sub(r"/-[\s\S]*?-/|--[^\n]*","",text)
        assert not re.search(r"\b(sorry|axiom|admit|unsafe|partial|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth|debug.skipKernelTC)",code),"trust/budget token"
        namespace=re.search(r"^namespace (\S+)",text,re.M)[1]
        expected_names.update(namespace+"."+name for name in re.findall(r"^theorem (\S+)",text,re.M))
    for path,digest in json.loads((TASK/"inputs.json").read_text()).items():assert sha(ROOT/path)==digest,"changed producer input"
    gates=[receipt(mode,target)for mode,target in modes]
    rows=json.loads(re.search(r"UNSIGNED_CAST_MATRIX (\[.*\])",gates[1][0].read_text())[1]);validate_rows(rows)
    for kind in ["tail","width","missing-row"]:
        bad=json.loads(json.dumps(rows))
        if kind=="tail":bad[0]["stack"][-1]="89"
        elif kind=="width":bad[0]["bits"]=9
        else:bad.pop()
        refused=False
        try:validate_rows(bad)
        except AssertionError:refused=True
        assert refused,"checker accepted corruption "+kind
    for kind in ["receipt-error","unstarted-receipt"]:
        bad=dict(gates[0][1])
        if kind=="receipt-error":bad["error"]="OSError"
        else:bad["process_started"]=False
        refused=False
        try:ensure_success(bad)
        except AssertionError:refused=True
        assert refused,"checker accepted controller failure"
    audit=gates[2][0].read_text();declarations=json.loads(re.search(r"UNSIGNED_CAST_DECLARATIONS (\[.*\])",audit)[1])
    for row in declarations:row["axioms"]=sorted(row["axioms"])
    declarations.sort(key=lambda r:r["name"])
    pins=json.loads((TASK/"pins.json").read_text());assert declarations==pins["declarations"],"declaration drift"
    assert {row["module"]for row in declarations}=={str(p.relative_to(ROOT).with_suffix("")).replace("/",".")for p in lean_files}
    assert not any(r["unsafe"]or r["partial"]or r["axiom"]or not set(r["axioms"])<={"propext","Classical.choice","Quot.sound"}for r in declarations)
    observed={m[1]:sorted(re.split(r",\s*",m[2].strip()))if m[2]else[]for m in re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",audit)}
    assert observed==pins["explicit"] and set(observed)==expected_names,"explicit axiom drift"
    all_names={r["name"]:r for r in declarations};assert all(all_names[n]["axioms"]==a for n,a in observed.items())
    assert "Lean (version 4.24.0"in gates[3][0].read_text() and "Lake version 5.0.0-src+797c613"in gates[3][0].read_text(),"toolchain mismatch"
    assert "12884901888\n0\n"in gates[3][0].read_text(),"cgroup limits"
    assert "parsed 377 taclets, 131 read-bearing, table covers 131"in gates[4][0].read_text() and "annotations match"in gates[4][0].read_text(),"KeySort mismatch"
    report={"packet":"G25-UCAST-1104","modules":5,"explicit_theorems":len(observed),"declarations":len(declarations),"rows":len(rows),"negative_controls":["tail","width","missing-row","receipt-error","unstarted-receipt"],"sources":source_hashes,"gates":[{"log":str(p.relative_to(ROOT)),"log_sha256":sha(p),**r}for p,r in gates],"boundary":"Actual Source and selected symbolic Instr semantics; no physical bytecode/external EVM equivalence claim."}
    with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        (OUT/"acceptance.json").write_text(json.dumps(report,indent=2)+"\n")
        (OUT/"matrix-report.json").write_text(json.dumps(rows,indent=2)+"\n")
    print(f"PACKET_ACCEPTANCE_PASS: {len(rows)} rows, {len(observed)} theorem pins, {len(declarations)} declarations")
    if args.full:subprocess.run([sys.executable,str(TASK/"run.py"),"checkpoint","full"],cwd=ROOT,check=True)
