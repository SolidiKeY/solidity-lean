#!/usr/bin/env python3
"""Prepare/verify owned C3 Lake cache files. Preparation is NOT a transfer receipt."""
import argparse,fcntl,hashlib,json,os,shutil,stat,subprocess,tarfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
AREA=ROOT/"tests/sol-c3-exactness"
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1048576),b""):h.update(b)
    return h.hexdigest()
def require(ok,msg):
    if not ok:raise ValueError(msg)
def checked_git(*args):
    try:return subprocess.check_output(["git",*args],cwd=ROOT,stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError as e:raise ValueError("invalid producing Git object") from e

def check_model(out,m,r,paths,mapping):
    closure=json.loads((AREA/"evidence/import-closure.json").read_text());task=json.loads((AREA/"manifest.json").read_text())
    require(m["roots"]==closure["roots"] and set(m["roots"])==set(task["modules"]),"root inventory drift")
    source_hashes={p:sha(ROOT/p) for p in closure["sources"]}
    require(source_hashes=={p:v["sha256"] for p,v in closure["sources"].items()}==m["source_hashes"],"source snapshot drift")
    traces={}
    for source in closure["sources"]:
        p=ROOT/".lake/build/lib/lean"/Path(source).with_suffix(".trace");d=json.loads(p.read_text());traces[source]=dict(trace_sha256=sha(p),depHash=d["depHash"],outputs=d["outputs"])
    require(m["traces"]==traces,"trace snapshot drift")
    expected_mappings={t["depHash"]:t["outputs"] for t in traces.values()}
    require(len(mapping)==len(expected_mappings) and dict(mapping)==expected_mappings,"mapping coverage drift")
    artifacts=set()
    for t in traces.values():
        require(set(t["outputs"])=={"o","i","c"},"unsupported Lake output schema")
        for kind,val in t["outputs"].items():
            for h in val if isinstance(val,list) else [val]:artifacts.add("artifacts/"+str(h)+"."+{"o":"olean","i":"ilean","c":"c"}[kind])
    require(paths==artifacts|{"inputs/solidity-lean.jsonl"},"mapped artifact coverage drift")
    require(r["head"]==m["head"] and len(r["head"])==40,"receipt head drift")
    require(checked_git("rev-parse","--verify",m["head"]+"^{commit}").decode().strip()==m["head"],"producing head drift")
    for source,pin in source_hashes.items():require(hashlib.sha256(checked_git("show",m["head"]+":"+source)).hexdigest()==pin,"producing Git source drift")
    require(m["toolchain"]==(ROOT/"lean-toolchain").read_text().strip()==checked_git("show",m["head"]+":lean-toolchain").decode().strip(),"toolchain drift")
    require(r["owned_modules"]==len(m["roots"]) and r["closure_modules"]==len(traces) and r["artifacts"]==len(artifacts),"receipt count drift")
    require(r["artifact_bytes"]==sum((out/p).stat().st_size for p in artifacts),"receipt byte count drift")
    require(r["preparer_sha256"]==sha(Path(__file__)),"preparer source drift")
    for name,g in m["gates"].items():
        require(Path(name).name==name and name.startswith("h35-") and name.endswith(".log.json"),"gate path drift")
        p=AREA/"evidence"/name;gate=json.loads(p.read_text())
        require(g==dict(receipt_sha256=sha(p),exit=gate["exit"],command=gate["command"],log_sha256=gate["log_sha256"]),"gate summary snapshot drift")
        require(sha(p.with_suffix(""))==gate["log_sha256"],"gate log snapshot drift")
        if name in {"h35-owned-build.log.json","h35-axiom-mcp.log.json","h35-controls-mcp.log.json","h35-graph-controls-mcp.log.json","h35-compiler-controls.log.json","h35-acceptance-controls.log.json"}:
            require(gate["exit"]==0 and not gate["pressure_stop"] and not gate["interrupted"] and gate["checked_head"]==m["head"],"VM gate status/head drift")
            require(gate["memory_limit_bytes"]==12884901888 and gate["swap_limit_bytes"]==0 and gate["minimum_parent_available_bytes"]>=4*1024**3,"VM gate resource drift")
            for source,pin in gate["input_hashes"].items():require(sha(ROOT/source)==pin,"VM gate source drift")
    require({"h35-owned-build.log.json","h35-axiom-mcp.log.json","h35-controls-mcp.log.json","h35-graph-controls-mcp.log.json","h35-compiler-controls.log.json","h35-acceptance-controls.log.json"}<=set(m["gates"]),"required gate omitted")

def negative_controls(out):
    import copy
    m=json.loads((out/"cache-manifest.json").read_text());r=json.loads((out/"receipt.json").read_text());paths=set(m["payload_sha256"]);mapping=[json.loads(x) for x in (out/"inputs/solidity-lean.jsonl").read_text().splitlines()]
    cases=[]
    def case():return copy.deepcopy(m),copy.deepcopy(r),set(paths),copy.deepcopy(mapping)
    x=case();x[1]["head"]="wrong";cases.append(x)
    x=case();x[1]["artifacts"]=0;cases.append(x)
    x=case();x[1]["artifact_bytes"]=0;cases.append(x)
    x=case();x[1]["preparer_sha256"]="0"*64;cases.append(x)
    x=case();x[2].remove(next(p for p in paths if p.startswith("artifacts/")));cases.append(x)
    x=case();x[3].pop();cases.append(x)
    x=case();x[3][0][1]={};cases.append(x)
    x=case();x[0]["source_hashes"][next(iter(x[0]["source_hashes"]))]="0"*64;cases.append(x)
    x=case();x[0]["gates"]["h35-owned-build.log.json"]["receipt_sha256"]="0"*64;cases.append(x)
    x=case();x[0]["head"]=x[1]["head"]="0"*40;cases.append(x)
    x=case();x[0]["head"]=x[1]["head"]="a7f4755cc1bd375052622aec6a966b6a1c21e427";cases.append(x)
    x=case();x[0]["toolchain"]="wrong";cases.append(x)
    x=case();x[0]["gates"]["h35-owned-build.log.json"]["exit"]=1;cases.append(x)
    x=case();x[0]["gates"]["h35-owned-build.log.json"]["command"]=["wrong"];cases.append(x)
    x=case();x[0]["gates"]["h35-owned-build.log.json"]["log_sha256"]="0"*64;cases.append(x)
    rejected=0
    for args in cases:
        try:check_model(out,*args)
        except ValueError:rejected+=1
        else:raise ValueError("cache negative control accepted")
    return rejected

def verify(out):
    m=json.loads((out/"cache-manifest.json").read_text());r=json.loads((out/"receipt.json").read_text())
    check_model(out,m,r,set(m["payload_sha256"]),[json.loads(x) for x in (out/"inputs/solidity-lean.jsonl").read_text().splitlines()])
    expected=set(m["payload_sha256"])|{"cache-manifest.json","receipt.json","cache.tar.gz","README.md","SHA256SUMS"}
    require({str(p.relative_to(out)) for p in out.rglob("*") if p.is_file()}==expected,"packet inventory drift")
    for p in out.rglob("*"):require(not p.is_symlink(),"packet symlink")
    actual={str(p.relative_to(out)):sha(p) for p in out.rglob("*") if p.is_file() and p.name!="SHA256SUMS"}
    require((out/"SHA256SUMS").read_text()=="".join(actual[p]+"  "+p+"\n" for p in sorted(actual)),"checksum inventory drift")
    for p,s in m["payload_sha256"].items():require(actual[p]==s,"payload hash drift")
    require(r["archive_sha256"]==actual["cache.tar.gz"] and r["manifest_sha256"]==actual["cache-manifest.json"],"receipt hash drift")
    require(r["shipping_status"]=="prepared_not_shipped","false shipping status")
    with tarfile.open(out/"cache.tar.gz","r:gz") as t:
        members=t.getmembers();require({x.name for x in members}==set(m["payload_sha256"])|{"cache-manifest.json"} and len(members)==len(m["payload_sha256"])+1,"archive inventory drift")
        for x in members:
            require(x.isfile(),"nonregular archive member")
            f=t.extractfile(x);h=hashlib.sha256()
            for b in iter(lambda:f.read(1048576),b""):h.update(b)
            require(h.hexdigest()==actual[x.name],"archive content drift")
    return r

def prepare(out,cache):
    start=time.monotonic();require(out.is_relative_to(AREA/".artifacts") and not out.exists(),"output must be new owned artifact directory")
    closure=json.loads((AREA/"evidence/import-closure.json").read_text());task=json.loads((AREA/"manifest.json").read_text())
    require(set(closure["roots"])==set(task["modules"]),"owned roots drift")
    for p,v in closure["sources"].items():require(sha(ROOT/p)==v["sha256"],"closure source drift")
    with (cache/"inputs/solidity-lean.jsonl").open() as mapfile:
        fcntl.flock(mapfile,fcntl.LOCK_SH|fcntl.LOCK_NB)
        mappings={}
        for l in mapfile:
            k,v=json.loads(l);mappings[k]=v
        names={}
        for p in (cache/"artifacts").iterdir():names.setdefault(p.name.split(".",1)[0],[]).append(p)
        chosen=set();entries={};traces={}
        for source in closure["sources"]:
            p=ROOT/".lake/build/lib/lean"/Path(source).with_suffix(".trace");d=json.loads(p.read_text());k=d["depHash"];v=d["outputs"]
            require(mappings.get(k)==v,"trace/cache input mapping mismatch");entries[k]=v;traces[source]=dict(trace_sha256=sha(p),depHash=k,outputs=v)
            for val in v.values():
                for h in val if isinstance(val,list) else [val]:
                    require(str(h) in names,"missing cached output")
                    chosen.update(names[str(h)])
        out.mkdir();(out/"artifacts").mkdir();(out/"inputs").mkdir()
        for p in sorted(chosen):
            st=p.lstat();require(stat.S_ISREG(st.st_mode) and st.st_uid==os.getuid(),"cache artifact must be owned regular file")
            dst=out/"artifacts"/p.name;shutil.copyfile(p,dst);require(sha(p)==sha(dst) and p.stat().st_size==st.st_size and p.stat().st_mtime_ns==st.st_mtime_ns,"cache artifact changed during copy")
    (out/"inputs/solidity-lean.jsonl").write_text("".join(json.dumps([k,v],separators=(",",":"))+"\n" for k,v in sorted(entries.items())))
    payload={str(p.relative_to(out)):sha(p) for p in out.rglob("*") if p.is_file()}
    gates={}
    required={"h35-owned-build.log.json","h35-axiom-mcp.log.json","h35-controls-mcp.log.json","h35-graph-controls-mcp.log.json","h35-compiler-controls.log.json","h35-acceptance-controls.log.json"}
    for p in sorted((AREA/"evidence").glob("h35-*.log.json")):
        r=json.loads(p.read_text())
        if p.name in required:
            require(r["exit"]==0 and not r["pressure_stop"] and not r["interrupted"],"required VM gate failed")
            require(r["memory_limit_bytes"]==12884901888 and r["swap_limit_bytes"]==0 and r["minimum_parent_available_bytes"]>=4*1024**3,"VM gate resource drift")
            require(sha(p.with_suffix(""))==r["log_sha256"],"VM gate log drift")
            for source,pin in r["input_hashes"].items():require(sha(ROOT/source)==pin,"VM gate source snapshot drift")
        gates[p.name]=dict(receipt_sha256=sha(p),exit=r["exit"],command=r["command"],log_sha256=r["log_sha256"])
    require(required<=set(gates),"missing required H35 gate receipt")
    m=dict(head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),toolchain=(ROOT/"lean-toolchain").read_text().strip(),roots=closure["roots"],source_hashes={p:v["sha256"] for p,v in closure["sources"].items()},traces=traces,payload_sha256=payload,gates=gates)
    (out/"cache-manifest.json").write_text(json.dumps(m,indent=2)+"\n")
    with tarfile.open(out/"cache.tar.gz","w:gz",compresslevel=6) as t:
        for p in sorted(payload):t.add(out/p,arcname=p,recursive=False)
        t.add(out/"cache-manifest.json",arcname="cache-manifest.json",recursive=False)
    r=dict(shipping_status="prepared_not_shipped",head=m["head"],owned_modules=len(closure["roots"]),closure_modules=len(traces),artifacts=len(chosen),artifact_bytes=sum(p.stat().st_size for p in chosen),archive_sha256=sha(out/"cache.tar.gz"),manifest_sha256=sha(out/"cache-manifest.json"),preparer_sha256=sha(Path(__file__)),elapsed_seconds=time.monotonic()-start)
    (out/"receipt.json").write_text(json.dumps(r,indent=2)+"\n")
    (out/"README.md").write_text("Prepared on the lane VM; NOT SHIPPED. Verify SHA256SUMS and archive contents before import.\nArtifacts and input-to-output mappings retain Lake content-addressed names. Run prepare-cache.py --verify from the producing checkout/build to check semantic metadata against its pinned sources/traces/gates; on another machine use transport checksums pending coordinator import validation. Import mappings only under Lake's input-map flock and only after their outputs are installed and verified. Never overwrite existing artifacts. The receiving coordinator must supply the actual import/transfer receipt.\n")
    files=sorted(p for p in out.rglob("*") if p.is_file());(out/"SHA256SUMS").write_text("".join(sha(p)+"  "+str(p.relative_to(out))+"\n" for p in files))
    verify(out)
    for p in out.rglob("*"):
        if p.is_file():p.chmod(0o444)
    for p in sorted([p for p in out.rglob("*") if p.is_dir()],key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
    out.chmod(0o555);return r

def main():
    ap=argparse.ArgumentParser(description=__doc__);g=ap.add_mutually_exclusive_group(required=True);g.add_argument("--out");g.add_argument("--verify");ap.add_argument("--self-test",action="store_true");ap.add_argument("--cache",default="/workspace/.setup/cache/lake");a=ap.parse_args()
    if a.verify:r=verify(Path(a.verify).resolve())
    else:
        with Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock").open("a") as writer,(AREA/".artifacts/lake-serial.lock").open("a") as serial:
            fcntl.flock(writer,fcntl.LOCK_EX|fcntl.LOCK_NB);fcntl.flock(serial,fcntl.LOCK_EX|fcntl.LOCK_NB);r=prepare(Path(a.out).resolve(),Path(a.cache).resolve())
    if a.self_test:r={**r,"negative_controls_rejected":negative_controls(Path(a.verify or a.out).resolve())}
    print(json.dumps(r,indent=2))
if __name__=="__main__":main()
