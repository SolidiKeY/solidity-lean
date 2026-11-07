#!/usr/bin/env python3
"""Portable archive positive/corruption controls with old workspace paths denied."""
import argparse,contextlib,gzip,hashlib,io,json,shutil,sys,tarfile
from pathlib import Path
from types import SimpleNamespace
import paired_evidence as pe

def add(tar,name,data):
    item=tarfile.TarInfo(name);item.size=len(data);item.mtime=0;tar.addfile(item,io.BytesIO(data))
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--archive",type=Path,required=True);ap.add_argument("--out",type=Path,required=True);a=ap.parse_args();archive=a.archive.resolve();out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
    preserved=out/"tested-input.tar.gz"
    if archive!=preserved:shutil.copyfile(archive,preserved)
    archive=preserved
    with archive.open("rb")as stream:input_sha=hashlib.file_digest(stream,"sha256").hexdigest()
    with tarfile.open(archive,mode="r|gz")as tar:
        index=json.loads(tar.extractfile(next(iter(tar))).read())
    targets={index["contexts"]["rebased"]["reports"][n]for n in("acceptance-snapshot.json","verified-payable.json")};targets.add(index["contexts"]["original"]["reports"]["mapped-module-dispositions.json"]);captured={};first=None
    with tarfile.open(archive,mode="r|gz")as tar:
        for member in tar:
            if member.name=="index.json":continue
            key=member.name[6:]
            if first is None:first=(key,tar.extractfile(member).read())
            elif key in targets:captured[key]=tar.extractfile(member).read()
    for key in targets:
        if first[0]==key:captured[key]=first[1]
    def small(path,obj,payload=None):
        with path.open("wb")as raw,gzip.GzipFile(filename="",fileobj=raw,mode="wb",mtime=0)as gz,tarfile.open(fileobj=gz,mode="w|")as tar:
            add(tar,"index.json",pe.canonical(obj))
            if payload:add(tar,"blobs/"+payload[0],payload[1])
    bad_blob=out/"corrupt-blob.tar.gz";raw=first[1];mutated=bytes([raw[0]^1])+raw[1:]if raw else b"x";small(bad_blob,index,(first[0],mutated))
    missing=json.loads(pe.canonical(index));olean=next(iter(missing["contexts"]["original"]["modules"].values()))["olean_blob"];del missing["blob_sizes"][olean];bad_olean=out/"missing-olean.tar.gz";small(bad_olean,missing)
    def rehash_case(name,report_name,change,label="rebased",index_change=None):
        obj=json.loads(pe.canonical(index));key=obj["contexts"][label]["reports"][report_name];report=json.loads(captured[key]);change(report);data=pe.canonical(report);new_key=pe.h(data)
        obj["contexts"][label]["reports"][report_name]=new_key;obj["blob_sizes"][new_key]=len(data)
        if index_change:index_change(obj)
        path=out/(name+".tar.gz")
        with path.open("wb")as raw,gzip.GzipFile(filename="",fileobj=raw,mode="wb",compresslevel=1,mtime=0)as gz,tarfile.open(fileobj=gz,mode="w|")as dest,tarfile.open(archive,mode="r|gz")as source:
            add(dest,"index.json",pe.canonical(obj))
            for member in source:
                if member.name!="index.json":dest.addfile(member,source.extractfile(member))
            add(dest,"blobs/"+new_key,data)
        return path
    counts=rehash_case("rehashed-snapshot-count","acceptance-snapshot.json",lambda report:report.__setitem__("joint_certificates",report["joint_certificates"]+1))
    def operational(report):
        row=next(r for r in report["declarations"]if r["source_name"]=="Solidity.Theory.Mutability.ContractWorld.World.enter_static");row["operational_refusal_coverage"]=True
    static=rehash_case("rehashed-static-row","verified-payable.json",operational)
    wrong=index["contexts"]["original"]["mapped_sources"]["Solidity/Theory/Typed/Obs.lean"]
    def mismatch(report):
        row=next(r for r in report["modules"]if r["file"]=="Solidity/Theory/Mutability/Pure.lean");row["current_source_sha256"]=wrong;row["original_source_sha256"]=wrong
    mapped=rehash_case("rehashed-mapped-source","mapped-module-dispositions.json",mismatch,label="original",index_change=lambda obj:obj["contexts"]["original"]["mapped_sources"].__setitem__("Solidity/Theory/Mutability/Pure.lean",wrong))
    cases=[("positive",archive,None),("corrupt-blob",bad_blob,"Blob integrity failure"),("missing-olean",bad_olean,"Referenced artifact missing from blob index"),("rehashed-snapshot-count",counts,"Snapshot/ledger counts mismatch"),("rehashed-static-row",static,"Static Payable row mismatch"),("rehashed-mapped-source",mapped,"Mapped/proof source mismatch")]
    allowed={p for _,p,_ in cases};rows=[]
    with contextlib.ExitStack()as stack:
        logs={name:stack.enter_context((out/(name+".log")).open("w"))for name,_,_ in cases};result=stack.enter_context((out/"portable-controls.json").open("w"))
        def audit(event,args):
            if event=="open"and isinstance(args[0],(str,bytes)):
                path=Path(args[0]).resolve()
                if str(path).startswith("/workspace/")and path not in allowed:raise RuntimeError("Old VM path access denied: "+str(path))
        sys.addaudithook(audit)
        for name,path,expected in cases:
            try:
                with contextlib.redirect_stdout(logs[name]):pe.verify(SimpleNamespace(archive=path))
            except AssertionError as err:
                assert expected is not None and expected in str(err),(name,str(err));logs[name].write("EXPECTED_REFUSAL: "+str(err)+"\n");status="refused"
            else:
                assert expected is None,name;status="pass"
            rows.append(dict(case=name,archive=str(path),result=status,expected_refusal=expected,old_VM_path_access="denied"))
        result.write(json.dumps(dict(input_archive_sha256=input_sha,preserved_input_archive=str(archive),cases=rows,old_VM_paths_opened=0,kernel_rerun=False,full_assignment_acceptance=False),indent=2)+"\n")
    print("PAIRED_PORTABLE_CONTROLS_PASS:positive+5refusals;old_VM_paths_denied;no_kernel_rerun")
if __name__=="__main__":main()
