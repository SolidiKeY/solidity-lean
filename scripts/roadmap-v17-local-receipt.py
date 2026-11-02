#!/usr/bin/env python3
"""Bounded auditor-capsule intake. Failure accounting is not native proof authentication."""
import base64
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import zlib

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("receipt_packets",ROOT/"scripts/roadmap-v17-packets.py")
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
CAPSULE_SHA="fa950fce1a634b69c5dc5d4ffb534b14542181bc9cdc8458fc2240aae6147c5d"
LIMIT=200*1024
FLAGS={"kernelValidated":False,"selectorsAuthenticated":False,"replayVerified":False,
       "semanticPremisesDischarged":False,"releaseClosed":False}
sha=lambda data:hashlib.sha256(data).hexdigest()


def physical_headers(raw):
    """Reject hidden GNU/link/sparse extensions before tarfile resolves metadata."""
    offset=0;count=0
    while offset<len(raw):
        block=raw[offset:offset+512]
        p.require(len(block)==512,"truncated physical header")
        if not any(block):
            p.require(len(raw)-offset>=1024 and not any(raw[offset:]),"bad physical end blocks")
            return
        header=tarfile.TarInfo.frombuf(block,"utf-8","strict")
        count+=1;p.require(count<=64,"physical header bound")
        p.require(header.type in (tarfile.REGTYPE,tarfile.AREGTYPE,tarfile.XHDTYPE,tarfile.XGLTYPE),
                  "non-PAX capsule extension")
        p.require(0<=header.size<=LIMIT,"physical member bound")
        data=raw[offset+512:offset+512+header.size]
        p.require(len(data)==header.size,"truncated physical body")
        if header.type in (tarfile.XHDTYPE,tarfile.XGLTYPE):
            cursor=0;seen=set()
            while cursor<len(data):
                end=data.find(b" ",cursor);p.require(end>cursor,"PAX length syntax")
                digits=data[cursor:end]
                p.require(digits.isdigit() and not digits.startswith(b"0"),"PAX length syntax")
                length=int(digits);record=data[cursor:cursor+length]
                p.require(length>len(digits)+2 and len(record)==length and record.endswith(b"\n"),"truncated PAX record")
                key,sep,_=record[len(digits)+1:-1].partition(b"=")
                p.require(sep and key in (b"mtime",b"atime",b"ctime") and key not in seen,"unsupported PAX key")
                seen.add(key);cursor+=length
        offset+=512+((header.size+511)//512)*512
    raise ValueError("missing physical end blocks")


def capsule(raw,expected_sha=CAPSULE_SHA):
    p.require(len(raw)<=LIMIT and sha(raw)==expected_sha,"capsule size/hash mismatch")
    decoder=zlib.decompressobj(16+zlib.MAX_WBITS);unpacked=decoder.decompress(raw,LIMIT+1)
    p.require(len(unpacked)<=LIMIT and decoder.eof and not decoder.unused_data
              and not decoder.unconsumed_tail,"capsule raw bound/truncation/trailing data")
    p.require(len(unpacked)%512==0,"truncated TAR blocks")
    physical_headers(unpacked)
    members={};total=0
    with tarfile.open(fileobj=io.BytesIO(unpacked),mode="r:") as archive:
        for member in archive:
            p.safe_path(member.name)
            p.require(member.isfile() and member.type in (tarfile.REGTYPE,tarfile.AREGTYPE)
                      and not member.issparse(),"nonregular capsule payload")
            p.require(set(member.pax_headers)<={"mtime","atime","ctime"},"unsupported PAX override")
            p.require(bool(member.pax_headers) or member.offset_data==member.offset+512,
                      "unsupported extended capsule header")
            p.require(member.name not in members and len(members)<16,"duplicate/extra capsule member")
            p.require(0<=member.size<=LIMIT,"member bound");total+=member.size
            p.require(total<=LIMIT,"total member bound")
            data=archive.extractfile(member).read(member.size+1)
            p.require(len(data)==member.size,"truncated capsule member")
            members[member.name]=data
        end=archive.offset
    p.require(len(unpacked)-end>=1024 and not any(unpacked[end:]),"missing end blocks/trailing TAR data")
    p.require(len(members)==16 and "SHA256SUMS" in members,"wrong capsule member set")
    manifest={}
    for line in members["SHA256SUMS"].decode("ascii").splitlines():
        p.require(len(line)>=67 and line[64:66] in ("  "," *"),"checksum manifest syntax")
        digest,name=line[:64],line[66:];p.safe_path(name)
        p.require(p.SHA.fullmatch(digest) and name not in manifest and name!="SHA256SUMS","duplicate/invalid checksum claim")
        manifest[name]=digest
    p.require(set(manifest)==set(members)-{"SHA256SUMS"},"checksum member set mismatch")
    for name,digest in manifest.items():p.require(sha(members[name])==digest,"corrupt capsule payload: "+name)
    return {"capsuleSha256":sha(raw),"memberSha256":{n:sha(b) for n,b in members.items()},
            "rawTarBytes":len(unpacked),"payloadBytes":total,"byteIntegrityVerified":True,**FLAGS},members


def main():
    import argparse,fcntl,resource,signal
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError("metadata deadline")))
    signal.alarm(60)
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--capsule",type=Path);group.add_argument("--base64",type=Path)
    parser.add_argument("--out",type=Path,required=True);args=parser.parse_args()
    try:
        lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        p.require(args.out.is_absolute() and args.out.resolve()==args.out and not args.out.exists()
                  and not args.out.is_relative_to(ROOT),"new external evidence directory")
        if args.base64:
            text=p.stable_read(args.base64,2*LIMIT)
            raw=base64.b64decode(b"".join(text.split()),validate=True)
        else:raw=p.stable_read(args.capsule,LIMIT)
        receipt,members=capsule(raw)  # Production has no caller-controlled self-derived expected hash.
        args.out.mkdir();payload=args.out/"payload";payload.mkdir()
        for name,body in members.items():
            path=payload/name;path.parent.mkdir(parents=True,exist_ok=True)
            p.require(path.resolve()==path and not path.exists(),"extraction collision")
            path.write_bytes(body)
        receipt.update(status="CAPSULE_BYTES_ONLY_NORMALIZER_PENDING",nativeReceiptAccepted=False,
                       historicalRunnerAuthenticated=False)
        (args.out/"INTAKE.json").write_text(json.dumps(receipt,indent=2)+"\n")
        print(json.dumps(receipt));return 2
    except (ValueError,TypeError,OSError,EOFError,tarfile.TarError,zlib.error,MemoryError,TimeoutError) as error:
        print(json.dumps({"status":"NONPASS","error":str(error),"byteIntegrityVerified":False,**FLAGS}));return 2


if __name__=="__main__":raise SystemExit(main())
