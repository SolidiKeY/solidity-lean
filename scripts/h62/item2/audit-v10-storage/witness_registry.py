#!/usr/bin/env python3
"""Frozen statement/witness reference accounting, not a Lean proof checker.
Exports the exact base to a temporary read-only-input fixture. The original
live census and its drift rejection remain unchanged. Bulk stays outside Git.
"""
import argparse
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile
from unittest import mock

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
spec=importlib.util.spec_from_file_location("frozen_census",HERE/"census.py")
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
MAP_DIR=ROOT/"tests/h62/item2/audit-v10-storage"

def digest(data): return hashlib.sha256(data).hexdigest()

def frozen_inventory(root=ROOT):
    original=subprocess.check_output
    archive=original(["git","archive",c.BASE,"--","docs/module-map/v10-storage.md",
        "Solidity/Backend/StorageOps","Solidity/Lowering/StorageOps"],cwd=root)
    with tempfile.TemporaryDirectory(prefix="h62-frozen-audit-") as temp:
        fixture=Path(temp)
        with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
            for member in tree.getmembers():
                if not member.isfile(): continue
                relative=Path(member.name)
                if relative.is_absolute() or ".." in relative.parts:
                    raise ValueError("unsafe frozen path")
                target=fixture/relative
                target.parent.mkdir(parents=True,exist_ok=True)
                target.write_bytes(tree.extractfile(member).read())
        def readonly_git(args,**kwargs):
            if args[0]!="git" or args[1] not in ("show","ls-tree"):
                raise ValueError("unexpected frozen reader command")
            return original(args,**dict(kwargs,cwd=root))
        # Only git's repository lookup is redirected. c.frozen still compares
        # EVERY fixture file byte-for-byte against the exact base's Git blob.
        with mock.patch.object(c.subprocess,"check_output",side_effect=readonly_git):
            return c.collect(fixture)

def maps(root=ROOT):
    directory=root/"tests/h62/item2/audit-v10-storage"
    return [(p,json.loads(p.read_text())) for p in sorted(directory.glob("*-witness-map.json"))]

def build(inventory,packets,root=ROOT):
    if inventory["base"]!=c.BASE: raise ValueError("inventory base mismatch")
    original={r["id"]:r for r in inventory["declarations"]}
    if len(original)!=len(inventory["declarations"]): raise ValueError("duplicate census row")
    directory=root/"tests/h62/item2/audit-v10-storage"
    pins=json.loads((directory/"kernel-source-pins.json").read_text())
    if pins["frozen_base"]!=c.BASE: raise ValueError("source-pin base mismatch")
    frozen_files={f["path"]:f["sha256"] for f in inventory["files"]}
    mapped={}; sources={}; packet_hashes={}
    for path,packet in packets:
        if packet["frozen_base"]!=c.BASE: raise ValueError("packet base mismatch")
        kind=packet.get("kind","joint-premise")
        if kind not in ("joint-premise","data-inhabitance"):raise ValueError("unknown witness kind")
        packet_hashes[str(path.relative_to(root))]=digest(path.read_bytes())
        for row in packet["rows"]:
            key=row["frozen_id"]
            if key in mapped: raise ValueError("duplicate witness row")
            if key not in original: raise ValueError("unknown frozen row")
            old=original[key]
            expected=frozen_files[old["path"]]
            if packet["frozen_module_sha256"]!=expected or digest((root/old["path"]).read_bytes())!=expected:
                raise ValueError("current frozen interface file drift")
            if row["signature"]!=old["signature"] or row["signature_sha256"]!=old["signature_sha256"]:
                raise ValueError("frozen signature drift")
            namespace,name=row["witness"].rsplit(".",1)
            matching=[]
            for source in sorted(directory.glob("*.lean")):
                text=source.read_text(); code=c.mask(text)
                if re.search(r"(?m)^namespace +"+re.escape(namespace)+r"\s*$",code) and re.search(r"(?m)^theorem +"+re.escape(name)+r"\b",code):
                    matching.append(source)
            if len(matching)!=1: raise ValueError("missing or duplicate witness declaration")
            source=matching[0]; relative=str(source.relative_to(root))
            observed=digest(source.read_bytes())
            if relative not in pins["sources"] or pins["sources"][relative]["sha256"]!=observed:
                raise ValueError("kernel-checked witness source drift")
            sources[relative]=observed
            mapped[key]=dict(row,witness_source=relative,witness_kind=kind)
    rows=[dict(id=r["id"],signature_sha256=r["signature_sha256"],context_sha256=r["context_sha256"],
          witness_reference=mapped.get(r["id"]),status="mapped-witness-reference" if r["id"] in mapped else "unmapped")
          for r in inventory["declarations"]]
    return dict(schema_version=1,frozen_base=c.BASE,
        boundary="Frozen source/signature/reference identity only. Kernel checks and manual semantic fidelity are separate; not a complete elaborated interface census or compiler totality proof.",
        counts=dict(conservative_rows=len(rows),mapped_rows=len(mapped),
          mapped_joint_bundles=sum(r["witness_kind"]=="joint-premise" for r in mapped.values()),
          mapped_data_inhabitants=sum(r["witness_kind"]=="data-inhabitance" for r in mapped.values()),
          unmapped=len(rows)-len(mapped)),
        witness_source_sha256=sources,packet_sha256=packet_hashes,rows=rows)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,required=True); args=ap.parse_args()
    output=args.output.resolve()
    if output.is_relative_to(ROOT):ap.error("bulk output must remain outside Git")
    result=build(frozen_inventory(),maps())
    output.mkdir(parents=True,exist_ok=True)
    (output/"witness-registry.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps(result["counts"],sort_keys=True))
if __name__=="__main__":main()
