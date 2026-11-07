#!/usr/bin/env python3
"""Exact additive-source preservation; not a kernel or family-migration gate."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
import census
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MODULE = "Solidity/Backend/StorageOps/OperationFamilies.lean"
START = "/-- Concatenation executes the original partial scheduler"
END = "/-- One partial operation commutes with an entire family"
def verify(original, current):
    if not isinstance(original, bytes) or not isinstance(current, bytes):
        raise ValueError("raw bytes required")
    start, end = START.encode(), END.encode()
    if current.count(start) != 1 or current.count(end) != 1:
        raise ValueError("ambiguous additive packet")
    a, b = current.index(start), current.index(end)
    if a >= b or current[:a] + current[b:] != original:
        raise ValueError("original source changed")
    old = {d["name"]:d for d in census.declarations(original.decode("utf-8"), MODULE)}
    new = {d["name"]:d for d in census.declarations(current.decode("utf-8"), MODULE)}
    added = "Solidity.Backend.StorageOps.modifyMany_append"
    if set(new) - set(old) != {added} or not set(old) <= set(new):
        raise ValueError("unexpected declaration delta")
    if any(new[n]["statement_sha256"] != d["statement_sha256"] for n,d in old.items()):
        raise ValueError("original statement changed")
    if re.search(r"\b(?:axiom|sorry|admit|native_decide|set_option)\b", census.mask(current[a:b].decode("utf-8"))):
        raise ValueError("forbidden additive packet token")
    return {"base":BASE,"module":MODULE,"original_declarations":len(old),
            "added_theorem":added,"existing_source_without_addition_identical":True,
            "original_sha256":hashlib.sha256(original).hexdigest(),
            "candidate_sha256":hashlib.sha256(current).hexdigest(),
            "boundary":"Source preservation only; kernel, axioms, timings and full family correspondence are separate."}
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--output",type=Path,required=True);args=ap.parse_args()
    root=Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
    if args.output.resolve().is_relative_to(root):ap.error("bulk output must stay outside checkout")
    original=subprocess.check_output(["git","show",BASE+":"+MODULE],cwd=root)
    report=verify(original,(root/MODULE).read_bytes())
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print("ADDITIVE_SOURCE_PRESERVATION_PASS")
if __name__ == "__main__":main()
