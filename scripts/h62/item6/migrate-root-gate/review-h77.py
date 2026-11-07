#!/usr/bin/env python3
"""Recheck H77 receipts/content only; never imports or executes producer tools."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

# Static review must not create bytecode beside an imported checker.
sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[4]
RECEIPTS = {
    "9316e94cd180297bf36d6e31e9e3631b3d2dceac0a0c729611afa81b41f61392-HANDOFF.md": 17276,
    "dd67a6cbba9c5ab94715ae17ab28496722f7bceaed93bd1d222a7ee6c98fac9c-HANDOFF.md": 15154,
    "c00c6698be9c948b7a8df049784703fdb687bb2f02fcc6f71f63ac12a24d1e72-source-full.patch": 75555,
}

def review(inputs, h76):
    spec = importlib.util.spec_from_file_location("h76_review", ROOT/"scripts/h62/item6/migrate-root-gate/review-delivery.py")
    prior = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(prior)
    data, receipts = {}, []
    for name, size in RECEIPTS.items():
        raw = (inputs/name).read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        prior.require(digest == name.split("-")[0] and len(raw) == size, "H77 receipt mismatch: "+name)
        data[name] = raw
        receipts.append({"path": str(inputs/name), "sha256": digest, "bytes": size})
    full = data[next(name for name in data if name.endswith(".patch"))]
    prior_raw = (h76/"3f6f954038-hash-owner-overlay.patch").read_bytes()
    prior.require(hashlib.sha256(prior_raw).hexdigest() == "b07f36b08faf0244fd350a54c9d72e3f5c333a566726b1e7f420aa21b727ffec", "H76 scoped patch mismatch")
    sections = re.split(rb"(?=^diff --git )", full, flags=re.M)
    sections = [section for section in sections if section]
    names = [re.match(rb"diff --git a/(\S+) b/(\S+)\n", section) for section in sections]
    prior.require(all(m and m[1] == m[2] for m in names), "unsupported patch header")
    paths = [m[1].decode() for m in names]
    prior.require(len(paths) == len(set(paths)), "duplicate patch path")
    production = {path: section for path, section in zip(paths, sections) if path.startswith("Solidity/")}
    prior.require(set(production) == {"Solidity/Hash/Adaptive.lean", "Solidity/Hash/CollisionBound.lean"}, "unexpected production scope")
    scoped = b"".join(production.values())
    prior.require(scoped == prior_raw, "H77/H76 production patch differs")
    originals = {path: subprocess.check_output(["git", "show", prior.BASE+":"+path], cwd=ROOT) for path in production}
    images = prior.apply_in_memory(scoped.decode(), originals)
    manifest_raw = (h76/"300764ecfb-producer-overlay.json").read_bytes()
    prior.require(hashlib.sha256(manifest_raw).hexdigest() == "2ae88b9e70a54731ec61bc454abdd9b5204895c95b9ea5e25018d9b12bd4a910", "H76 manifest mismatch")
    manifest = json.loads(manifest_raw)
    files = []
    current = {path: (ROOT/path).read_bytes() for path in production}
    for row in manifest["files"]:
        path = row["path"]
        prior.require(hashlib.sha256(originals[path]).hexdigest() == row["base_sha256"], "base digest mismatch")
        prior.require(hashlib.sha256(images[path]).hexdigest() == row["head_sha256"], "postimage digest mismatch")
        prior.require(current[path] in (originals[path], images[path]), "current production differs from pinned or reviewed bytes")
        files.append(row)
    check = prior.check_patch_at_base(full)
    prior.require(check.returncode == 0, "full patch applicability: "+check.stderr.decode())
    for path, raw in current.items():
        prior.require((ROOT/path).read_bytes() == raw, "production changed during review")
    return {"schema_version": 1, "kind": "static H77 receipt and production-content review", "receipts": receipts,
            "base": prior.BASE, "reported_hash_source_head": manifest["head"],
            "reported_hash_handoff_head": "a3f49ee0ec1829e63022c90194048d5a1ffe0d22",
            "reported_syntax_handoff_head": "72441d298484976c48dd14b4e095c9149b852025",
            "patch_paths": paths, "files": files, "production_patch_matches_H76": True,
            "full_patch_git_apply_check_exit": check.returncode, "applicability_base": prior.BASE,
            "current_source_sha256": {path: hashlib.sha256(raw).hexdigest() for path, raw in current.items()},
            "git_ancestry_verified": False,
            "member_finality_verified": False, "member_stopped_acknowledgement_verified": False,
            "patch_applied": False, "Lean_started": False,
            "boundary": "Handoffs reviewed as historical producer reports; tooling paths listed, not executed or comprehensively audited. No full gate, generated API, axiom, timing, retirement or cut-over acceptance."}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", type=Path)
    parser.add_argument("h76", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    report = review(args.inputs.resolve(strict=True), args.h76.resolve(strict=True))
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
