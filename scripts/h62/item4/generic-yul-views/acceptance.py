#!/usr/bin/env python3
"""Static deterministic acceptance. Does NOT claim Lean or runtime gate pass."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import census
from verify_manifest import verify as verify_manifest_files

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def run(argv, root):
    result = subprocess.run(argv, cwd=root, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{argv!r} exit {result.returncode}: {result.stderr}{result.stdout}")
    return dict(command=argv, exit=result.returncode, stdout=result.stdout, stderr=result.stderr)

def verify_inputs(inputs):
    """Verify local input identities, not coordinator origin or semantic coverage."""
    class DigestPairs(list):
        # Preserve duplicate object keys for the shared path/identity verifier.
        pass

    pairs = json.loads((inputs / "sha256.json").read_text(), object_pairs_hook=DigestPairs)
    if not isinstance(pairs, DigestPairs):
        raise ValueError("input digest manifest must be a JSON object")
    return verify_manifest_files(inputs, dict(schema_version=1, files=[
        dict(path=name, sha256=digest) for name, digest in pairs]))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    args = ap.parse_args()
    root, evidence = args.root.resolve(), args.evidence.resolve()
    if evidence.is_relative_to(root): raise SystemExit("bulk evidence must be outside git checkout")
    evidence.mkdir(parents=True, exist_ok=True)
    checks = []
    verified_inputs = verify_inputs(args.inputs)
    checks.append(dict(command="verify coordinator input SHA256 manifest", exit=0, files=verified_inputs))
    checks.append(run([sys.executable, str(Path(__file__).with_name("test_census.py"))], root))
    checks.append(run([sys.executable, str(Path(__file__).with_name("test_bounded.py"))], root))
    data = census.scan(root)
    tree = subprocess.check_output(["git", "ls-tree", "-rz", BASE, "--", "Solidity/Yul/Views/"], cwd=root)
    originals = {}
    for entry in tree.split(b"\0"):
        if not entry: continue
        meta, name = entry.split(b"\t", 1)
        originals[name.decode()] = meta.split()[2].decode()
    if set(originals) != {f["path"] for f in data["files"]}:
        raise RuntimeError("original file universe changed")
    for name, blob in originals.items():
        raw = (root/name).read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if actual != blob: raise RuntimeError("owned original changed: " + name)
    checks.append(dict(command="compare every Views file blob and file universe to pinned base", exit=0, files=len(originals)))
    encoded = (json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()
    (evidence/"census.json").write_bytes(encoded)
    cmd = [sys.executable, str(Path(__file__).with_name("census.py")), "--root", str(root),
        "--verify", str(evidence/"census.json"), "--output", str(evidence/"census-reproduced.json")]
    checks.append(run(cmd, root))
    for p in (root/"tests/h62/item4/generic-yul-views").glob("*.lean"):
        code = census.mask(p.read_text())
        if re.search(r"\b(?:sorry|axiom|native_decide|ofReduceBool)\b|set_option\s+(?:maxHeartbeats|debug.skipKernelTC)", code):
            raise RuntimeError("forbidden proof shortcut: " + str(p))
    checks.append(dict(command="lexical proof shortcut/budget scan of additive Lean files", exit=0))
    result = dict(status="STATIC_ACCEPTANCE_PASS", boundary="external tests and source identity only; Lean proofs, all refusal coverage, full gates and timings pending", checks=checks, summary=data["summary"], census_sha256=hashlib.sha256(encoded).hexdigest())
    (evidence/"static-acceptance.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__": main()
