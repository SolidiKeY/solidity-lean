#!/usr/bin/env python3
"""Apply the branch-only pilot object to an isolated exact-base source tree.

The prototype object must already exist locally (lane branch or private bundle).
This script deliberately contains no prototype Lean source.
"""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
BASE = "381328f608032dd19c405373c2b265e83a969850"
PROTOTYPE = "301b96ef901df6d67758de44b5f078a4f547ec8b"
FAMILY = "Solidity/Lowering/G19"

def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)

def main():
    if subprocess.run(["git", "cat-file", "-e", PROTOTYPE+"^{commit}"], cwd=ROOT, stderr=subprocess.DEVNULL).returncode:
        raise SystemExit("Prototype object required: retrieve the recorded lane commit/private bundle first")
    names = git("ls-tree", "-r", "--name-only", BASE, FAMILY).decode().splitlines()
    names = [n for n in names if n.endswith(".lean")]
    actual = {str(p.relative_to(ROOT)) for p in (ROOT/FAMILY).rglob("*.lean")}
    if actual != set(names):
        raise SystemExit("Refusing missing or unexpected family files")
    for n in names:
        if (ROOT/n).read_bytes() != git("show", BASE+":"+n):
            raise SystemExit("Refusing non-base source: "+n)
    changed = git("diff", "--name-only", BASE, PROTOTYPE).decode().splitlines()
    if not changed or any(not n.startswith(FAMILY+"/") for n in changed):
        raise SystemExit("Prototype commit exceeds its source-family boundary")
    patch = git("diff", "--binary", BASE, PROTOTYPE, "--", FAMILY)
    subprocess.run(["git", "apply", "--check", "-"], cwd=ROOT, input=patch, check=True)
    subprocess.run(["git", "apply", "-"], cwd=ROOT, input=patch, check=True)
    for n in names:
        if (ROOT/n).read_bytes() != git("show", PROTOTYPE+":"+n):
            raise SystemExit("Reproduction mismatch: "+n)
    print("Reproduced all 36 family files from the recorded branch-only prototype")

if __name__ == "__main__":
    main()
