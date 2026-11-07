#!/usr/bin/env python3
"""Compare published Roadmap owner and isolated-overlay guard inputs read-only."""
import argparse, hashlib, json, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PATH = "Solidity/Roadmap/Contracts.lean"
GUARD = "#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.transfer"

def inspect(data):
    lines = data.decode("utf-8").splitlines()
    matches = [i for i, line in enumerate(lines) if line.strip() == GUARD]
    if len(matches) != 1:
        raise ValueError("expected exactly one literal transfer guard")
    index = matches[0]
    if index == 0:
        raise ValueError("transfer guard has no preceding line")
    return {"sha256": hashlib.sha256(data).hexdigest(), "guard_line": index + 1,
            "preceding_line": lines[index - 1], "guard_text": lines[index]}

def commit(value):
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise argparse.ArgumentTypeError("expected a full lowercase commit SHA")
    return value

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--overlay", type=commit, required=True)
    p.add_argument("--owner", type=commit, required=True)
    a = p.parse_args()
    rows = {}
    data = {}
    for label, rev in (("overlay", a.overlay), ("owner", a.owner)):
        subprocess.run(["git", "merge-base", "--is-ancestor", BASE, rev], check=True)
        data[label] = subprocess.check_output(["git", "show", rev + ":" + PATH])
        rows[label] = {"commit": rev, **inspect(data[label])}
    print(json.dumps({"method": "read-only exact Git blob comparison and literal guard context; not Lean validation, owner approval or evidence about unpublished work", "file": PATH, "identical_bytes": data["overlay"] == data["owner"], "inputs": rows}, indent=2))

if __name__ == "__main__": main()
