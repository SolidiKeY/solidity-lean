#!/usr/bin/env python3
"""Seal a compacted, accepted H28 run: `runs/<run>/seal.json`.

The seal lists the sha256 of the inputs and outputs the run's verdicts rest
on: the manifest and the frozen manifest it extends, every committed tool and
oracle of the lane, the production inputs and the proof oracle, every Lean
module in the import closure of the targets and oracles (on which the reuse
of earlier diagnostics depends), the full-record archives of the runs whose
diagnostics were reused, and the run's summary, acceptance record, compact
records and full-record archive.  The Lean toolchain itself is named by
`lean-toolchain`, which is hashed too.  It
refuses a run whose acceptance is not `scope_complete`, a dirty input, or a
summary whose archive digest does not match.  `--verify` recomputes every
digest of an existing seal.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

LANE = "tests/h28-sol/mutation-testing"


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def files(repo, run):
    manifest = json.loads((repo / LANE / "manifests/h28-final.json").read_text())
    names = [LANE + "/manifests/h28-final.json", manifest["base_manifest"]["path"]]
    names += sorted(subprocess.check_output(["git", "ls-files", LANE + "/tools", LANE + "/oracles"],
                                            cwd=repo, text=True).split())
    names += sorted(manifest["production_inputs"]) + sorted(manifest["oracle_sha256"])
    names += closure(repo, ["Solidity/Calculus/Rules.lean", "Solidity/Calculus/CallbackRules.lean",
                      "Solidity/Calculus/Taclet.lean"] +
                     [n for n in names if n.startswith(LANE + "/oracles/")])
    names += ["lean-toolchain"]
    rel = run.relative_to(repo)
    summary = json.loads((run / "summary.json").read_text())
    names += sorted(f"{rel.parent}/{r}-checks-full.tar.gz" for r in summary.get("reuse") or []
                    if (repo / rel.parent / f"{r}-checks-full.tar.gz").exists())
    names += [f"{rel}/summary.json", f"{rel}/acceptance.json", f"{rel}/checks.jsonl",
              f"{rel.parent}/{rel.name}-checks-full.tar.gz"]
    return names


def closure(repo, roots):
    """Every repository module imported, transitively, by the given files."""
    import re
    seen, todo = [], []
    for r in roots:
        todo += re.findall(r"^import (\S+)", (repo / r).read_text(), re.M)
    while todo:
        m = todo.pop()
        p = m.replace(".", "/") + ".lean"
        if p in seen or not (repo / p).exists():
            continue
        seen.append(p)
        todo += re.findall(r"^import (\S+)", (repo / p).read_text(), re.M)
    return sorted(seen)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--verify", action="store_true")
    a = ap.parse_args()
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    run = Path(a.run).resolve()
    if a.verify:
        seal = json.loads((run / "seal.json").read_text())
        # H44: a bulk file kept off Git may be absent; it then must carry the
        # sealed digest in runs/BULK.json (`tools/bulk.py restore` brings it
        # back, verified, for a full check)
        bulkm = repo / LANE / "runs/BULK.json"
        bulk = json.loads(bulkm.read_text())["files"] if bulkm.exists() else {}
        bad, absent = [], []
        for n, h in seal["sha256"].items():
            if not (repo / n).exists():
                (absent if bulk.get(n, {}).get("sha256") == h else bad).append(n)
            elif sha(repo / n) != h:
                bad.append(n)
        print(json.dumps({"verified": not bad, "files": len(seal["sha256"]), "present_verified":
                          len(seal["sha256"]) - len(bad) - len(absent), "bulk_absent": absent,
                          "mismatch": bad}, indent=1))
        sys.exit(1 if bad else 0)
    acceptance = json.loads((run / "acceptance.json").read_text())
    if not acceptance["scope_complete"]:
        raise SystemExit("refusing to seal: not scope_complete")
    summary = json.loads((run / "summary.json").read_text())
    archive = run.parent / (run.name + "-checks-full.tar.gz")
    if summary.get("full_records", {}).get("sha256") != sha(archive):
        raise SystemExit("refusing to seal: archive digest differs from summary")
    names = list(dict.fromkeys(files(repo, run)))
    mine = str(run.relative_to(repo))
    dirty = subprocess.run(["git", "status", "--porcelain", "--"] + [n for n in names if not n.startswith(mine)],
                           cwd=repo, capture_output=True, text=True).stdout.strip()
    if dirty:
        raise SystemExit("refusing to seal: inputs not committed:\n" + dirty)
    seal = {"run": run.name, "run_head": summary["head"], "manifest_sha256": summary["manifest_sha256"],
            "scope_complete": True, "sealed_at_head": subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
            "sha256": {n: sha(repo / n) for n in names}}
    (run / "seal.json").write_text(json.dumps(seal, indent=1) + "\n")
    print(json.dumps({k: v for k, v in seal.items() if k != "sha256"} | {"files": len(names)}, indent=1))


if __name__ == "__main__":
    main()
