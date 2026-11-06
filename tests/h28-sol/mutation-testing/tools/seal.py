#!/usr/bin/env python3
"""Seal a compacted, accepted H28 run: `runs/<run>/seal.json`.

The seal lists the sha256 of every input and output the run's verdicts rest
on: the manifest and the frozen manifest it extends, every committed tool and
oracle of the lane, the production inputs and the proof oracle, the run's
summary, acceptance record, compact records and full-record archive.  It
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
    rel = run.relative_to(repo)
    names += [f"{rel}/summary.json", f"{rel}/acceptance.json", f"{rel}/checks.jsonl",
              f"{rel.parent}/{rel.name}-checks-full.tar.gz"]
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--verify", action="store_true")
    a = ap.parse_args()
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    run = Path(a.run).resolve()
    if a.verify:
        seal = json.loads((run / "seal.json").read_text())
        bad = [n for n, h in seal["sha256"].items() if sha(repo / n) != h]
        print(json.dumps({"verified": not bad, "files": len(seal["sha256"]), "mismatch": bad}, indent=1))
        sys.exit(1 if bad else 0)
    acceptance = json.loads((run / "acceptance.json").read_text())
    if not acceptance["scope_complete"]:
        raise SystemExit("refusing to seal: not scope_complete")
    summary = json.loads((run / "summary.json").read_text())
    archive = run.parent / (run.name + "-checks-full.tar.gz")
    if summary.get("full_records", {}).get("sha256") != sha(archive):
        raise SystemExit("refusing to seal: archive digest differs from summary")
    names = files(repo, run)
    dirty = subprocess.run(["git", "status", "--porcelain", "--"] + [n for n in names if not n.startswith(
        str(run.relative_to(repo)))], cwd=repo, capture_output=True, text=True).stdout.strip()
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
