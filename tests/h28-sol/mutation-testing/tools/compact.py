#!/usr/bin/env python3
"""Compact a run directory's per-check records for Git (H44: bulk stays out).

Each `checks/<key>.json` becomes one line of `checks.jsonl` keeping the key,
phase, decision, timing, bridge exit, scratch and mutant hashes, the regions,
the one-change diff, the sha256 of the full record, every error/warning
location with its first 240 characters, and the `#print axioms` lines.  The
full records are then archived as `<run>-checks-full.tar.gz`, which
is committed beside it (small), with its sha256 in `summary.json`.
"""
import hashlib
import json
from pathlib import Path
import sys
import tarfile


def main(run):
    run = Path(run)
    lines = []
    for p in sorted((run / "checks").glob("*.json")):
        raw = p.read_bytes()
        r = json.loads(raw)
        diags = r.get("diagnostics") or []
        lines.append(json.dumps({
            "key": p.stem, "phase": r.get("phase"), "entry": r.get("entry"),
            "result": r.get("result"), "elapsed_s": r.get("elapsed_s"), "exit": r.get("exit"),
            "status": r.get("status"), "bridge": r.get("bridge"),
            "scratch_sha256": r.get("scratch_sha256"), "mutant_sha256": r.get("mutant_sha256"),
            "regions": r.get("regions_classified", r.get("regions")), "diff": r.get("diff"),
            "record_sha256": hashlib.sha256(raw).hexdigest(),
            "problems": [{"line": d["line"], "severity": d["severity"], "message": d["message"][:240]}
                         for d in diags if d["severity"] in ("error", "warning")][:12],
            "problem_count": sum(d["severity"] in ("error", "warning") for d in diags),
            "axioms": [d["message"] for d in diags if " axioms" in d["message"][:200] and d["severity"] == "info"],
        }, ensure_ascii=False, sort_keys=True))
    (run / "checks.jsonl").write_text("\n".join(lines) + "\n")
    archive = run.parent / (run.name + "-checks-full.tar.gz")
    with tarfile.open(archive, "w:gz") as t:
        t.add(run / "checks", arcname=run.name + "/checks")
    summary = json.loads((run / "summary.json").read_text())
    summary["full_records"] = {"archive": archive.name, "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
                               "files": len(lines), "in_git": True}
    (run / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(len(lines), "records;", archive.name, summary["full_records"]["sha256"])


if __name__ == "__main__":
    main(sys.argv[1])
