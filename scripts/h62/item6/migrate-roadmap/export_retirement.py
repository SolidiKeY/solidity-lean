#!/usr/bin/env python3
"""Export an already committed, clean retirement snapshot; no Lean or network."""
import hashlib
import fcntl
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
BRANCH = "codex/solidity-h62-6-20261106/migrate-roadmap"
SOURCE = ROOT / "tests/h62/item6/migrate-roadmap/retirement"
EVIDENCE = Path("/workspace/migrate-roadmap-evidence")
OUT = EVIDENCE / "h82-retirement"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert git("branch", "--show-current").decode().strip() == BRANCH
    assert not git("status", "--porcelain"), "Commit all task work before exporting"
    git("merge-base", "--is-ancestor", BASE, "HEAD")
    assert not git("diff", BASE, "HEAD", "--", "Solidity", "lean-toolchain"), "Production changed"
    head = git("rev-parse", "HEAD").decode().strip()
    OUT.mkdir(exist_ok=True)
    assert not (OUT / "HANDOFF.json").exists(), "Never overwrite a sealed handoff"
    for path in SOURCE.iterdir():
        if path.is_file():
            (OUT / path.name).write_bytes(git("show", head + ":" + str(path.relative_to(ROOT))))
    (OUT / "original.patch").write_bytes(git("format-patch", "--stdout", BASE + ".." + head))
    (OUT / "cumulative.diff").write_bytes(git("diff", "--binary", BASE, head))
    bundle = OUT / "migrate-roadmap-final.bundle"
    git("bundle", "create", str(bundle), BRANCH, "^" + BASE)
    verify = subprocess.run(["git", "bundle", "verify", str(bundle)], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / "bundle-verify.log").write_bytes(verify.stdout)
    assert verify.returncode == 0
    prior = [EVIDENCE / x for x in ["SHA256SUMS", "h70/SHA256SUMS",
             "h70-contracts-producer/SHA256SUMS", "h71-contracts-producer/SHA256SUMS"]]
    index = [{"manifest": str(x), "sha256": digest(x), "bulk_evidence_preserved_in_place": True}
             for x in prior]
    (OUT / "evidence-index.json").write_text(json.dumps(index, indent=2) + "\n")
    report = json.loads((SOURCE / "RETIREMENT.json").read_text())
    report.update({"head": head, "worktree_clean": True, "writer_lock_held_during_export": True, "worker_stopped_acknowledgement": True,
        "historical_gates": str(OUT / "historical-gates.json"),
        "integration_responsibility": "Successor integrates this exact final head; no automatic worker continuation",
        "reviews": json.loads((OUT / "reviews.json").read_text()),
        "checks": json.loads((OUT / "checks.json").read_text()),
        "artifacts": {"original_patch": str(OUT / "original.patch"),
                      "cumulative_diff": str(OUT / "cumulative.diff"),
                      "bundle": str(bundle), "handoff": str(OUT / "HANDOFF.json"),
                      "evidence": str(EVIDENCE), "checksums": str(OUT / "SHA256SUMS"),
                      "assignment": str(OUT / "original-assignment.txt"),
                      "queue": str(OUT / "original-work-and-backfill-queue.txt"),
                      "scope": str(OUT / "scope-manifest.json")}})
    assert git("rev-parse", "HEAD").decode().strip() == head
    assert git("branch", "--show-current").decode().strip() == BRANCH
    assert not git("status", "--porcelain"), "Worktree changed during export"
    (OUT / "HANDOFF.json").write_text(json.dumps(report, indent=2) + "\n")
    files = sorted(x for x in OUT.rglob("*") if x.is_file() and x.name != "SHA256SUMS")
    (OUT / "SHA256SUMS").write_text("".join(digest(x) + "  " + str(x) + "\n" for x in files))
    print(json.dumps({"head": head, "clean": True, "files": len(files),
                      "manifest_sha256": digest(OUT / "SHA256SUMS"),
                      "handoff": str(OUT / "HANDOFF.json")}, indent=2))


if __name__ == "__main__":
    with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        main()
