#!/usr/bin/env python3
"""Export this isolated committed checkpoint; keep bulk evidence outside Git."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
BRANCH = "codex/solidity-h62-2-20261106/audit-language"

def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--output", type=Path, required=True)
args = p.parse_args()
args.output = args.output.resolve()
assert not args.output.is_relative_to(ROOT), "bulk export must be outside repository"
assert git("branch", "--show-current").decode().strip() == BRANCH
subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=ROOT, check=True)
assert not git("status", "--porcelain"), "commit the reviewable checkpoint first"
changed = git("diff", "--name-only", BASE, "HEAD").decode().splitlines()
assert changed, "do not create empty result-marker commits"
for path in changed:
    assert path.startswith(("tests/h62/item2/audit-language/", "scripts/h62/item2/audit-language/")) or path == "docs/feature-work/h62-2-audit-language.md", path
args.output.mkdir(parents=True, exist_ok=True)
(args.output / "original.patch").write_bytes(git("diff", "--binary", BASE, "HEAD"))
handoff = {"batch": "solidity-h62-2-20261106", "slug": "audit-language", "status": "blocked",
           "branch": BRANCH, "base": BASE, "head": git("rev-parse", "HEAD").decode().strip(),
           "environment_id": "ccarenv_b64_Y2NhcmVudl9hNTQ3YjYwNzYwNjA4MTkxOGJhYmM3MGZiMTJjYzk0Mw",
           "repository": str(ROOT), "goal": "existing launcher goal; never recreated; incomplete",
           "changed_paths": changed,
           "checkpoints": [{"name": "inventory", "status": "partial"},
                           {"name": "simultaneous-witnesses", "status": "partial"},
                           {"name": "compiler-totality", "status": "blocked"},
                           {"name": "statement-fidelity-census", "status": "partial"}],
           "completed_work_items": ["source-census-tooling", "catalog-feasibility", "lattice-arithmetic-joint-witnesses", "ABI-success-failure-backfill"],
           "additive_theorems": 37, "additive_lean_modules": 4,
           "versions": json.loads((args.output / "versions.json").read_text()),
           "reviews": json.loads((args.output / "reviews.json").read_text()),
           "static_gates": json.loads((args.output / "static-gates.json").read_text()),
           "focused_gates": str(args.output / "final-reviewed/checks.json"),
           "migration_gate_failures": json.loads((args.output / "migration-blockers.json").read_text()),
           "h70_baseline_source_classification": json.loads((args.output / "h70-classification-final/classification.json").read_text())["summary"],
           "h70_source_classification": json.loads((args.output / "h70-remaining-reviewed/classification.json").read_text())["summary"],
           "continuation_source_refinements": json.loads((args.output / "h70-remaining-reviewed/summary.json").read_text()),
           "continuation_overlay_review": json.loads((args.output / "h70-overlay-review-final/overlay-review.json").read_text()),
           "continuation_validation": json.loads((args.output / "h70-continuation-validation.json").read_text()),
           "continuation_reviews": json.loads((args.output / "h70-continuation-reviews.json").read_text()),
           "h70_generation_gate": json.loads((args.output / "h70-classification-gate.json").read_text()),
           "h70_reproduction_gate": json.loads((args.output / "h70-reproduction-gate.json").read_text()),
           "h70_reviews": json.loads((args.output / "h70-reviews.json").read_text()),
           "h70_validation": json.loads((args.output / "h70-validation.json").read_text()),
           "requests": [json.loads((ROOT / "tests/h62/item2/audit-language/owner-resolution-request.json").read_text())],
           "certificates": 12, "source_declarations": 4146, "uncovered_source_declarations": 4134,
           "frozen_statements_touched": [], "new_sorry": 0, "new_axiom_declarations": 0, "new_native_decide": 0,
           "timing_delta": None, "timing_limitation": "No comparable full-build baseline; no refactor of existing files",
           "blockers": json.loads((ROOT / "tests/h62/item2/audit-language/owner-tickets.json").read_text()),
           "questions": [],
           "artifacts": {"original_patch": str(args.output / "original.patch"),
                         "handoff": str(args.output / "handoff.json"), "evidence": str(args.output),
                         "checksums": str(args.output / "SHA256SUMS")}}
(args.output / "handoff.json").write_text(json.dumps(handoff, indent=2)+"\n")
# Hash bulk evidence deterministically without duplicating the extracted release
# and opaque compiled products. The archive itself and all proof logs are kept.
rows = []
for file in sorted(args.output.rglob("*")):
    if not file.is_file(): continue
    rel = file.relative_to(args.output)
    if rel.name == "SHA256SUMS" or "lib" in rel.parts: continue
    if rel.parts[0] == "toolchain" and len(rel.parts) > 1 and rel.parts[1] == "lean-4.35.0-linux": continue
    digest = hashlib.sha256(file.read_bytes()).hexdigest()
    rows.append(digest + "  " + str(rel))
(args.output / "SHA256SUMS").write_text("\n".join(rows)+"\n")
print(json.dumps({"head": handoff["head"], "changed_paths": len(changed), "hashed_artifacts": len(rows),
                  "patch_sha256": hashlib.sha256((args.output / "original.patch").read_bytes()).hexdigest()}))
