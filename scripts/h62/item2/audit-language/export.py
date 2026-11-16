#!/usr/bin/env python3
"""Export a committed checkpoint, with an opt-in private historical reader v2.

Use --interface-version 2 --historical-input-root DIR to read the exact request
from private archive fa68e0ac599d1f6a59dab0af5b19dbf2ae029c9f. DIR is external
and contains tests/h62/...; no download or fallback occurs. The request is
historical report data, not current authority or proof. V1 remains the default.
"""
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

def export(output, *, owner_request=None):
    """Keep the v1 export guards; v2 may supply authenticated historical data."""
    args = argparse.Namespace(output=output)
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
               "requests": [owner_request if owner_request is not None else json.loads((ROOT / "tests/h62/item2/audit-language/owner-resolution-request.json").read_text())],
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



REQUEST = "tests/h62/item2/audit-language/owner-resolution-request.json"
REQUEST_BYTES = 1477
REQUEST_SHA256 = "45666be1711a6b63c303b3fe9d3bfa04e1bf4e349f07a56a202144ba3feda41d"


def load_historical_request(directory):
    root = directory.resolve()
    if root.is_relative_to(ROOT.resolve()):
        raise ValueError("Historical input root must be outside the repository")
    path = (root / REQUEST).resolve(strict=True)
    if not path.is_relative_to(root):
        raise ValueError("Historical request escapes its input root")
    raw = path.read_bytes()
    if len(raw) != REQUEST_BYTES or hashlib.sha256(raw).hexdigest() != REQUEST_SHA256:
        raise ValueError("Historical request checksum mismatch: " + REQUEST)
    return json.loads(raw)



def export_v2(output, historical_input_root):
    """Use only pinned private historical request data; retain v1 export guards."""
    export(output, owner_request=load_historical_request(historical_input_root))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--interface-version", type=int, choices=(1, 2), default=1)
    p.add_argument("--historical-input-root", type=Path)
    args = p.parse_args()
    if args.interface_version == 2:
        if args.historical_input_root is None:
            p.error("v2 requires --historical-input-root")
        export_v2(args.output, args.historical_input_root)
    else:
        if args.historical_input_root is not None:
            p.error("--historical-input-root requires --interface-version 2")
        export(args.output)


if __name__ == "__main__":
    main()
