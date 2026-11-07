#!/usr/bin/env python3
"""Deterministic source/proposal acceptance; never labels pending proofs done."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import census as c
from propose import proposal


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output == c.ROOT or c.ROOT in output.parents:
        raise SystemExit("H44: acceptance output belongs off git")
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    tests = subprocess.run([sys.executable, str(Path(__file__).with_name("test_census.py"))], env=env, capture_output=True, text=True)
    (output/"tests.log").write_text(tests.stdout+tests.stderr)
    if tests.returncode:
        raise SystemExit(tests.returncode)
    timings = subprocess.run([sys.executable, str(Path(__file__).with_name("test_measure.py"))], env=env, capture_output=True, text=True)
    (output/"timing-tests.log").write_text(timings.stdout+timings.stderr)
    if timings.returncode:
        raise SystemExit(timings.returncode)
    frozen, live = c.census(c.BASE), c.census()
    if frozen != live or c.seal(frozen) != json.loads(c.DEST.read_text()):
        raise SystemExit("frozen inventory mismatch")
    first, first_rows = proposal()
    second, second_rows = proposal()
    if first != second or first_rows != second_rows:
        raise SystemExit("non-deterministic proposal")
    patchpath = output/"proposed-owner.patch"
    patchpath.write_text(first)
    command = ["git", "apply", "--check", str(patchpath)]
    check = subprocess.run(command, cwd=c.ROOT, capture_output=True, text=True)
    (output/"patch-check.log").write_text("command="+repr(command)+"\nexit="+str(check.returncode)+"\n"+check.stdout+check.stderr)
    if check.returncode:
        raise SystemExit(check.returncode)
    # Confirm the read-only check changed no original source bytes.
    if c.census() != frozen:
        raise SystemExit("original files changed")
    helper = c.ROOT/"tests/h62/item4/generic-structuredflow/GenericMapped.lean"
    hidden = c.mask(helper.read_text())
    import re
    if re.search(r"\b(sorry|axiom|native_decide|ofReduceBool|maxHeartbeats)\b", hidden):
        raise SystemExit("forbidden proof shortcut/budget token in helper")
    result = dict(source_acceptance="PASS", semantic_acceptance="PENDING_DEPENDENCY", performance_acceptance="PENDING_DEPENDENCY_AND_OWNER", original_files=len(frozen["files"]),
                  original_declarations=len(frozen["declarations"]), controls_theorems=frozen["controls_counts"]["theorem"],
                  frozen_sha256=c.seal(frozen)["census_sha256"], patch_sha256=c.sha(first),
                  proposal_rows=first_rows, helper_sha256=hashlib.sha256(helper.read_bytes()).hexdigest(),
                  patch_applied=False, exact_owner_agreement=False, new_axioms="UNMEASURED (helper not compiled)",
                  source_forbidden_shortcuts=0)
    (output/"acceptance.json").write_text(json.dumps(result, sort_keys=True, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "proposal_rows"}, sort_keys=True))


if __name__ == "__main__":
    main()
