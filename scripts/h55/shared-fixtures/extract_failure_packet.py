#!/usr/bin/env python3
"""Emit an unapplied owner proposal against the exact H55 base; no files are edited."""
import difflib
import pathlib
import subprocess
import sys

BASE = "4d3790eadb8a5212233bc7d5e345817476b2f590"
ROOT = pathlib.Path(__file__).resolve().parents[3]
FILES = [f"Solidity/Lowering/V08/{name}Controls.lean" for name in
         ("CreationSuccess", "Handler", "LibraryHandler", "Prefix")]
HELPER = "Solidity/Lowering/V08/SharedFailureFixture.lean"
OLD = """private theorem extract_failure {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) : run = .error halt := by
  cases run with
  | ok value => cases checked
  | error actual =>
    have same : actual = halt := Option.some.inj checked
    cases same
    rfl
"""
NEW = """import Solidity.Semantics.Run

/-! Shared failure extraction for V08 control fixtures. -/
namespace Solidity.Lowering.V08.SharedFailureFixture
open Solidity

theorem extract_failure {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) : run = .error halt := by
  cases run with
  | ok value => cases checked
  | error actual =>
    have same : actual = halt := Option.some.inj checked
    cases same
    rfl

end Solidity.Lowering.V08.SharedFailureFixture
"""

def diff(old, new, a, b):
    sys.stdout.writelines(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=a, tofile=b))

if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() != BASE and subprocess.run(
    ["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=ROOT, check=False
).returncode:
    raise SystemExit("base is not an ancestor")
if (ROOT / HELPER).exists():
    raise SystemExit("helper already exists; rebase proposal manually")
for path in FILES:
    original = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT, text=True)
    if (ROOT / path).read_text() != original or original.count(OLD) != 1:
        raise SystemExit(f"precondition failed: {path}")
    proposed = "import Solidity.Lowering.V08.SharedFailureFixture\n" + original.replace(OLD, "")
    proposed = proposed.replace("extract_failure", "Solidity.Lowering.V08.SharedFailureFixture.extract_failure")
    diff(original, proposed, f"a/{path}", f"b/{path}")
diff("", NEW, "/dev/null", f"b/{HELPER}")
