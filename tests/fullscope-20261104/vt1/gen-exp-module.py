#!/usr/bin/env python3
"""Writes Solidity/SolcValidation/IrExpHelpers.lean from fixtures/exp-helpers.yul
(the quoted text) and fixtures/exp-helpers.term (the parser's tree, printed by
IrLeanGen.lean), splitting the tree into named bodies. Nothing here is trusted:
the module's `expHelpers_certified` re-checks the tree against the text by
kernel evaluation. Usage: gen-exp-module.py [--check]
"""
import sys, pathlib
here = pathlib.Path(__file__).resolve().parent
root = here.parents[2]
text = (here / "fixtures/exp-helpers.yul").read_text()
term = (here / "fixtures/exp-helpers.term").read_text().strip()

def group(s, i):
    """The balanced parenthesised group starting at s[i] == '('."""
    assert s[i] == "("
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return s[i:j + 1], j + 1
    raise ValueError("unbalanced")

assert term.startswith("(.mk [")
sigs_end = term.index("] (.cons ")
sigs = term[len("(.mk "):sigs_end + 1]
rest_at = sigs_end + 2
bodies_term, after = group(term, rest_at)
items_term, _ = group(term, after + 1)
bodies = []
cur = bodies_term
while cur != ".nil":
    assert cur.startswith("(.cons ")
    b, k = group(cur, len("(.cons "))
    bodies.append(b)
    cur = cur[k + 1:-1]
names = ["CleanupU", "Panic11", "Shr1", "ExpHelper", "ExpUnsigned", "ExpU256"]
params = [(["value"], ["cleaned"]), ([], []), (["value"], ["newValue"]),
          (["_power", "_base", "exponent", "max"], ["power", "base"]),
          (["base", "exponent", "max"], ["power"]), (["base", "exponent"], ["power"])]
assert len(bodies) == len(names)

def strs(xs):
    return "[" + ", ".join(f'"{x}"' for x in xs) + "]"

def lean_str(s):
    assert all(ord(c) < 128 for c in s)
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'

out = f'''import Solidity.SolcValidation.IrParse
import Solidity.SolcValidation.IrEval

/-!
# solc's `checked_exp` helpers, as imported

`expHelpersText` is the verbatim text of six functions cut from the saved solc
0.8.38 `--ir` output of `Census` (`tests/fullscope-20261104/vt1/extract-helpers.py`):
`checked_exp_t_uint256_t_uint256` and everything it calls. The tree was printed
from the parser's output (`IrLeanGen.lean`) and split into named bodies
(`gen-exp-module.py`); `expHelpers_certified` re-checks it against the text by
kernel evaluation (`Parsed.sound`'s statement).
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

def expHelpersText : String :=
  {lean_str(text)}

def expSigs : List FnSig :=
  {sigs}

abbrev ExpBody (params rets : List String) :=
  Block (expSigs ++ []) ⟨true, false⟩ (params ++ rets)
'''
for n, (ps, rs), b in zip(names, params, bodies):
    out += f"\ndef exp{n} : ExpBody {strs(ps)} {strs(rs)} :=\n  {b}\n"
chain = ".nil"
for n in reversed(names):
    chain = f"(.cons exp{n} {chain})"
out += f'''
def expBodies : Bodies (expSigs ++ []) expSigs :=
  {chain}

def expItems : Items (expSigs ++ []) ⟨false, false⟩ [] expSigs.length :=
  {items_term}

def expHelpersCode : Code := .mk expSigs expBodies expItems

def expHelpersRoot : Object Code := .object "ExpHelpers" expHelpersCode []

/-- The generated tree carries the same certificate as a parse of the text. -/
theorem expHelpers_certified :
    lex expHelpersText = some (objectToks expHelpersRoot) ∧ objectWf expHelpersRoot = true := by
  decide +kernel

end Solidity.SolcValidation.IrSyntax
'''
target = root / "Solidity/SolcValidation/IrExpHelpers.lean"
if "--check" in sys.argv:
    if target.read_text() != out:
        sys.exit("IrExpHelpers.lean differs")
    print("EXP_MODULE_CHECK_PASS")
    sys.exit(0)
target.write_text(out)
print(target, len(out), "bytes")
