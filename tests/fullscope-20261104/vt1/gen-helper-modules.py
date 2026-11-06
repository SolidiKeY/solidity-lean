#!/usr/bin/env python3
"""Writes the helper-group modules of Solidity/SolcValidation/ from their
fixtures: fixtures/<group>.yul (the quoted text) and fixtures/<group>.term (the
parser's tree, printed by IrLeanGen.lean), splitting the tree into named bodies.
Nothing here is trusted: each module's certificate re-checks the tree against
the text by kernel evaluation. Usage: gen-helper-modules.py [--check]
"""
import sys, pathlib, re
here = pathlib.Path(__file__).resolve().parent
root = here.parents[2]

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

def strs(xs):
    return "[" + ", ".join(f'"{x}"' for x in xs) + "]"

def lean_str(s):
    assert all(ord(c) < 128 for c in s)
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'

def module(fixture, prefix, obj, names, doc):
    text = (here / f"fixtures/{fixture}.yul").read_text()
    term = (here / f"fixtures/{fixture}.term").read_text().strip()
    assert term.startswith("(.mk [")
    sigs_end = term.index("] (.cons ")
    sigs = term[len("(.mk "):sigs_end + 1]
    params = [(re.findall(r'"([^"]*)"', ps), re.findall(r'"([^"]*)"', rs))
              for ps, rs in re.findall(r'⟨"[^"]*", (\[[^\]]*\]), (\[[^\]]*\])⟩', sigs)]
    bodies_term, after = group(term, sigs_end + 2)
    items_term, _ = group(term, after + 1)
    bodies = []
    cur = bodies_term
    while cur != ".nil":
        assert cur.startswith("(.cons ")
        b, k = group(cur, len("(.cons "))
        bodies.append(b)
        cur = cur[k + 1:-1]
    assert len(bodies) == len(names) == len(params)
    P = prefix
    out = f'''import Solidity.SolcValidation.IrParse
import Solidity.SolcValidation.IrEval

/-!
{doc}
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

def {P}HelpersText : String :=
  {lean_str(text)}

def {P}Sigs : List FnSig :=
  {sigs}

abbrev {P.capitalize()}Body (params rets : List String) :=
  Block ({P}Sigs ++ []) ⟨true, false⟩ (params ++ rets)
'''
    for n, (ps, rs), b in zip(names, params, bodies):
        out += f"\ndef {P}{n} : {P.capitalize()}Body {strs(ps)} {strs(rs)} :=\n  {b}\n"
    chain = ".nil"
    for n in reversed(names):
        chain = f"(.cons {P}{n} {chain})"
    out += f'''
def {P}Bodies : Bodies ({P}Sigs ++ []) {P}Sigs :=
  {chain}

def {P}Items : Items ({P}Sigs ++ []) ⟨false, false⟩ [] {P}Sigs.length :=
  {items_term}

def {P}HelpersCode : Code := .mk {P}Sigs {P}Bodies {P}Items

def {P}HelpersRoot : Object Code := .object "{obj}" {P}HelpersCode []

/-- The generated tree carries the same certificate as a parse of the text. -/
theorem {P}Helpers_certified :
    lex {P}HelpersText = some (objectToks {P}HelpersRoot) ∧ objectWf {P}HelpersRoot = true := by
  decide +kernel

end Solidity.SolcValidation.IrSyntax
'''
    return out

EXP_DOC = """# solc's `checked_exp` helpers, as imported

`expHelpersText` is the verbatim text of six functions cut from the saved solc
0.8.38 `--ir` output of `Census` (`tests/fullscope-20261104/vt1/extract-helpers.py`):
`checked_exp_t_uint256_t_uint256` and everything it calls. The tree was printed
from the parser's output (`IrLeanGen.lean`) and split into named bodies
(`gen-helper-modules.py`); `expHelpers_certified` re-checks it against the text by
kernel evaluation (`Parsed.sound`'s statement)."""
ABI_DOC = """# solc's `uint256` calldata decoder, as imported

`abiHelpersText` is the verbatim text of the five functions of solc 0.8.38's
`abi_decode_tuple_t_uint256` group, cut from the saved `--ir` output of `Census`
(`tests/fullscope-20261104/vt1/extract-helpers.py`), and its tree printed from the
parser's output (`IrLeanGen.lean`, split by `gen-helper-modules.py`);
`abiHelpers_certified` re-checks it against the text by kernel evaluation."""
PUSH_DOC = """# solc's storage-array push, as imported

`pushHelpersText` is the verbatim text of the thirteen functions of solc 0.8.38's
`array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr` group, cut from
the saved `--ir` output of `Census` (`tests/fullscope-20261104/vt1/extract-helpers.py`),
and its tree printed from the parser's output (`IrLeanGen.lean`, split by
`gen-helper-modules.py`); `pushHelpers_certified` re-checks it against the text by
kernel evaluation."""

MODULES = [
    ("exp-helpers", "exp", "ExpHelpers", ["CleanupU", "Panic11", "Shr1", "ExpHelper", "ExpUnsigned", "ExpU256"],
     EXP_DOC, "IrExpHelpers.lean"),
    ("abi-helpers", "abi", "AbiHelpers", ["Revert", "CleanupU", "Validator", "DecodeU256", "DecodeTuple"],
     ABI_DOC, "IrAbiHelpers.lean"),
    ("push-helpers", "push", "PushHelpers",
     ["CleanupU", "Panic41", "Panic32", "Length", "DataSlot", "IndexAccess", "ShiftLeft", "UpdateSlice",
      "Identity", "Convert", "PrepareStore", "UpdateStorage", "Push"], PUSH_DOC, "IrPushHelpers.lean"),
]

failed = False
for fixture, prefix, obj, names, doc, file in MODULES:
    out = module(fixture, prefix, obj, names, doc)
    target = root / "Solidity/SolcValidation" / file
    if "--check" in sys.argv:
        if target.read_text() != out:
            print(f"{file} differs")
            failed = True
    else:
        target.write_text(out)
        print(target, len(out), "bytes")
if "--check" in sys.argv:
    if failed:
        sys.exit(1)
    print("HELPER_MODULES_CHECK_PASS")
