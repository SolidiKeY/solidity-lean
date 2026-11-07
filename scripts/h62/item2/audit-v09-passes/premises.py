#!/usr/bin/env python3
"""Source premise/owner classification over the unchanged 1,259-row census.

This is a review aid, never a Lean type inference or feasibility oracle. Unknown
heads, implicit inclusion and logical premises in the return type remain pending.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
from census import BASE, OWNER, DECL, COMMAND, census, masked, sha

REFERENCES = {
    "compiled-value": ["Solidity/Evm/MemoryCompile.lean", "structure CompiledVal"],
    "compilation": ["Solidity/Evm/Compiler.lean", "inductive Compilation"],
    "compiled-program": ["Solidity/Evm/MemoryCompile.lean", "structure CompiledProg"],
    "composition-program": ["Solidity/Backend/InternalFlow/RuntimeFrameComposition.lean", "structure Program"],
    "alias-law": ["Solidity/Backend/InternalFlow/RuntimeFrameInterfaceV1.lean", "def NoAliasPromotion"],
    "state-repr": ["Solidity/Evm/MemorySource.lean", "structure StateRepr"],
    "input": ["Solidity/Evm/Compiler.lean", "def Input"],
    "mapped-link": ["Solidity/Backend/Passes/MappedSequence.lean", "def MappedBoundaryLink"],
    "boundary-link": ["Solidity/Backend/Passes/Sequence.lean", "def BoundaryLink"],
    "reached-link": ["Solidity/Backend/Passes/TripleSequence.lean", "def ReachedMappedLink"],
    "call-program": ["Solidity/Evm/MemoryCalls.lean", "structure Program"],
    "scalar-certificate": ["Solidity/Backend/Scalar/Typed.lean", "structure BinaryCertificate"],
    "reference-form": ["Solidity/Backend/InternalFlow/RuntimeFrameV3CallProducerRef.lean", "inductive Form"],
    "entry": ["Solidity/Backend/InternalFlow/RuntimeFrameInterfaceV1.lean", "structure Entry"],
    "captured": ["Solidity/Backend/InternalFlow/RuntimeFrameContext.lean", "structure Captured"],
    "signed-range": ["Solidity/Backend/PrimitivePackets/SignedMod/Source.lean", "abbrev Range"],
    "bitwise-supported": ["Solidity/Backend/PrimitivePackets/Bitwise/Source.lean", "def Supported"],
    "value-repr": ["Solidity/Evm/Repr.lean", "def ReprV"],
    "mapped-output": ["Solidity/Backend/Passes/MappedSequence.lean", "def MappedOutput"],
    "allocation-input": ["Solidity/Evm/MemoryGrowResult.lean", "def AllocationInput"],
    "pointer-repr": ["Solidity/Evm/MemorySource.lean", "def PointerRepr"],
    "abi-word": ["Solidity/Semantics/AbiEntry.lean", "structure Word"],
    "bytecode": ["Solidity/Backend/Opcode.lean", "abbrev Program"],
    "successful-projection": ["Solidity/Backend/Passes/EffectfulConditionalControls.lean", "private def okMachine"],
    "binary-capacity": ["Solidity/Backend/Scalar/Capacity.lean", "structure BinaryInvocation"],
    "closed-capacity": ["Solidity/Backend/Scalar/Capacity.lean", "structure ClosedInvocation"],
    "admitted": ["Solidity/Backend/InternalFlow/RuntimeFrameV3CallProducer.lean", "def admitted"],
}


def skip(clean, i):
    while i < len(clean) and clean[i].isspace():
        i += 1
    return i


def group_end(clean, start):
    stack = []
    for i in range(start, len(clean)):
        char = clean[i]
        if char in "([{":
            stack.append(char)
        elif char in ")]}":
            if not stack or {")": "(", "]": "[", "}": "{"}[char] != stack.pop():
                raise ValueError("unbalanced binder group")
            if not stack:
                return i + 1
    raise ValueError("unterminated binder group")


def top_colon(clean):
    stack = []
    for i, char in enumerate(clean):
        if char in "([{":
            stack.append(char)
        elif char in ")]}":
            stack.pop()
        elif char == ":" and not stack and not clean.startswith(":=", i):
            return i
    return None


def groups(text, start, origin=0):
    clean = masked(text)
    i = skip(clean, start)
    result = []
    while i < len(clean) and clean[i] in "([{":
        end = group_end(clean, i)
        inner = clean[i+1:end-1]
        colon = top_colon(inner)
        if colon is None:
            names, type_text = [], text[i+1:end-1].strip()
        else:
            names = inner[:colon].strip().split()
            type_text = text[i+1+colon+1:end-1].strip()
        result.append({"source": text[i:end], "span": [origin+i, origin+end],
                       "names": names, "type": type_text,
                       "binder_kind": {"(": "explicit", "{": "implicit", "[": "instance"}[clean[i]],
                       "has_type_annotation": colon is not None})
        i = skip(clean, end)
    return result, i


def telescope(signature):
    clean = masked(signature)
    match = DECL.match(clean)
    if match is None:
        raise ValueError("missing declaration header")
    result, end = groups(signature, match.end())
    if end >= len(clean) or clean[end] != ":":
        raise ValueError("unsupported declaration telescope")
    return result, signature[end+1:].strip()


def scoped_variables(source, before):
    clean = masked(source)
    events = [(m.start(), "scope", m) for m in COMMAND.finditer(clean[:before])]
    events += [(m.start(), "variables", m) for m in re.finditer(r"(?m)^[ \t]*variable\b", clean[:before])]
    frames = [[]]
    for _, kind, match in sorted(events, key=lambda x: x[0]):
        if kind == "scope":
            if match.group(1) == "end":
                frames.pop()
            else:
                frames.append([])
        else:
            declarations, _ = groups(source, match.end())
            if not declarations:
                raise ValueError("unsupported variable command")
            for binder in declarations:
                binder["origin"] = "available-section-variable; actual implicit inclusion requires Lean"
            frames[-1].extend(declarations)
    return [binder for frame in frames for binder in frame]


def classify(type_text):
    """Assign source roles; do not infer inhabitation, Prop or name resolution."""
    text = masked(type_text).strip()
    constraints = re.sub(r":=|=>", " ", text)
    head = text.split()[0] if text else ""
    bare = head.split(".")[-1]
    if bare in {"CompiledVal", "CompiledProg", "Compilation"}:
        ref = {"CompiledVal": "compiled-value", "CompiledProg": "compiled-program", "Compilation": "compilation"}[bare]
        return "global-program-certificate", ref
    if head.endswith("Composition.Program"):
        return "global-program-certificate", "composition-program"
    if head.endswith("Memory.Calls.Program"):
        return "global-program-certificate", "call-program"
    if head.endswith(("Scalar.BinaryCertificate", "Scalar.UnaryCertificate")):
        return "global-operator-certificate", "scalar-certificate"
    if head.endswith(("Scalar.BinaryInvocation", "Scalar.ClosedInvocation")):
        return "per-input-stack-capacity-certificate", "binary-capacity" if head.endswith("BinaryInvocation") else "closed-capacity"
    if head.endswith("V3CallProducerRef.Form"):
        return "global-return-form-law", "reference-form"
    if bare == "NoAliasPromotion":
        return "global-fragment-law", "alias-law"
    if bare in {"StateRepr", "RefArrayStateRepr", "FixedStateRepr", "Sim"}:
        return "per-input-representation", "state-repr"
    if bare == "Input" and len(text.split()) > 1:
        return "per-input-admission", "input"
    if text.startswith("(") and text[group_end(text, 0):].startswith(".Input "):
        return "per-input-admission", "input"
    if head.endswith("InterfaceV1.Entry"):
        return "per-input-admission", "entry"
    if head.endswith("Context.Captured"):
        return "per-input-capture-observation", "captured"
    if head.endswith("SignedMod.Range"):
        return "per-value-range-constraint", "signed-range"
    if head == "Supported":
        return "program-operator-support-candidate", "bitwise-supported"
    if bare in {"ReprV", "MappedOutput", "AllocationInput", "PointerRepr"}:
        return "per-input-representation-or-allocation", {"ReprV": "value-repr", "MappedOutput": "mapped-output", "AllocationInput": "allocation-input", "PointerRepr": "pointer-repr"}[bare]
    if bare in {"BoundaryLink", "MappedBoundaryLink", "ReachedMappedLink"}:
        return "per-input-reached-transport", {"BoundaryLink": "boundary-link", "MappedBoundaryLink": "mapped-link", "ReachedMappedLink": "reached-link"}[bare]
    if head.endswith("V3CallProducer.admitted"):
        return "per-input-admission", "admitted"
    if text.startswith(("∀", "forall ")):
        return "quantified-law; scope-unresolved", None
    if re.search(r"(?:\.evalT|\.run|\brun\b|\bverdict\b|\.verdict)\b", text) and re.search(r"[=≠↔]", constraints):
        return "execution-evaluation-or-verdict-constraint; layer-unresolved", None
    if re.search(r"(?:\.pays|hasAllocation|inFragP|valIn)\b", text) and "=" in text:
        return "program-fragment-constraint", None
    if re.search(r"[=≠≤<>↔]|(?:^|\s)(?:True|False|¬|∀|∃)(?:\s|$)", constraints):
        return "other-logical-or-resource-constraint; scope-unresolved", None
    if head == "AbiEntry.Word":
        return "certified-input-value-data-candidate", "abi-word"
    if text == "Backend.Program":
        return "target-code-data-candidate", "bytecode"
    if text.startswith("(okMachine ") and text.endswith(".isSome"):
        return "boolean-success-projection-constraint; layer-unresolved", "successful-projection"
    if text.startswith("Nat → Fin "):
        return "per-input-address-map-data-candidate", None
    if head in {"Nat", "Int", "Bool", "Fin", "Order", "Word", "THalt"} or text.endswith(".Denote"):
        return "scalar-or-value-parameter-candidate; scope-dependent", None
    if bare in {"Machine", "State", "EMState", "Out", "HRef", "Memory", "Stack"} or text in {"Source.St E", "Source.Fr", "AbiEntry.Input"}:
        return "per-input-state-or-result-data-candidate", None
    if head == "List":
        return "sequence-data-candidate; tail-code-or-value-scope-unresolved", None
    if bare in {"Contract", "Ctx", "RCtx", "Env", "Glob", "Frag", "Val", "Prog", "Idx", "Name", "Var", "Args", "PrimTy", "RefTy", "IntTy", "BinOp", "UnOp", "Pipeline"}:
        return "model-program-or-configuration-data-candidate", None
    return "unresolved-type; data-or-premise-not-inferred", None


def constraint_form(text):
    """Lexical refinement of the residual source constraints, not type inference."""
    if "compileProg" in text:
        return "compiler-acceptance-equation"
    if "stackBound" in text or ("1024" in text and "length" in text):
        return "stack-capacity-bound"
    if ".lo" in text and ".hi" in text:
        return "numeric-range-bound"
    if "≤" in text and ("frame" in text or "lo" in text):
        return "frame-or-arena-bound"
    if "TEnv.get" in text or "source.1.get" in text:
        return "source-or-target-environment-read-equation"
    if "target.mem" in text:
        return "target-memory-observation-equation"
    if "op.accepts" in text or ".mapFree" in text or "Evm.Prog.pushes" in text:
        return "static-fragment-or-operator-condition"
    if "op.shortT" in text:
        return "short-circuit-selection-equation"
    if "++" in text:
        return "code-decomposition-equation"
    if "≠ 0" in text:
        return "nonzero-operand-condition"
    if text == "F = G":
        return "fragment-identity-equation"
    if ".stack = []" in text:
        return "initial-stack-observation-equation"
    if text == "n < W":
        return "word-range-bound"
    return "unresolved-source-form"


def return_frontier(conclusion):
    """Record outer source syntax, never infer missing inputs or feasibility."""
    text = masked(conclusion).lstrip()
    if "type_of%" in text:
        return "macro-expansion-required"
    if text.startswith("∃"):
        return "existential-result; witnesses-are-outputs"
    if text.startswith("∀"):
        return "universal-result; binder-inclusion-review-required"
    if text.startswith("let "):
        return "let-prefixed-result; reduction-review-required"
    return "other-source-result; no-hypothesis-absence-inference"



def return_inputs(conclusion):
    """Expose only recognized outer forall/arrow source prefixes.

    Arrow domains may be data types, not proof premises. Unreduced lets,
    existentials, macros and lower-precedence iff forms remain barriers; no
    conclusion about implicit inputs or simultaneous feasibility follows.
    """
    clean = masked(conclusion)
    begin, end = 0, len(clean)
    inputs = []
    status = "unresolved-remainder; no-hypothesis-absence-inference"
    while True:
        while begin < end and clean[begin].isspace(): begin += 1
        while end > begin and clean[end-1].isspace(): end -= 1
        text = clean[begin:end]
        if not text: status = "empty-remainder; review-required"; break
        if "«" in text or "»" in text:
            status = "quoted-identifier; syntax-review-required"; break
        if text.startswith("(") and group_end(text, 0) == len(text):
            begin += 1; end -= 1; continue
        if text.startswith(("∃", "let ", "fun ", "match ", "if ", "by ", "type_of%")):
            status = "output-or-unreduced-form; review-required"; break
        events = []
        stack = []
        for pos in range(begin, end):
            ch = clean[pos]
            if ch in "([{⟨": stack.append(ch)
            elif ch in ")]}⟩":
                if not stack or {')': '(', ']': '[', '}': '{', '⟩': '⟨'}[ch] != stack.pop():
                    raise ValueError("unbalanced return source")
            elif not stack:
                if ch in "∀∃,↔→": events.append((pos, ch))
                elif clean.startswith("->", pos): events.append((pos, "->"))
        if stack: raise ValueError("unbalanced return source")
        quantified = text.startswith("∀") or text.startswith("forall ")
        if quantified:
            comma = next((pos for pos, token in events if token == ","), None)
            if comma is None: status = "forall-without-comma; review-required"; break
            finish = comma + 1
            inputs.append({"kind": "forall-binder-prefix; inclusion-and-type-pending",
                           "source": conclusion[begin:finish], "span": [begin, finish]})
            begin = finish; continue
        # A top-level quantifier can bind an apparent arrow within an output;
        # iff has lower precedence than arrow. Do not misclassify either case.
        if any(token in {"∀", "∃", "↔", ","} for _, token in events) or re.search(r"\b(?:forall|let|fun|match|if|by)\b", text):
            status = "compound-scope; review-required"; break
        arrow = next(((pos, token) for pos, token in events if token in {"→", "->"}), None)
        if arrow is None: break
        pos, token = arrow
        stop = pos
        while stop > begin and clean[stop-1].isspace(): stop -= 1
        if stop == begin: status = "empty-arrow-domain; review-required"; break
        domain = conclusion[begin:stop]
        inputs.append({"kind": "arrow-domain; Prop-or-data-pending", "source": domain,
                       "span": [begin, stop], "source_role": classify(domain)[0]})
        begin = pos + len(token)
    return {"inputs": inputs, "remainder": conclusion[begin:end],
            "remainder_span": [begin, end], "status": status,
            "implicit_inclusion": "pending Lean", "simultaneous_witness": None}


def macro_heads(conclusion):
    result = []
    for match in re.finditer(r"type_of%\s*\(*\s*([\w.']+)", masked(conclusion)):
        result.append({"token": match.group(1), "macro_start_in_return_type": match.start(),
                       "token_span_in_return_type": list(match.span(1)),
                       "resolution": "lexical callee token only; namespace, type and owner require resolution"})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[4]
    frozen = census(root)
    sources = {f["path"]: (root/f["path"]).read_text() for f in frozen["files"]}
    definitions = {}
    for key, (path, marker) in REFERENCES.items():
        data = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=root)
        if (root/path).read_bytes() != data:
            raise ValueError(f"changed classification reference {path}")
        text = data.decode()
        pos = text.index(marker)
        definitions[key] = {"path": path, "line": text.count("\n", 0, pos)+1,
                            "source_sha256": sha(data), "marker": marker,
                            "boundary": "Family-level source reference, not resolved Lean identity for every unqualified binder."}
    rows = []
    for original in frozen["declarations"]:
        binders, conclusion = telescope(original["signature"])
        source = sources[original["path"]]
        context = scoped_variables(source, original["character_span"][0])
        start, end = original["character_span"]
        signature_start = start + len(source[start:end]) - len(source[start:end].lstrip())
        for binder in binders + context:
            role, ref = classify(binder["type"])
            binder["source_role"] = role
            binder["definition_family_reference"] = ref
            binder["inhabitation"] = "unproved"
            if role.startswith("other-logical"):
                binder["source_constraint_form"] = constraint_form(binder["type"])
            binder["source_features"] = {
                "forall_occurs": "∀" in binder["type"] or "forall " in binder["type"],
                "arrow_occurs": "→" in binder["type"],
                "allocation_input_occurs": "AllocationInput" in binder["type"],
                "execution_or_evaluation_occurs": bool(re.search(r"\b(?:run|evalT|verdict)\b", binder["type"])),
            }
            binder["span_basis"] = "frozen-file" if binder in context else "trimmed-signature"
            binder["absolute_span"] = binder["span"] if binder in context else [signature_start+x for x in binder["span"]]

        kinds = sorted({b["source_role"] for b in binders})
        path = original["path"]
        rows.append({key: original[key] for key in ["name", "path", "line", "visibility", "signature_sha256", "source_sha256"]} | {
            "owner": OWNER, "owner_basis": "User-assigned frozen V09 area; no per-file writer claim.",
            "file_role": "pin-candidate" if path.endswith("Pins.lean") else "control-candidate" if path.endswith("Controls.lean") else "named-map-interface-candidate",
            "source_binders": binders, "available_section_variables": context,
            "signature_start": signature_start,
            "return_type": conclusion, "source_roles_present": kinds,
            "return_frontier": return_frontier(conclusion),
            "return_input_accounting": return_inputs(conclusion),
            "macro_callee_tokens": macro_heads(conclusion),
            "return_type_kind": "type_of-macro; expansion-required" if "type_of%" in conclusion else "source-syntax; elaboration-required",
            "return_type_logical_inputs": "pending source review and Lean; return type retained verbatim (including all forall/arrows)",
            "implicit_inclusion_and_name_resolution": "pending Lean",
            "source_telescope_status": "extracted", "simultaneous_witness": None,
            "witness_status": "uncovered", "semantic_classification": "pending Lean and statement review"})
    explicit = [b for row in rows for b in row["source_binders"]]
    result = {"schema": 1, "base": BASE, "inventory_rows": len(rows),
        "inventory_join": "(path,name,signature_sha256,source_sha256); one row per frozen declaration",
        "boundary": "Source role candidates only. No Prop/data inference, resolved elaborated names, implicit-inclusion, satisfiability or proof claim. No exclusions.",
        "simultaneous_requirement": "Choose one common assignment for all theorem parameters and every premise together, including Lean-included context; individual inhabited binders do not suffice.",
        "migration_dependency": {"path": "Solidity/Syntax/Raw.lean", "owner": "solidity-h62-6-20261106/migrate-root-gate", "routing": "Current H70 successor routing; Raw compatibility and reported axiom-growth review remain pending. No overlay acceptance inferred; wait before value_success_tail proof imports/controls/gates."},
        "definition_family_references": definitions, "declarations": rows,
        "summary": {"rows": len(rows), "source_binder_groups": len(explicit),
                    "available_section_groups_across_rows": sum(len(r["available_section_variables"]) for r in rows),
                    "rows_without_source_binder_groups": sum(not r["source_binders"] for r in rows),
                    "rows_with_global_certificate_or_law": sum(any(b["source_role"].startswith("global-") for b in r["source_binders"]) for r in rows),
                    "rows_with_per_input_role": sum(any(b["source_role"].startswith("per-input-") for b in r["source_binders"]) for r in rows),
                    "return_frontiers": dict(sorted(Counter(r["return_frontier"] for r in rows).items())),
                    "residual_constraint_forms": dict(sorted(Counter(b["source_constraint_form"] for b in explicit if "source_constraint_form" in b).items())),
                    "return_source_input_prefixes": sum(len(r["return_input_accounting"]["inputs"]) for r in rows),
                    "rows_with_return_source_inputs": sum(bool(r["return_input_accounting"]["inputs"]) for r in rows),
                    "macro_callee_token_count": sum(len(r["macro_callee_tokens"]) for r in rows),
                    "type_of_macro_return_rows": sum("type_of%" in r["return_type"] for r in rows),
                    "leading_forall_return_rows": sum(r["return_type"].startswith(("∀", "forall ")) for r in rows),
                    "source_binder_roles": dict(sorted(Counter(b["source_role"] for b in explicit).items())),
                    "witnesses_verified": 0, "uncovered": len(rows)}}
    args.output.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True)+"\n").encode()
    (args.output/"premises.json").write_bytes(data)
    (args.output/"premises.sha256").write_text(sha(data)+"  premises.json\n")
    print(json.dumps(result["summary"], sort_keys=True))
    print("SOURCE_PREMISE_CLASSIFICATION_ONLY: no inhabitation or Lean gate claimed")


if __name__ == "__main__":
    main()
