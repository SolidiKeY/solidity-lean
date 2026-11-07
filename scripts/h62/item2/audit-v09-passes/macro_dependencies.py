#!/usr/bin/env python3
"""Source-only macro dependency candidates. Never substitutes callee premises
for caller premises: applied arguments and type_of% still require Lean.
"""
import argparse
import json
from pathlib import Path
import subprocess
from census import BASE, OWNER, census, declarations, masked, sha
from premises import telescope, macro_heads, scoped_variables

# Reviewed source candidates from caller namespaces/open commands and imports.
# Names are candidates until Lean resolves the applied macro term.
GROUPS = {
 "BitwiseValueContextControls": {"inhabited": ("Passes/BitwiseValueContext", "application"), "source_result": ("PrimitivePackets/Bitwise/Source", "evalE_operand")},
 "ComparisonReferenceCaptureControls": {"inhabited": ("Passes/ComparisonReferenceCapture", "execution"), "source_component": ("PrimitivePackets/Comparisons/LocalReads", "source_run")},
 "DeferredCondition.Controls": {"correlated": ("Passes/DeferredCondition", "shared")},
 "DeferredConditionFailure.Controls": {"correlated": ("Passes/DeferredConditionFailure", "reached_shared"), "witness": ("Passes/DeferredConditionFailure", "revert_witness_iff")},
 "ShiftCaptureControls": {"inhabited": ("Passes/ShiftCapture", "application"), "source_expression": ("PrimitivePackets/Shifts/General", "source_execution")},
 "SignedDivisionCaptureControls": {"origin": ("Passes/SignedDivisionCapture", "ordinary"), "unchecked_overflow": ("Passes/SignedDivisionCapture", "shared"), "zero_source": ("PrimitivePackets/SignedDiv/Controls", "zero_both"), "overflow_source": ("PrimitivePackets/SignedDiv/Controls", "overflow_both")},
 "SignedRemainderCaptureControls": {"origin_and_component": ("Passes/SignedRemainderCapture", "application"), "zero_source": ("PrimitivePackets/SignedMod/Controls", "source_failure"), "guard_required": ("PrimitivePackets/SignedMod/Controls", "raw_zero_differs"), "no_horizon_promotion": ("PrimitivePackets/SignedMod/Controls", "too_short_horizon")},
 "SignedSubtractionCaptureControls": {"origin": ("Passes/SignedSubtractionCapture", "application"), "source_checked_boundary": ("PrimitivePackets/SignedSub/Controls", "checked_overflow_boundary"), "no_horizon_promotion": ("PrimitivePackets/SignedSub/Controls", "no_horizon_promotion")},
 "UnsignedDependentControls": {"inhabited": ("Passes/UnsignedDependentCapture", "success"), "origins": ("Passes/UnsignedDependentCapture", "component_origins"), "reached_failure": ("Passes/UnsignedDependentFailure", "reached"), "source_first_panic": ("PrimitivePackets/UnsignedDiv/Composition", "division_zero_packet"), "source_second_panic": ("Passes/UnsignedDependentFailure", "reached_source")},
 "UnsignedDependentScopeControls": {"inhabited": ("Passes/UnsignedDependentScope", "reused")},
 "UnsignedWidthCaptureControls": {"inhabited": ("Passes/UnsignedWidthCapture", "application")},
}


def build(root):
    inventory = census(root)
    cache = {}
    imports = {}
    def frozen(path):
        if path not in cache:
            cache[path] = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=root).decode()
        return cache[path]
    def imported_paths(path):
        seen, pending = set(), [path]
        while pending:
            path = pending.pop()
            if path in seen:
                continue
            seen.add(path)
            if path not in imports:
                imports[path] = []
                for line in masked(frozen(path)).splitlines():
                    if line.startswith("import "):
                        imports[path].extend(module.replace(".", "/")+".lean"
                                             for module in line[7:].split() if module.startswith("Solidity."))
            pending.extend(imports[path])
        return seen
    selectors = {"Solidity.Backend.Passes."+group+"."+name: value
                 for group, entries in GROUPS.items() for name, value in entries.items()}
    rows = []
    for caller in inventory["declarations"]:
        _, return_type = telescope(caller["signature"])
        heads = macro_heads(return_type)
        if not heads:
            continue
        module, name = selectors.pop(caller["name"])
        path = "Solidity/Backend/"+module+".lean"
        source = frozen(path)
        candidates = [r for r in declarations(path, source) if r["name"].endswith("."+name)]
        if len(candidates) != 1:
            raise ValueError(f"ambiguous candidate selector {path}:{name}")
        target = dict(candidates[0])
        target["owner"] = "V09 area candidate" if module.startswith("Passes/") else "unconfirmed PrimitivePackets producer"
        target["owner_basis"] = "Dependency source family only; no per-file live owner agreement inferred."
        if path not in imported_paths(caller["path"]):
            raise ValueError(f"candidate outside frozen import closure {path}")
        groups, conclusion = telescope(target["signature"])
        available = scoped_variables(source, target["character_span"][0])
        current = (root/path).read_text()
        current_targets = [r for r in declarations(path, current) if r["name"] == target["name"]]
        fidelity = len(current_targets)==1 and current_targets[0]["signature"]==target["signature"]
        current_available = scoped_variables(current, current_targets[0]["character_span"][0]) if len(current_targets)==1 else []
        context_equal = len(current_targets)==1 and [b["source"] for b in available]==[b["source"] for b in current_available]
        rows.append({"caller": caller["name"], "caller_path": caller["path"],
            "caller_signature_sha256": caller["signature_sha256"], "caller_owner": OWNER,
            "macro_heads": heads, "applied_return_type": return_type,
            "candidate": target, "candidate_telescope": groups,
            "candidate_available_section_variables": available,
            "current_candidate_available_section_text_equal": context_equal,
            "candidate_return_type": conclusion, "candidate_in_frozen_import_closure": True,
            "current_candidate_signature_text_equal": fidelity,
            "candidate_current_source_sha256": sha(current.encode()),
            "candidate_owner": "V09 area candidate" if module.startswith("Passes/") else "PrimitivePackets producer; precise live owner unconfirmed",
            "resolution": "source candidate only; Lean name/type resolution pending",
            "caller_new_premises": [], "simultaneous_witness": None,
            "boundary": "Callee telescope is reference evidence, not extra caller assumptions. Applied arguments may discharge inputs; macro expansion/implicit inclusion remain unverified."})
    if selectors:
        raise ValueError(f"unaccounted selectors {list(selectors)}")
    return {"schema_version":1,"frozen_base":BASE,"validation_revision":subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(),
            "rows":rows,"summary":{"macro_rows":len(rows),"candidate_signature_text_equal":sum(r["current_candidate_signature_text_equal"] for r in rows),"candidate_section_text_equal":sum(r["current_candidate_available_section_text_equal"] for r in rows),"verified_witnesses":0},
            "boundary":"All rows remain uncovered. No applied type inferred, no new premise, no owner agreement or proof claim."}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[4]
    result=build(root)
    data=(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+"\n").encode()
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/"macro-dependencies.json").write_bytes(data)
    (args.output/"macro-dependencies.sha256").write_text(sha(data)+"  macro-dependencies.json\n")
    print(json.dumps(result["summary"],sort_keys=True))


if __name__=="__main__":
    main()
