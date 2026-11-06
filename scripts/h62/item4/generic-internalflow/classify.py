#!/usr/bin/env python3
"""Expand the manually reviewed case map; never infer semantics from names.
Generated inventories and statement text belong off git. This is external audit
accounting, not a Lean parser, elaboration result, theorem or semantic proof.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from census import ROOT, FAMILY

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
INVENTORY_SHA256 = "b1535a1f91512c882b49b8bf780fe7a41f54a8dda0fa22a1c5ba4a08b4457014"
MAP = ROOT / "tests/h62/item4/generic-internalflow/semantic-cases.txt"
# Facets describe conclusion obligations, including quantified/conditional branches.
# An annotation does not assert that a premise is inhabited or an execution exists.
FACETS = {
    "eq": "Exact construction/equality/coherence; preserve both operands and indices",
    "neq": "Unequal observation/state/layout/identity; retain complete unequal operands",
    "auth": "Positive code-authentication Boolean equality; not source admission",
    "aref": "Negative code-authentication Boolean equality; not runtime revert",
    "view": "Positive intrinsic syntax view/checker reconstruction",
    "vref": "Intrinsic syntax view/checker refusal; not an executed halt",
    "cert": "Inhabited intrinsic source certificate",
    "certneg": "Nonexistence of an intrinsic source certificate",
    "compile": "Compiler/selector acceptance, possibly for a reverting argument",
    "cref": "Compiler/selector refusal, not an executed source or target halt",
    "ev": "Typed expression/argument evaluation success, including false Boolean values",
    "er": "Typed expression/argument evaluation bare revert",
    "ss": "Intrinsic source success case; preserve source, input and full output",
    "sr": "Intrinsic source bare-revert case",
    "sx": "Intrinsic source exhaustion case; never identify with revert",
    "sp": "Intrinsic source panic case; preserve distinct halt constructor",
    "sd": "Intrinsic source payload-bearing revert; retain exact bytes",
    "sn": "Source run result discrimination; full unequal outcomes retained",
    "ts": "Successful target execution case; full machine and residual skip retained",
    "tr": "Target bare-revert execution, sometimes for arbitrary appended suffix",
    "tn": "Target outcome discrimination (revert/fault/success remain distinct)",
    "loop": "Finite target-loop prefix or completed horizon; inl/inr distinguished",
    "loopneg": "Loop prefix is not completed/stopped at the wrong horizon",
    "repr": "Typed state/value/path representation or an inhabited represented input",
    "rneg": "Failure of a typed value/state representation (not compiler refusal)",
    "obs": "Exact typed locals/heap/storage or machine observation, ordered vector retained",
    "pres": "Typed environment/storage/heap/frame or base-extension preservation",
    "pneg": "Failure of heap preservation; cannot impose Heap.Keeps as a premise",
    "alloc": "Allocator ownership/growth witness, distinct from mere capacity",
    "aneg": "Allocator ownership does not exist; success may still be witnessed",
    "capacity": "Exact room/demand or allocation-capacity witness; retain bounds",
    "capneg": "Capacity/admission refusal; retain same caller/frontier/machine",
    "cost": "Exact allocation cost; retain selected computation and input",
    "cneg": "Incorrect-cost counterexample",
    "entry": "Positive frozen Entry witness, including entries for reverting input",
    "eneg": "Frozen Entry fails at a boundary; not a source runtime halt",
    "return": "Frozen Returned witness; retains its target/frame/ownership contract",
    "switness": "Frozen SuccessfulEntry witness; not a universal return claim",
    "fwitness": "Frozen RevertingEntry witness; not a selector refusal",
    "sclaim": "Universal frozen ReturnClaim; retain all quantified entry hypotheses",
    "fclaim": "Universal frozen BareRevertClaim; retain all quantified hypotheses",
    "form": "Typed return form, alias-promotion or nonfragile invariant",
    "formneg": "Counterexample to old nonfragile condition; do not add it as premise",
    "member": "Positive admission membership, including reverting inputs",
    "impossible": "A typed reference is impossible in this heap shape",
    "livenessneg": "A storage reference has no live binding",
    "defaultsneg": "New-object defaults fail despite retained old-object preservation",
    "conditional": "The observation is conditional on an execution premise, not existence",
}

PAIRS = {
    "ordered": {
        "files": ["RuntimeFrameV3OrderedEffectfulScalar.lean", "RuntimeFrameV3OrderedEffectfulStorage.lean"],
        "boundary": "Scalar endpoint requires nonfragile aliases; storage variant transports fragile storage-alias liveness via storage equality while retaining the explicit heap-reference live premise and admitting fragile aliases. Capture count before write; retain mutation and no-Heap.Keeps counterexample. Not type-substitution instances.",
    },
    "runtime": {
        "files": ["RuntimeFrameV3EffectfulRuntime.lean", "RuntimeFrameV3EffectfulStorageRuntime.lean"],
        "boundary": "Keep selected source, Entry, actual pre-write demand, Returned/BareRevert claims and fragile-alias distinction. Never share by strengthening the storage variant with scalar nonfragile premise.",
    },
    "selector": {
        "files": ["RuntimeFrameV3RecursiveScopeCompiler.lean", "RuntimeFrameV3ScalarSourceCompiler.lean"],
        "boundary": "Recursive scopes accept optional wrappers at every quotation level; scalar body equality is exact. Retain full depth/child/name/Idx/context recognition and shallow/deep refusal distinctions.",
    },
    "arguments": {
        "files": ["RuntimeFrameV3AllocatingArguments.lean", "RuntimeFrameV3MutatingCaller.lean"],
        "boundary": "Both transport checked arguments and restore caller with explicit nonfragile restriction, but mutating callee changes old heap contents. Keep same input capacity and separately prove body effects; no Heap.Keeps substitution.",
    },
}
DIRECT9 = {
    "RuntimeFrameV3OrderedEffectfulStorageControls.lean": "ordered",
    "RuntimeFrameV3EffectfulRuntimeControls.lean": "runtime",
    "RuntimeFrameV3EffectfulStorageRuntimeControls.lean": "runtime",
    "RuntimeFrameV3ScalarSourceCompilerControls.lean": "selector",
    "RuntimeFrameV3RecursiveScopeControls.lean": "selector",
}
SUPPORT9 = {
    "RuntimeFrameV3CallerStorageFrameControls.lean": "ordered",
    "RuntimeFrameV3EffectfulSourceCheckControls.lean": "runtime",
    "RuntimeFrameV3EffectfulSourceSelectionControls.lean": "runtime",
    "RuntimeFrameV3ScopedScalarControls.lean": "selector",
}
ABSENCE = {
    ("RuntimeFrameV3CallerStorageFrameControls.lean", "no_ref"): "Empty heap has no HRef of arbitrary RefTy; candidate instance of typed absence lemma.",
    ("RuntimeFrameV3OrderedEffectfulStorageControls.lean", "no_struct"): "Singleton uint-array heap admits no struct HRef; needs constructor disjointness as well as shape. Not identical to empty-heap helper.",
}
NAMED11 = ("sourceReverted", "pushes_zero", "allocationCostProg", "Loc.data")
NOTES = {
    ("RuntimeFrameV3CallProducerControls.lean", "negative_member"): "Positive admission for a reverting input, despite negative in its name.",
    ("RuntimeFrameV3CallProducerControls.lean", "negative_entry"): "Positive Entry for a reverting input, not a refusal.",
    ("RuntimeFrameV3DisjointScalarControls.lean", "bad_selected"): "Compiler accepts the expression whose evaluation later reverts; do not label refusal.",
    ("RuntimeFrameV3ScalarSourceCompilerControls.lean", "bad_root"): "Accepted source selection later reverts; preserve all separate error witnesses.",
    ("RuntimeFrameV3AllocatingCallCoherenceControls.lean", "actual"): "Two successful horizons with equal outputs and heap/env observations, plus zero-depth exhaustion and non-revert.",
    ("RuntimeFrameV3AllocatingOuterZeroControls.lean", "actual"): "Success/Returned and absent allocator coexist; no allocator-ownership premise may be inserted.",
    ("RuntimeFrameV3AllocatingScopedEndpointControls.lean", "zero_without_owner"): "Success/Returned and absent allocator coexist; retain conjunction.",
    ("RuntimeFrameV3AllocatingSourceViewsControls.lean", "actual_exhaustion"): "Conclusion contains source exhaustion and source non-revert only; target success is not asserted here.",
    ("RuntimeFrameV3TypedHeapExtensionalityControls.lean", "old_keeps_insufficient"): "Both Heap.Keeps facts hold, yet heaps differ and new-object Defaults fail. Preserve all four conjuncts.",
    ("RuntimeFrameV3OrderedEffectfulStorageControls.lean", "changed_count"): "Post-write count evaluates to 37, while actual argument capture was 7; do not evaluate after mutation for demand.",
}


def parse_map(text):
    result = {}
    current = None
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("@"):
            current = "RuntimeFrame" + line[1:] + "Controls.lean"
            if current in result:
                raise ValueError(f"duplicate file at map line {number}")
            result[current] = {}
            continue
        if current is None or ":" not in line:
            raise ValueError(f"bad map line {number}")
        tags, names = line.split(":", 1)
        facets = tags.split(",")
        if not facets or len(set(facets)) != len(facets) or set(facets) - FACETS.keys():
            raise ValueError(f"unknown/duplicate facets at map line {number}")
        if not names.split():
            raise ValueError(f"empty case group at map line {number}")
        for name in names.split():
            if name in result[current]:
                raise ValueError(f"duplicate case at map line {number}: {name}")
            result[current][name] = facets
    return result


def classify(inventory, mapping):
    files = [f for f in inventory["files"] if f["controls_file"]]
    if {Path(f["path"]).name for f in files} != set(mapping):
        raise ValueError("Controls file inventory and manual map differ")
    result = []
    totals = Counter()
    for file in files:
        filename = Path(file["path"]).name
        declarations = file["declarations"]
        cases = [d for d in declarations if d["kind"] in ("theorem", "lemma", "example")]
        if len({d["name"] for d in cases}) != len(cases):
            raise ValueError(f"ambiguous declaration name in {filename}; use line keys")
        if set(mapping[filename]) != {d["name"] for d in cases}:
            raise ValueError(f"missing/extra cases in {filename}")
        pair = DIRECT9.get(filename) or SUPPORT9.get(filename)
        audit9 = {"status": "direct_control" if filename in DIRECT9 else "supporting_control" if pair else "not_a_named_twin_control",
                  "pair": pair,
                  "decision": PAIRS[pair]["boundary"] if pair else "No direct audit9 twin claim for this Controls file. Retain its cases; shared dependencies alone do not prove duplication."}
        records = []
        for d in declarations:
            row = dict(d)
            key = (filename, d["name"])
            row["id"] = f"{file['path']}:{d['line']}:{d['header_sha256']}"
            row["audit9"] = audit9
            row["audit11"] = {"status": "candidate_typed_absence_instance" if key in ABSENCE else "no_confirmed_named_helper_duplicate",
                              "decision": ABSENCE.get(key, "Ordinary typed HRef/representation use is not duplicate-proof evidence. No named audit11 helper motif found in InternalFlow; concrete fixtures remain distinct.")}
            row["note"] = NOTES.get(key)
            if d in cases:
                row["role"] = "semantic_case"
                row["facets"] = mapping[filename][d["name"]]
                totals.update(row["facets"])
                row["audit16"] = {"status": "typed_table_method_applies",
                    "decision": "Retain this exact declaration as an obligation/instance. Data may index its typed fixture, but semantic run/correspondence proofs must remain parameterized kernel proofs. No decide-table substitution or existing proof deletion authorized."}
            else:
                row["role"] = "fixture_alias" if d["kind"] == "abbrev" else "fixture_definition"
                row["facets"] = []
                row["audit16"] = {"status": "retain_fixture",
                    "decision": "Keep original intrinsic types, indices, namespace dependencies and definitions; no replacement fixture or erased state representation authorized."}
            records.append(row)
        result.append({"path": file["path"], "source_sha256": file["source_sha256"],
                       "audit9": audit9, "commands": file["commands"], "declarations": records})
    return {"schema": 1, "base": BASE,
            "scope": "All and only 57 filename-suffix Controls files. Embedded Checks/Client controls in other family files remain pending semantic classification. semantic_cases counts original theorem declarations (including helpers), not independent program executions.",
            "boundary": "Manually adjudicated source conclusions with exact lexical headers/hashes; not Lean elaboration or proof replay. Every conditional premise and full conjunct is authoritative in the retained header; facets are nonexclusive summaries, not replacements.",
            "audit9_pairs": PAIRS,
            "audit11_adjudication": "Named motifs absent in InternalFlow. Two distinct typed-absence candidates, not established duplicate bodies. Audit11 MemoryCopies shared-fixture example is outside this lane.",
            "audit16_adjudication": "Method applies to data indexing only; InternalFlow semantic run/correspondence/counterexample obligations are not interchangeable one-decide packets. Yul Raw/vector and Numeric/StatementGrammar examples are out of scope; no H55 generator added.",
            "facet_definitions": FACETS, "files": result,
            "summary": {"controls_files": len(result), "declarations": sum(len(f["declarations"]) for f in result),
                        "semantic_cases": sum(d["role"] == "semantic_case" for f in result for d in f["declarations"]),
                        "fixture_declarations": sum(d["role"] != "semantic_case" for f in result for d in f["declarations"]),
                        "unclassified": 0, "facet_counts_nonexclusive": dict(sorted(totals.items()))}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inventory", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    data = args.inventory.read_bytes()
    if hashlib.sha256(data).hexdigest() != INVENTORY_SHA256:
        raise SystemExit("original frozen inventory SHA256 mismatch")
    destination = args.output.resolve()
    if destination.is_relative_to(ROOT.resolve()):
        raise SystemExit("bulk classification must stay outside repository")
    if destination == args.inventory.resolve() or (destination.exists() and destination.samefile(args.inventory)):
        raise SystemExit("output must not overwrite frozen inventory")
    result = classify(json.loads(data), parse_map(MAP.read_text()))
    encoded = json.dumps(result, sort_keys=True, ensure_ascii=False, indent=2) + "\n"
    destination.write_text(encoded)
    print(json.dumps({"sha256": hashlib.sha256(encoded.encode()).hexdigest(), **result["summary"]}, sort_keys=True))

if __name__ == "__main__":
    main()
