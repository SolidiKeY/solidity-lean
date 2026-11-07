#!/usr/bin/env python3
"""Five frozen retained-cycle source plans; no new proof/correspondence claim."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import census

PATH = "Solidity/Backend/StorageOps/TargetRetainedCycleControls.lean"
SOURCE_SHA256 = "6d1d5f6ab145f43704a8ba19a1ddd2887b40c116a7de5b4333f8af6d109931ea"
PREFIX = "Solidity.Backend.StorageOps.TargetRetainedCycle.Controls."
CASES = {
    "executions": {
        "result_components": ["popRegrowPop target returns out1", "code out1 returns out1", "code ++ code out1 returns out1"],
        "obligations": ["Retain all three Evm.run equations and whole Machine equality, not only store views.", "Initial pop derives capacity and the cleared reused-child header; retained tail need not be zero.", "The final zero is the Evm.run result index, not a gas or Source-fuel adequacy theorem."],
        "generic_dependencies": ["TargetRetainedCycle.run_pop_regrow_pop", "TargetRetainedCycle.run_reuse", "Evm.run_append_ok"]
    },
    "ordered": {
        "result_components": ["view target", "view out1", "view grown", "view after grown", "contextView out1", "contextView grown", "contextView after grown"],
        "obligations": ["Retain all 18 ordered slots in each of the four store views and all nine contextView components.", "The reused child2 header and its two previously live words are zero; older child2 tail61, child3 payload79/89, opaque77 and outside99/default87 remain distinct observations.", "Regrowth changes the outer header2 to3 without restoring cleared child2 payload; the next pop returns the post-first-pop state.", "Finite contextView samples are not universal context preservation; do not promote this tuple equality to whole Machine equality."],
        "generic_dependencies": []
    },
    "uncleared_negative": {
        "result_components": ["code target succeeds with wrong", "all 18 wrong-state store observations", "wrong differs from target"],
        "obligations": ["Preserve the positive execution alongside the counterexample; do not replace it with a refusal.", "On old state push then pop selects child3, clearing79 while preserving child2 words53/59 and child3 older tail89.", "The missing cleared-child-header premise invalidates reuse equality; the disequality witness is cell3,0."],
        "generic_dependencies": ["TargetHeaderPush.run_current", "TargetNestedPop.run_current", "Evm.run_append_ok"]
    },
    "failures": {
        "result_components": ["code full reverts", "popRegrowPop empty reverts"],
        "obligations": ["Keep the distinct program orders: capacity refusal at the first push versus empty refusal at the first pop.", "The full outer header is Evm.W-1; the empty outer header is zero.", "An Evm.run revert result supplies no final Machine here; do not infer whole-world rollback or a Source refusal payload."],
        "generic_dependencies": ["Evm.run_append_revert", "TargetHeaderPush.run_current", "TargetRetainedCycle.run_pop_regrow_pop"]
    },
    "changed_payload": {
        "result_components": ["out1 cell2,0 is zero", "target cell2,0 is53", "out1 cell2,2 remains61", "out1 cell3,0 remains79", "out1 differs from target"],
        "obligations": ["Retain every conjunct and the original-state disequality, separately from cycle stability.", "An idempotent reuse cycle preserves the already-cleared state; it does not restore the original live payload.", "Older retained payload61 and another child's79 must not be erased by a whole-extent clear substitution."],
        "generic_dependencies": []
    }
}


def build_packet(source, path, source_sha256, prefix, cases, boundary):
    if hashlib.sha256(source).hexdigest() != source_sha256:
        raise ValueError("frozen module byte drift")
    rows = census.declarations(source.decode('utf-8'), path)
    claims = [r for r in rows if r['candidate_case']]
    if {r['name'] for r in claims} != {prefix+n for n in cases} or len(claims) != len(cases):
        raise ValueError("original control case omission/duplication")
    return dict(schema_version=1, base=census.BASE, path=path, source_sha256=source_sha256,
                boundary=boundary,
                fixture_support=[dict(name=r['name'], declaration_sha256=r['declaration_sha256']) for r in rows if not r['candidate_case']],
                cases=[dict(name=r['name'], statement=r['statement'], statement_sha256=r['statement_sha256'],
                            ambient_binders=r['ambient_binders'], source_plan=copy.deepcopy(cases[r['name'][len(prefix):]]),
                            status="manual-source-plan; generic instance/correspondence pending", counts_as_new_verified_proof=False) for r in claims])


def build(source):
    return build_packet(source, PATH, SOURCE_SHA256, PREFIX, CASES,
        "Manual source obligations for five exact frozen controls only; no new Lean, generic-law instance, elaborated equivalence, runtime test, timing or physical/Source/compiler/world adequacy acceptance.")


def validate(report, source):
    if report != build(source):
        raise ValueError("case ledger drift or unsupported acceptance claim")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args=parser.parse_args()
    root=census.ROOT
    output=args.output.resolve()
    if output == root or root in output.parents:
        parser.error('bulk output must be outside checkout')
    source=subprocess.check_output(['git','show',census.BASE+':'+PATH],cwd=root)
    if (root/PATH).read_bytes() != source:
        raise ValueError('live fixture differs; no frozen-to-live correspondence assumed')
    report=build(source);validate(report,source)
    output.write_text(json.dumps(report,indent=2)+'\n')
    print('five frozen control source plans; zero new verified proofs')


if __name__ == '__main__':
    main()
