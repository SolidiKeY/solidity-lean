#!/usr/bin/env python3
"""Three target-only self-copy source plans; the filename supplies no Source bridge."""
import argparse
import json
from pathlib import Path
import subprocess
from retained_cycle_cases import build_packet, census

PATH = "Solidity/Backend/StorageOps/SourceSelfCopyControls.lean"
SOURCE_SHA256 = "0256187b987a431d51f9d160d7d1c89df3d3446a28d39002c1fcac0b413cae03"
PREFIX = "Solidity.Backend.StorageOps.SourceSelfCopyTargetControls."
CASES = {
    "target_self": {
        "result_components": ["actual self-copy program returns entire original Machine"],
        "obligations": ["Retain both identical source/destination slot operands above the original two-word tail; program success consumes the operands and restores exactly machine.", "The whole Machine result is stronger than a finite store/context view; do not reduce its contract to sampled words.", "This is structured intrinsic Evm.run, not ordinary Source AST execution or a physical hashed-word adequacy bridge."],
        "generic_dependencies": ["TargetSelfCopy.run_self"]
    },
    "target_ordered": {
        "result_components": ["original ten-slot view", "afterCopy same-slot ten-slot view", "afterCopy same-slot sampled context"],
        "obligations": ["Retain all ten ordered slots and all nine sampled context components.", "Preserve live nested words7/17, older child0 tail11, older outer child2 header1/payload71, empty root1 and outside root9 sentinel99.", "Finite view equality does not itself prove arbitrary context equality; the distinct target_self whole-Machine execution law is retained.", "The afterCopy state transformer is used here with identical symbolic slots; no numeric hash-injectivity premise is invented."],
        "generic_dependencies": ["TargetSelfCopy.nested_after_self"]
    },
    "different_target_ordered": {
        "result_components": ["afterCopy distinct-empty-source ten-slot view", "afterCopy distinct-empty-source sampled context"],
        "obligations": ["Source root1 has header0 and differs from destination root0; destination outer header and formerly live child0/child1 payloads become zero.", "Retain old child0 tail11, older outer child2 header1/payload71, empty root1 and outside sentinel99.", "Retain all ten slots and all nine context components; do not substitute whole-extent clearing.", "This is an afterCopy state-transformer view equality, not an Evm.run statement or a refusal/rollback theorem.", "The SourceSelfCopy filename and compatibility import do not implement an ordinary Source evaluator."],
        "generic_dependencies": []
    }
}


def build(source):
    return build_packet(source, PATH, SOURCE_SHA256, PREFIX, CASES,
        "Manual source obligations for three exact frozen target-only controls. No new Lean, generic-law instance, elaborated correspondence, Source execution, physical adequacy, rollback or runtime acceptance.")


def validate(report, source):
    if report != build(source):
        raise ValueError('case ledger drift or unsupported acceptance claim')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args=parser.parse_args();output=args.output.resolve();root=census.ROOT
    if output == root or root in output.parents:
        parser.error('bulk output must be outside checkout')
    source=subprocess.check_output(['git','show',census.BASE+':'+PATH],cwd=root)
    if (root/PATH).read_bytes() != source:
        raise ValueError('live fixture differs; no frozen-to-live correspondence assumed')
    report=build(source);validate(report,source)
    output.write_text(json.dumps(report,indent=2)+'\n')
    print('three target-only frozen source plans; zero new verified proofs')


if __name__ == '__main__':main()
