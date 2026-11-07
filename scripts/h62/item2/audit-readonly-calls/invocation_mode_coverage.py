#!/usr/bin/env python3
"""Guard invocation-mode credit from detached metadata or dropped originals.
Capture does not establish callee execution, compiler/world binding or frames.
"""
import importlib.util
from pathlib import Path
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
module=load('invocation_mode_configuration','check_invocation_modes.py')
collector=load('invocation_mode_collector','primitive_read_coverage.py')
verifier=load('invocation_mode_verifier','initialization_coverage.py')
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='9549c8a4e1719fa8454895f725095bbd2e4cc10470aa10b3080d45556b1957ff'
collector.BASELINE='f1d14a91f1831610f2b74ba28941250e1b8ea4f8'
collector.ADMISSION_SHA256='38f1a8909527afdf11ab15cd95aea1a0f56943e0f671d1bbefcd3466643e6957'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=module.gate.NAMES[:3]
collector.ENTRY_DETAILS={
 'global_premises':'Explicit checked function declaration, environment and Glob; each Invocation jointly contains membership, signature, typed target/value/arguments and actual successful capture.',
 'per_input':'Payable declaration with inherited static=true; view/pure declarations with ordinary static=false parents. Nonempty address locals capture distinct receiver2/caller0 and zero call value at horizon2.',
 'evidence':'Private coordination archive: invocation-modes/validated/{frozen,current}-accepted/receipt.json',
 'evidence_manifest':'Private coordination archive: invocation-modes/SHA256SUMS',
 'proof_boundary':'Joint mode premises and actual pre-callee capture only; explicit hasCode/callee model records are not callee execution, selected compiler/world binding, physical frames, gas/fork or H121 adequacy.'}
base_apply=collector.apply
def apply(*args):
    rows,coverage,delta=base_apply(*args)
    changed={r['source_name'] for r in delta['changes']}
    for row in rows['declarations']:
        if row['source_name'] in changed:
            row['premise_assessment']='Actual captured Invocation supplies the same checked declaration and frame as its mode premise; no callee execution or whole-program/compiler adequacy inferred.'
    return rows,coverage,delta
collector.apply=apply
if __name__=='__main__':collector.main()
