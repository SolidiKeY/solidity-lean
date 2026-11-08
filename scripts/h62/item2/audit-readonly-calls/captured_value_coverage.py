#!/usr/bin/env python3
"""Guard captured receiver truncation, argument order and heap transport credit.
Use fresh adopted-master captures; retain old rows/receipt hashes and private
locators. Captured primitives do not establish Source capture provenance or H121.
"""
import importlib.util
from pathlib import Path
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
module=load('captured_values_configuration','check_captured_values.py')
collector=load('captured_values_collector','primitive_read_coverage.py')
verifier=load('captured_values_verifier','initialization_coverage.py')
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='11ce8cab96624fe816fd0c8c8017f5e0fd61a2b70180f29ab840861090c74742'
collector.BASELINE='ec121bd8edd7ed85ae5544a9ee765a8b06a5aee8'
collector.ADMISSION_SHA256='17381d9d610a70562e3be7d32e66b6e09258e166dbec1d0ebef0a5649fc78e22'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=module.gate.NAMES[:9]
collector.ENTRY_DETAILS={
 'global_premises':'Explicit intrinsic contract, stored Bool, uint locals, high-bit 160-bit receiver, mixed uint/Bool binders and captured values; no assumed compiler model.',
 'per_input':'Same captured receiver/arguments evaluated across local 9→4, true→false storage and distinct empty/nonempty heap typings; ordered names and literal/reheap observations checked.',
 'evidence':'Private coordination archive: captured-values/validated/{frozen,current}-accepted/receipt.json',
 'evidence_manifest':'Private coordination archive: captured-values/SHA256SUMS',
 'proof_boundary':'Already captured primitive values only. No reachable mutation path, reference copy, selected-function/ABI provenance, Source callee execution, compiler/world/frame adequacy or runtime credit.'}
base_apply=collector.apply
def apply(*args):
    rows,coverage,delta=base_apply(*args)
    changed={r['source_name'] for r in delta['changes']}
    for row in rows['declarations']:
        if row['source_name'] in changed:
            row['premise_assessment']='Exact original receiver/argument constant applied to jointly supplied intrinsic states and captured values across distinct heap typings. No capture provenance or callee/compiler adequacy credit.'
    return rows,coverage,delta
collector.apply=apply
if __name__=='__main__':collector.main()
