#!/usr/bin/env python3
"""Guard boundary witness credit from substituted receipts or dropped originals.

Only three Source boundary statements are credited. Actual callee execution,
compiler/world binding, physical frames, gas/fork and all other rows remain open.
"""
import importlib.util
from pathlib import Path
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
module=load('boundary_joint_configuration','check_call_boundaries.py')
collector=load('boundary_joint_collector','primitive_read_coverage.py')
verifier=load('boundary_joint_verifier','initialization_coverage.py')
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='34726cb4b643f1b1fac8e380dfe973b74018d733e4b7581edcac5b2d4b723a65'
collector.BASELINE='b9560a4f32f2792699314830bf76bfc2e23355d7'
collector.ADMISSION_SHA256='db516bc147081f08766528c28751943ea812808edbf8eaa10afe313f2cf54a94'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=module.gate.NAMES[:3]
collector.ENTRY_DETAILS={
 'global_premises':'No assumed compiler/model record. Explicit Env, static frame, account-balance operation and inhabited Source state.',
 'per_input':'Same static=true frame and balance-changing operation; one Bool declared return with exactly 31 bytes and checked 31<32; supplied nonempty callee revert bytes [7,9].',
 'evidence':'Private coordination archive: call-boundaries/authenticated/{frozen,current}-accepted/receipt.json',
 'evidence_manifest':'Private coordination archive: call-boundaries/SHA256SUMS',
 'proof_boundary':'Joint Source boundary inputs and actual extReturn/applyOp runs only; supplied outcomes do not establish callee execution or compiler/world/native-frame/gas/fork adequacy.'}
base_apply=collector.apply
def apply(*args):
    rows,coverage,delta=base_apply(*args)
    changed={r['source_name'] for r in delta['changes']}
    for row in rows['declarations']:
        if row['source_name'] in changed:
            row['premise_assessment']='Exact original/current interface applications with jointly supplied Source boundary inputs; supplied outcomes are not evidence of callee execution.'
    return rows,coverage,delta
collector.apply=apply
if __name__=='__main__':collector.main()
