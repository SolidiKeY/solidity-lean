#!/usr/bin/env python3
"""Guard journal witness credit from changed receipts or erased original rows.
Algebraic History and actual credit/transfer inputs do not imply static-call
admission, general Source execution, compiler binding or physical frames.
"""
import importlib.util
from pathlib import Path
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
module=load('journal_joint_configuration','check_journal_witnesses.py')
collector=load('journal_joint_collector','primitive_read_coverage.py')
verifier=load('journal_joint_verifier','initialization_coverage.py')
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='4375daa3d12b629a461ed5dbfe1e59ee3c7cadbc4fb76a082b816eeb52bc9c6c'
collector.BASELINE='1f61aff14a63372d531db6dc9ee0a54d6fc99e34'
collector.ADMISSION_SHA256='c8de010a9891075452c5627aaf52bf679f317ddb1df6a7d9092b8244c42f67b7'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=module.gate.NAMES[:3]
collector.ENTRY_DETAILS={
 'global_premises':'No assumed compiler/callee/runtime-frame record. Explicit nonempty persistent Bool environment, Source state and inhabited nonempty Bool locals.',
 'per_input':'Distinct sender0/receiver1, amount3, balances9/1→6/4, actual transfer success and same algebraic History at mode=true; actual credit run and checked true persistent cell.',
 'evidence':'Private coordination archive: journal-witnesses/validated/{frozen,current}-accepted/receipt.json',
 'evidence_manifest':'Private coordination archive: journal-witnesses/SHA256SUMS',
 'proof_boundary':'Joint original History premises and actual primitive Source transfer/credit runs only. History is algebraic, not nonzero static-call authorization, general execution linkage, compiler/world/native-frame/gas/fork or cross-version semantic equivalence.'}
base_apply=collector.apply
def apply(*args):
    rows,coverage,delta=base_apply(*args)
    changed={r['source_name'] for r in delta['changes']}
    for row in rows['declarations']:
        if row['source_name'] in changed:
            row['premise_assessment']='Funded distinct-account transfer and nonempty stored-cell inputs jointly satisfy original/current History premises; algebraic static history is not authorization of a nonzero static call.'
    return rows,coverage,delta
collector.apply=apply
if __name__=='__main__':collector.main()
