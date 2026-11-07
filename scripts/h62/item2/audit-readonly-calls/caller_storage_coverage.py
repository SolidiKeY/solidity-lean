#!/usr/bin/env python3
"""Guard caller-storage witness credit from dropped premises or original rows.
Reflexive storage equality is premise satisfiability, never compiler adequacy.
"""
import importlib.util
from pathlib import Path
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
module=load('caller_storage_configuration','check_caller_storage.py')
collector=load('caller_storage_collector','primitive_read_coverage.py')
verifier=load('caller_storage_verifier','initialization_coverage.py')
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='af61b58b1fef35036efdc0c987ae76110bce1f536387bc4ce61cfee94e93fbb5'
collector.BASELINE='e693d5bafb7b59eccffcf0454ceeeb07c73d1fbc'
collector.ADMISSION_SHA256='29a3ff4ad6b7a6a4d9af3d6ad6fe0a2cec015d86d52d1ad52d240f7c39f15d5e'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=['storage_joint','exit_joint','owned_exit_joint']
collector.ENTRY_DETAILS={
 'global_premises':'Same actual captured Invocation and explicit external-model Glob; successful RawAt and RuntimeFrames checked together at the same Source endpoints.',
 'per_input':'Nonself receiver2/caller0, actual success[7] and changed events, named persistent true Bool C.flag, caller-owned layout and same true intrinsic storage with both entry/exit relations.',
 'evidence':'Private coordination archive: caller-storage/validated/{frozen,current}-accepted/receipt.json',
 'evidence_manifest':'Private coordination archive: caller-storage/SHA256SUMS',
 'proof_boundary':'Joint premise satisfiability for original caller-storage transports, including the reflexive equality only. Explicit model reply is not compiled/resolved Source body execution, compiler/world binding, physical frames, gas/fork, semantic transport or full H121 adequacy.'}
base_apply=collector.apply
def apply(*args):
    rows,coverage,delta=base_apply(*args)
    changed={r['source_name'] for r in delta['changes']}
    for row in rows['declarations']:
        if row['source_name'] in changed:
            row['premise_assessment']='Same actual Source invocation/raw/history and nonempty caller-owned field representations jointly supplied; reflexive result is premise satisfiability only, not compiler adequacy.'
    return rows,coverage,delta
collector.apply=apply
if __name__=='__main__':collector.main()
