#!/usr/bin/env python3
"""Guard exact private bind credit and preserved reached-state effects.
Use fresh adopted-master captures; retain old rows/receipt hashes and private
locators. Present helpers do not restore removed private identities or H121.
"""
import importlib.util
from pathlib import Path
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
module=load('private_bind_configuration','check_private_bind.py')
collector=load('private_bind_collector','primitive_read_coverage.py')
verifier=load('private_bind_verifier','initialization_coverage.py')
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='dd143d54cc3eaa1a03f2c51a31e8a20487af56b31e2110ef3778fa5eca9eb99e'
collector.BASELINE='316571df66984bb4597810ad44ef686eceea87a4'
collector.ADMISSION_SHA256='f548156a5df829132b40e0c9e557b4f75f5e7ac4bb0eb65df3bbfebce45fefb0'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=module.gate.NAMES[:3]
collector.ENTRY_DETAILS={
 'global_premises':'No assumed global/compiler model. Explicit Source environment, nonempty Bool locals, initial state and effectful EM action/continuation; exact private constants checked in proof terms.',
 'per_input':'Success appends two event records and flips true→false; failure after first effect keeps that reached state and skips continuation; early revert[5] retains entry. Same actions/continuation/input satisfy both private bind laws.',
 'evidence':'Private coordination archive: private-bind/current-master/{frozen,current}-accepted/receipt.json',
 'evidence_manifest':'Private coordination archive: private-bind/SHA256SUMS',
 'proof_boundary':'Joint private-helper inputs and primitive EM bind observations only; event records are not protocol-valid callee/body executions. No compiler/world/frame/gas/fork/H121 or removed-private identity credit. SDK harness is test-only.'}
base_apply=collector.apply
def apply(*args):
    rows,coverage,delta=base_apply(*args)
    changed={r['source_name'] for r in delta['changes']}
    for row in rows['declarations']:
        if row['source_name'] in changed:
            row['premise_assessment']='Exact present private bind constant applied to jointly inhabited effectful action/continuation/state; reached error-state and continuation effects checked. No removed-private or callee/compiler adequacy credit.'
    return rows,coverage,delta
collector.apply=apply
if __name__=='__main__':collector.main()
