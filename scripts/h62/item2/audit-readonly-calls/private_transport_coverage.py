#!/usr/bin/env python3
"""Guard private helper credit from omitted identities or surrogate applications.
Only four present original private constants gain joint-input credit; the three
removed-private gaps and all execution/compiler/frame obligations remain open.
"""
import importlib.util
from pathlib import Path
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
module=load('private_transport_configuration','check_private_transport.py')
collector=load('private_transport_collector','primitive_read_coverage.py')
verifier=load('private_transport_verifier','initialization_coverage.py')
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='fcbe9d8acc7c9006d613fac140d000abe397b8f58c417335e831ff98f63f1bb5'
collector.BASELINE='673271f4464fd802f33862bbcaa6c15e5edabe93'
collector.ADMISSION_SHA256='776b975edc5f616a48f3c3fa5bae4922bcf63a344d2d18a4af8cd19e504908ef'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=module.gate.NAMES[:4]
collector.ENTRY_DETAILS={
 'global_premises':'No assumed compiler or global execution model. Explicit Source layout and inhabited Bool values at the same reflexive type equality.',
 'per_input':'Actual true/true casted pair and its equality premise, roundtrip casts of true, actual Bool default false and source typing equation; exact private kernel constants also occur in witness proof terms.',
 'evidence':'Private coordination archive: private-transport/validated/{frozen,current}-accepted/receipt.json',
 'evidence_manifest':'Private coordination archive: private-transport/SHA256SUMS',
 'proof_boundary':'Joint original private-helper premise satisfiability only. No Source execution, compiler/world/frame/gas/fork adequacy or restoration of removed private identities. SDK name-resolution macros remain test-only.'}
base_apply=collector.apply
def apply(*args):
    rows,coverage,delta=base_apply(*args)
    changed={r['source_name'] for r in delta['changes']}
    for row in rows['declarations']:
        if row['source_name'] in changed:
            row['premise_assessment']='Exact original private kernel theorem applied to jointly supplied equality/type/value inputs; proof-term constant link checked. No execution or removed-identity credit.'
    return rows,coverage,delta
collector.apply=apply
if __name__=='__main__':collector.main()
