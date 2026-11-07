#!/usr/bin/env python3
"""Guard static acceptance, short-return decoding and erased revert bytes.

Reuse exact authenticated dependency objects; compile missing dependencies, this
new witness and its exact interface probe. Never load held WorldCalls.Premises.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('call_boundary_overlap',Path(__file__).with_name('check_primitive_reads.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
gate=module.gate
# Exact later executed pair: the old primitive parent correctly refuses drift.
gate.cache_module.ADMITTED={'frozen':'77dabe72f101e76e7f06b1138333ef8891048768db33eb92c33557633b31cfb6',
                            'current':'de296db73898608cd3062f15a4e8a2d9c734fb17ed7cbebe425f104e596df1e8'}
# H145 already authenticated the read-parent tools at this exact saved head.
# Only hash-matching historical Python bytes are restored; none are executed.
authenticate_tools=gate.cache_module.authenticate_tools
def authenticate_read_parent(repo,head,pins,archive,create=True):
    return authenticate_tools(repo,'b099c40125795ce00cfa39c1df48fe5f76925a40',pins,archive,create=create)
gate.cache_module.authenticate_tools=authenticate_read_parent
gate.TARGET='Solidity.Backend.Passes.SourceCallBoundary'
gate.SOURCE='tests/h62/item2/audit-readonly-calls/CallBoundaryWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.CallBoundaryWitnesses.'
gate.INTERFACES=['Solidity.Backend.Passes.SourceCallBoundary.'+n for n in ['static_operation','return_short','return_revert']]
gate.NAMES=['static_joint','short_joint','revert_joint','static_observed','short_observed','revert_observed','static_acceptance_refused','erased_revert_refused']
if __name__=='__main__':gate.main()
