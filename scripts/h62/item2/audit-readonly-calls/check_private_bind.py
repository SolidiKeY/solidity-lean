#!/usr/bin/env python3
"""Guard exact private bind identities and reached success/error state effects.
Reuse verified parent objects through hash-checked hard links to avoid duplicate
cache bytes. Parent objects are never compiler outputs; all hashes still checked.
"""
import importlib.util
import os
from pathlib import Path
from types import SimpleNamespace
spec=importlib.util.spec_from_file_location('private_bind_parent',Path(__file__).with_name('check_private_transport.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);gate=module.gate
gate.SOURCE='tests/h62/item2/audit-readonly-calls/PrivateBindWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.PrivateBindWitnesses.'
gate.INTERFACES=['Solidity.Backend.Passes.SourceCallBoundary.halt_bind','Solidity.Backend.Passes.SourceTypedCall.run_bind','Solidity.Lowering.Readonly.PrimitiveReads.run_bind']
gate.NAMES=['halt_joint','typed_joint','read_joint','success_observed','failure_joint','failure_observed','halt_observed','dropped_continuation_refused','discarded_failure_state_refused']
def generate(data):
    by={r['source_name']:r for r in data['declarations']}
    if len(by)!=3 or set(by)!=set(gate.INTERFACES) or any('private' not in r['visibility'] for r in by.values()):raise ValueError('private bind selection mismatch')
    query=module.original_generate(data)+'\nopen Lean Elab Command\n'
    for source,proof in zip(gate.INTERFACES,gate.NAMES[:3],strict=True):
        owner=by[source]['file'][:-5].replace('/','.')
        query+=f"""run_cmd do
  let env ← getEnv
  let some (.thmInfo info) := env.find? `{gate.PREFIX+proof} | throwError "missing bind witness"
  unless info.value.getUsedConstants.contains (mkPrivateNameCore `{owner} `{source}) do
    throwError "bind witness omits exact private constant"
  logInfo "H62-PRIVATE-USE {source} {gate.PREFIX+proof}"
"""
    return query
gate.original.export.generate=generate
original_copy=gate.cache_module.Cache.copy
original_provenance=gate.cache_module.Cache.provenance
def linked_copy(self,relative,captured,staged,artifact):
    if relative not in self.receipt['source_pins']:return original_copy(self,relative,captured,staged,artifact)
    expected=self.root/'library'/(relative[:-5]+'.olean')
    def link(source,destination):
        if Path(source)!=expected or Path(destination)!=artifact:raise ValueError('unexpected cached link destination')
        os.link(source,destination)
        return str(destination)
    old=gate.cache_module.shutil
    gate.cache_module.shutil=SimpleNamespace(copyfile=link)
    try:return original_copy(self,relative,captured,staged,artifact)
    finally:gate.cache_module.shutil=old
def linked_provenance(self):
    return original_provenance(self)|{'object_storage':'hard-linked checked parent objects; no parent writes; hashes checked before/after'}
gate.cache_module.Cache.copy=linked_copy
gate.cache_module.Cache.provenance=linked_provenance
if __name__=='__main__':gate.main()
