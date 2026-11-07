#!/usr/bin/env python3
"""Guard exact private transport identities being omitted or replaced by aliases.
The test-only SDK import resolves names; unchanged original proof constants and
all their types are checked by the existing isolated frozen/current gate.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('private_transport_parent',Path(__file__).with_name('check_call_boundaries.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);gate=module.gate
gate.TARGET='Solidity.Lowering.Readonly.PrimitiveReads'
gate.SOURCE='tests/h62/item2/audit-readonly-calls/PrivateTransportWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.PrivateTransportWitnesses.'
gate.INTERFACES=['Solidity.Lowering.Readonly.PrimitiveFields.'+n for n in ['cast_injective','cast_back','default_transport']]+['Solidity.Lowering.Readonly.PrimitiveReads.cancel']
gate.NAMES=['injective_joint','back_joint','default_joint','cancel_joint','true_not_default']
def inventory(raw):
    if gate.profile.imports(raw.decode())!=['Lean',gate.TARGET]:raise ValueError('unadmitted private witness import')
    rows=gate.original.export.census.declarations_text(gate.SOURCE,raw.decode())
    if [r['source_name'] for r in rows]!=[gate.PREFIX+n for n in gate.NAMES]:raise ValueError('private witness declaration census drift')
    return rows
gate.inventory=inventory
original_generate=gate.original.export.generate
def generate_with_private_uses(data):
    by={r['source_name']:r for r in data['declarations']}
    if len(by)!=4 or set(by)!=set(gate.INTERFACES) or any('private' not in r['visibility'] for r in by.values()):
        raise ValueError('exact private interface selection mismatch')
    query=original_generate(data)+'\nopen Lean Elab Command\n'
    for source,proof in zip(gate.INTERFACES,gate.NAMES[:4],strict=True):
        module=by[source]['file'][:-5].replace('/','.')
        query+=f"""run_cmd do
  let env ← getEnv
  let some (.thmInfo info) := env.find? `{gate.PREFIX+proof} | throwError "missing witness proof"
  unless info.value.getUsedConstants.contains (mkPrivateNameCore `{module} `{source}) do
    throwError "witness omits exact original private theorem"
  logInfo "H62-PRIVATE-USE {source} {gate.PREFIX+proof}"
"""
    return query
gate.original.export.generate=generate_with_private_uses
if __name__=='__main__':gate.main()
