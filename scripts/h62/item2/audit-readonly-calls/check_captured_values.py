#!/usr/bin/env python3
"""Guard truncated receivers, binder reordering and mutation-sensitive literals.
Use the isolated exact-interface gate and checked hard-linked dependency reuse;
missing dependencies compile from pinned source. No private-name SDK test import.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('captured_values_parent',Path(__file__).with_name('check_private_bind.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);gate=module.gate
gate.TARGET='Solidity.Lowering.Readonly.ReceiverCapture'
gate.SOURCE='tests/h62/item2/audit-readonly-calls/CapturedValueWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.CapturedValueWitnesses.'
gate.INTERFACES=['Solidity.Lowering.Readonly.ReceiverCapture.'+n for n in ['exact_value','evaluate','stable']]+['Solidity.Lowering.Readonly.CapturedArguments.'+n for n in ['literal_eval','reheap_id','eval_any_heap','eval','names','stable']]
gate.NAMES=['receiver_exact_joint','receiver_eval_joint','receiver_stable_joint','literal_joint','reheap_joint','any_heap_joint','arguments_joint','names_joint','arguments_stable_joint','caller_mutations','truncated_receiver_refused','reordered_names_refused']
gate.original.export.generate=module.module.original_generate
def inventory(raw):
    if gate.profile.imports(raw.decode())!=[gate.TARGET]:raise ValueError('unadmitted captured-value witness import')
    rows=gate.original.export.census.declarations_text(gate.SOURCE,raw.decode())
    if [r['source_name'] for r in rows]!=[gate.PREFIX+n for n in gate.NAMES]:raise ValueError('captured-value declaration census drift')
    return rows
gate.inventory=inventory
if __name__=='__main__':gate.main()
