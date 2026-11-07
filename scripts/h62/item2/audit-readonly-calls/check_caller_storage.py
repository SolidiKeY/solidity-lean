#!/usr/bin/env python3
"""Guard empty caller layouts and unrelated endpoints replacing joint premises.
Use exact authenticated read-parent objects and the existing isolated checker.
No held Premises workload or compiler/physical-frame adequacy claim.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('caller_storage_parent',Path(__file__).with_name('check_call_boundaries.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);gate=module.gate
gate.TARGET='Solidity.Lowering.Readonly.PrimitiveFields'
gate.SOURCE='tests/h62/item2/audit-readonly-calls/CallerStorageWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.CallerStorageWitnesses.'
gate.INTERFACES=['Solidity.Lowering.Readonly.PrimitiveFields.'+n for n in ['caller_storage','caller_exit','lowered_caller_exit']]
gate.NAMES=['raw','frames','entry','exit','storage_joint','exit_joint','owned_exit_joint','changed_events','erased_representation_refused']
if __name__=='__main__':gate.main()
