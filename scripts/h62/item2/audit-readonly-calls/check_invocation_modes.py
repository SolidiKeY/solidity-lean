#!/usr/bin/env python3
"""Guard metadata-only labels replacing jointly captured source invocations.
Reuse authenticated read-parent objects and the existing exact-interface gate;
no held Premises workload or general compiler/callee/frame adequacy claim.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('invocation_mode_parent',Path(__file__).with_name('check_call_boundaries.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
gate=module.gate
gate.TARGET='Solidity.Lowering.Readonly.InvocationFrame'
gate.SOURCE='tests/h62/item2/audit-readonly-calls/InvocationModeWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.InvocationModeWitnesses.'
gate.INTERFACES=['Solidity.Lowering.Readonly.InvocationFrame.Invocation.'+n for n in ['inherited','view_mode','pure_mode']]
gate.NAMES=['inherited_joint','view_joint','pure_joint','view_capture_observed','pure_capture_observed','receiver_not_self','ordinary_parent','pure_downgrade_refused']
if __name__=='__main__':gate.main()
