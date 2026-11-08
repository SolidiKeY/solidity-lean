#!/usr/bin/env python3
"""Guard empty/self-transfer histories replacing funded persistent-storage inputs.
Reuse the exact authenticated read-parent pair and isolated interface checker;
compile missing dependencies and the additive witness, never held Premises.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('journal_boundary_parent',Path(__file__).with_name('check_call_boundaries.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
gate=module.gate
gate.TARGET='Solidity.Lowering.Readonly.StaticJournal'
gate.SOURCE='tests/h62/item2/audit-readonly-calls/JournalWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.JournalWitnesses.'
gate.INTERFACES=['Solidity.Lowering.Readonly.StaticJournal.'+n for n in ['transfer_history','History.storage','credit_history']]
gate.NAMES=['transfer_joint','storage_joint','credit_joint','credit_observed','transfer_balances','preserved_flag','unchanged_world_refused','erased_flag_refused']
if __name__=='__main__':gate.main()
