#!/usr/bin/env python3
"""Guard read/discard lowering erasing following writes, reverts or typed locals.

Reuse the prior nonempty primitive input module and unchanged isolated checker;
old helper statements stay intact, and all their proofs are rechecked too.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('statement_joint_gate',Path(__file__).with_name('check_primitive_reads.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);gate=module.gate
OLD_NAMES=list(gate.NAMES)
spec=importlib.util.spec_from_file_location('fresh_statement_joint_gate',Path(__file__).with_name('check_primitive_transport.py'))
fresh=importlib.util.module_from_spec(spec);spec.loader.exec_module(fresh);gate=fresh
gate.SOURCE='tests/h62/item2/audit-readonly-calls/PrimitiveReadWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.PrimitiveReadWitnesses.'
gate.TARGET='Solidity.Lowering.Readonly.ReadStatement'
ALL_INTERFACES=['Solidity.Lowering.Readonly.PrimitiveReads.'+n for n in ['source_expression','root_expression']]+['Solidity.Lowering.Readonly.ReadStatement.'+n for n in ['source_run','target_run','simulation','target_then']]
ALL_NEW_NAMES=['source_expression_joint','root_expression_joint','source_statement_joint','target_statement_joint','statement_simulation_joint','continuation_joint']
gate.INTERFACES=[ALL_INTERFACES[i] for i in [3,5]]
NEW_NAMES=[ALL_NEW_NAMES[i] for i in [3,5]]
gate.NAMES=OLD_NAMES+ALL_NEW_NAMES+['continuation_writes','continuation_reverts']
if __name__=='__main__':gate.main()
