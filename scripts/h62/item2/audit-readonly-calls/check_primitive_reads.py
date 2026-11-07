#!/usr/bin/env python3
"""Guard empty/head-only reads replacing original nonempty field/read inputs.

Reuse the existing isolated dual-tree checker and authenticated dependency cache;
only this named selection changes. No held workload or arbitrary cache fallback.
"""
import importlib.util
from pathlib import Path
import hashlib
spec=importlib.util.spec_from_file_location('primitive_read_joint_gate',Path(__file__).with_name('check_initialization.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
gate.TARGET='Solidity.Lowering.Readonly.PrimitiveReads'
gate.SOURCE='tests/h62/item2/audit-readonly-calls/PrimitiveReadWitnesses.lean'
gate.PREFIX='Solidity.H62.ReadonlyAudit.PrimitiveReadWitnesses.'
gate.INTERFACES=['Solidity.Lowering.Readonly.PrimitiveFields.'+n for n in ['read_value','total','unique','select']]+['Solidity.Lowering.Readonly.PrimitiveReads.'+n for n in ['read_of_read','read_head','target_read_head','target_expression']]
gate.NAMES=['related','read_value_joint','total_joint','unique_joint','select_joint','read_of_read_joint','read_head_joint','target_read_head_joint','target_expression_joint','distinct_reads','head_only_refused']
OriginalCache=gate.cache_module.Cache
class OverlapCache(OriginalCache):
    """Authenticate the full parent, then reuse only its checked overlap.

    A narrower consumer need not load PrimitiveLocals; its parent source is still
    checked against the selected tree before the unchanged cache verifier runs.
    Missing/changed parent bytes refuse reuse, never fall back to another cache.
    """
    def __init__(self,inputs,root,mode,pins,archive,create=True):
        receipt=inputs.current.original.load_pinned(root.resolve()/'receipt.json',gate.cache_module.ADMITTED[mode])
        compared=dict(pins)
        for relative,pin in receipt['source_pins'].items():
            raw=inputs.original.read_git(relative) if mode=='frozen' else (gate.ROOT/relative).read_bytes()
            actual={'source_sha256':hashlib.sha256(raw).hexdigest(),'imports':gate.profile.imports(raw.decode())}
            if actual!=pin:raise ValueError('parent source/import drift outside or inside overlap')
            if relative in compared and compared[relative]!=actual:raise ValueError('consumer overlap source drift')
            compared[relative]=actual
        super().__init__(inputs,root,mode,compared,archive,create=create)
gate.cache_module.Cache=OverlapCache
if __name__=='__main__':gate.main()
