#!/usr/bin/env python3
"""Guard read-statement joint credit from dropped identities or inferred call adequacy.
Reuse the shared exact-accounting collector with an explicit two-case mapping; four Source type drifts remain pending.
"""
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('statement_coverage_gate',Path(__file__).with_name('check_read_statements.py'))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
spec=importlib.util.spec_from_file_location('statement_coverage_collector',Path(__file__).with_name('primitive_read_coverage.py'))
collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector)
spec=importlib.util.spec_from_file_location('statement_fresh_verifier',Path(__file__).with_name('primitive_coverage.py'))
verifier=importlib.util.module_from_spec(spec);spec.loader.exec_module(verifier)
collector.gate=module.gate;collector.verifier=verifier;verifier.gate=module.gate
collector.CANONICAL_SHA='532234a73caefaadee0ef39a75108d9392b6de99e05fcbd763ce9634642c9077'
collector.BASELINE='abcf292e41410f0ba4eb379dd554c4269f1ec735'
collector.ADMISSION_SHA256='e654ee83644eb0c80a69b1c635d8497ec1bd42685f31827dff61ce00f7799882'
collector.CONFIGURATION_SOURCE=Path(__file__)
collector.CREDIT_PROOFS=module.NEW_NAMES
collector.ENTRY_DETAILS={
 'global_premises':'Same explicitly constructed Glob, nonempty fields/source/typed locals and exact field relation; no callee execution inferred.',
 'per_input':'Actual intrinsic second-field read at the same nonempty typed locals and target state; following assignment/revert continuations retained. Four Source-facing original type drifts receive no credit.',
 'evidence':'read-statements/validated/frozen-accepted/receipt.json and read-statements/validated/current-accepted/receipt.json',
 'evidence_manifest':'tests/h62/item2/audit-readonly-calls/read-statements.sha256',
 'proof_boundary':'Joint actual primitive expression/read-statement inputs and typed continuation results only; no compiled call/Source-world/native-frame/gas adequacy.'}
if __name__=='__main__':collector.main()
