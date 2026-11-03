#!/usr/bin/env python3
"""Generate frozen V15 routine-task signatures; never creates proofs or axioms.
Only the owned output module may be written. --check performs no writes.
"""
import json,sys
from pathlib import Path
root=Path(__file__).resolve().parents[1]
spec=json.loads((root/'scripts/roadmap-v15-environment-tasks-v1.json').read_text())
assert spec['version']==1 and spec['namespace']=='SolidityBridge.RoadmapV15.P10.EnvironmentTasksV1'
rows=spec['rows']
assert [(r['opcode'],r['claim']) for r in rows]==[('ORIGIN','OriginClaim'),('GASPRICE','GasPriceClaim'),('CHAINID','ChainIdClaim')]
terms=['UInt256.ofNat site.state.executionEnv.sender.val','UInt256.ofNat site.state.executionEnv.gasPrice','EvmYul.State.chainId site.state.toState']
assert [r['value'] for r in rows]==terms
text='import SolidityBridge.RoadmapV15.P10.DecoderAgreement\nimport Solidity.Backend.Environment.Frames\n\n/-! GENERATED frozen routine-task statements v1. No proof, instance or axiom is\nprovided. A value of PendingGlueBatch is an outstanding obligation, not evidence.\nThese native clauses cannot extend G31/source/Osaka admission. -/\nnamespace '+spec['namespace']+'\nopen Solidity Solidity.Backend EvmYul Solidity.Evm.External\n\n'
for r in rows:
 text+='def '+r['claim']+' : Prop :=\n  ∀ (site : Site .'+r['opcode']+') (fuel : Nat),\n    2 ≤ site.state.gasAvailable.toNat → site.state.stack.length+1 ≤ 1024 →\n    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC\n      ('+r['value']+' :: site.state.stack)\n    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧\n      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next\n\n'
text+='def SourceRefusalsClaim : Prop :=\n  ∀ (frame : Backend.Environment.Frame) (tail : List Backend.Environment.Word),\n'
for i,r in enumerate(rows):
 text+='    (Backend.Environment.admittedOp .'+r['opcode']+' = false ∧\n      Backend.Environment.step frame (.op .'+r['opcode']+') tail = none)'+(' ∧\n' if i<2 else '\n\n')
text+='def LocalFacts (op : Backend.Op) (site : Site op) : Prop :=\n  EVM.C\' site.state (DecoderAgreement.referenceOp op) = 2 ∧\n  EVM.δ (DecoderAgreement.referenceOp op) = some 0 ∧\n  EVM.α (DecoderAgreement.referenceOp op) = some 1 ∧\n  EVM.memoryExpansionCost site.state (DecoderAgreement.referenceOp op) = 0\n\n'
for r in rows:
 text+='def '+r['claim'].replace('Claim','FactsClaim')+' : Prop :=\n  ∀ site : Site .'+r['opcode']+', LocalFacts .'+r['opcode']+' site\n\n'
text+='structure PendingGlueBatch : Prop where\n  originFacts : OriginFactsClaim\n  gasPriceFacts : GasPriceFactsClaim\n  chainIdFacts : ChainIdFactsClaim\n  sourceRefusals : SourceRefusalsClaim\n\nend '+spec['namespace']+'\n'
p=root/'Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentTasksV1.lean'
if sys.argv[1:]==['--check']:
 assert p.read_text()==text,'generated signature drift'
elif not sys.argv[1:]:
 assert not p.is_symlink()
 if p.exists():assert p.read_text()==text,'frozen signatures already exist with different content'
 else:p.write_text(text)
else:raise SystemExit('usage: generator [--check]')
print('EnvironmentTasksV1: frozen signatures match; proof_values=0; new_axioms=0; registrations=0')
