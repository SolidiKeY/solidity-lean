import SolidityBridge.RoadmapV15.P10.EnvironmentTasksV1

/-! Native producer steps from exact finite opcode facts. The facts remain
explicit routine obligations; no future frame/source simulation is assumed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open EnvironmentTasksV1

private theorem environment_gate {op : Backend.Op} (site : Site op)
    (facts : LocalFacts op site) (allowed : op=.ORIGIN ∨ op=.GASPRICE ∨ op=.CHAINID)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1≤1024) :
    Assembly.driverGate #[] site.state (DecoderAgreement.referenceOp op) = .ok (site.state,2) := by
  rcases facts with ⟨cost,delta,alpha,expansion⟩
  have charge : site.state.gasAvailable-UInt256.ofNat 0=site.state.gasAvailable := by
    change UInt256.mk (site.state.gasAvailable.val-0)=site.state.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),Nat.sub_zero,if_neg (Nat.not_lt_of_ge room)]
  first
  | solve | rfl
  | rcases allowed with rfl|rfl|rfl <;> cases site.state.executionEnv.perm <;> rfl

private theorem environment_checked {op : Backend.Op} (site : Site op)
    (facts : LocalFacts op site) (allowed : op=.ORIGIN ∨ op=.GASPRICE ∨ op=.CHAINID)
    (fuel : Nat) (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1≤1024)
    (next : EVM.State)
    (step : EVM.step (fuel+1) 2 (some (DecoderAgreement.referenceOp op,none)) site.state = .ok next) :
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  have gate := environment_gate site facts allowed gas room
  have decoded := DecoderAgreement.decode_all site
  have nonhalting : Assembly.NonhaltingOpcode (DecoderAgreement.referenceOp op) := by
    rcases allowed with rfl|rfl|rfl <;>
      simp only [DecoderAgreement.referenceOp,Assembly.NonhaltingOpcode,ne_eq,reduceCtorEq,
        not_false_eq_true,and_self]
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] site.state site.state next
      (DecoderAgreement.referenceOp op,none) 2 decoded gate step nonhalting

/-- Native ORIGIN reads sender (not CALLER's source), with no source-frame hypothesis. -/
theorem origin_at (site : Site .ORIGIN) (facts : LocalFacts .ORIGIN site) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1≤1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.sender.val::site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply environment_checked site facts (Or.inl rfl) fuel gas room
  rfl

/-- Native transaction price is distinct from entry or post-charge gas. -/
theorem gasprice_at (site : Site .GASPRICE) (facts : LocalFacts .GASPRICE site) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1≤1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.executionEnv.gasPrice::site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply environment_checked site facts (Or.inr (Or.inl rfl)) fuel gas room
  rfl

/-- Actual pinned chainId observation, without a substituted environment parameter. -/
theorem chainid_at (site : Site .CHAINID) (facts : LocalFacts .CHAINID site) (fuel : Nat)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (room : site.state.stack.length+1≤1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (EvmYul.State.chainId site.state.toState::site.state.stack)
    Assembly.driverSteps 1 (fuel+2) #[] site.state = .ok next ∧
      EVM.X (fuel+2) #[] site.state = EVM.X (fuel+1) #[] next := by
  apply environment_checked site facts (Or.inr (Or.inr rfl)) fuel gas room
  rfl

#print axioms origin_at
#print axioms gasprice_at
#print axioms chainid_at
end SolidityBridge.RoadmapV15.P10
