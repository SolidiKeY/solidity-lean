import SolidityBridge.AccessBridge.StorageInterface
import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Charged storage opcode execution through the existing P10 decoder and
Osaka driver. Gate errors, native updates and the protected stack remain
observable. Symbolic slot representation, reset/rollback and full pass
adequacy remain separate obligations. -/
namespace SolidityBridge.AccessBridge.Storage
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem read_charged : ∀ (op : Backend.Op), op ∈ [.SLOAD,.TLOAD] →
    ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state (if op=.SLOAD then .SLOAD else .TLOAD) with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop with
        | none => .error .StackUnderflow
        | some (tail,key) =>
          let prepared := Assembly.chargedPrepare charged cost
          let read := if op=.SLOAD then EvmYul.State.sload prepared.toState key
            else EvmYul.State.tload prepared.toState key
          .ok (({prepared with toState := read.1} : EVM.State).replaceStackAndIncrPC
            (read.2 :: tail)) := by
  intro op allowed site valid fuel
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl
  all_goals
    simp only [reduceCtorEq,ite_true,ite_false]
    rw [Assembly.driverSteps,RoadmapV15.P10.DecoderAgreement.decode_all site]
    simp only [RoadmapV15.P10.DecoderAgreement.referenceOp,Option.option,bind,Except.bind]
    split <;> rename_i gate
    · simp only [gate]
    · rename_i pair
      rcases pair with ⟨state,cost⟩
      dsimp only
      cases state with
      | mk shared pc stack count => cases stack <;> simp only [gate] <;> rfl

theorem write_charged : ∀ (op : Backend.Op), op ∈ [.SSTORE,.TSTORE] →
    ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
    Assembly.driverSteps 1 (fuel+2) valid site.state =
      match Assembly.driverGate valid site.state (if op=.SSTORE then .SSTORE else .TSTORE) with
      | .error error => .error error
      | .ok (charged,cost) =>
        match charged.stack.pop2 with
        | none => .error .StackUnderflow
        | some (tail,key,value) =>
          let prepared := Assembly.chargedPrepare charged cost
          let stored := if op=.SSTORE then EvmYul.State.sstore prepared.toState key value
            else EvmYul.State.tstore prepared.toState key value
          .ok (({prepared with toState := stored} : EVM.State).replaceStackAndIncrPC tail) := by
  intro op allowed site valid fuel
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl
  all_goals
    simp only [reduceCtorEq,ite_true,ite_false]
    rw [Assembly.driverSteps,RoadmapV15.P10.DecoderAgreement.decode_all site]
    simp only [RoadmapV15.P10.DecoderAgreement.referenceOp,Option.option,bind,Except.bind]
    split <;> rename_i gate
    · simp only [gate]
    · rename_i pair
      rcases pair with ⟨state,cost⟩
      dsimp only
      cases state with
      | mk shared pc stack count =>
        cases stack with
        | nil => (simp only [gate]; rfl)
        | cons key tail => cases tail <;> simp only [gate] <;> rfl

theorem continuation : ∀ (op : Backend.Op), op ∈ [.SLOAD,.SSTORE,.TLOAD,.TSTORE] →
    ∀ (site : RoadmapV15.P10.Site op) (valid : Array UInt256) (fuel : Nat),
    EVM.X (fuel+2) valid site.state =
      match Assembly.driverSteps 1 (fuel+2) valid site.state with
      | .error error => .error error
      | .ok next => EVM.X (fuel+1) valid next := by
  intro op allowed site valid fuel
  have nonhalting : ∀ next : EVM.State,
      Assembly.driverHalt next (RoadmapV15.P10.DecoderAgreement.referenceOp op)=none := by
    intro next
    simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
    rcases allowed with rfl | rfl | rfl | rfl <;> rfl
  rw [Assembly.X_unfold,RoadmapV15.P10.DecoderAgreement.decode_all site,
    Assembly.driverSteps,RoadmapV15.P10.DecoderAgreement.decode_all site]
  simp only [Option.getD_some,Option.option,bind,Except.bind]
  cases gate : Assembly.driverGate valid site.state
      (RoadmapV15.P10.DecoderAgreement.referenceOp op) with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨state,cost⟩
    dsimp only
    cases execution : EVM.step (fuel+1) cost
        (some (RoadmapV15.P10.DecoderAgreement.referenceOp op,none)) state with
    | error error => rfl
    | ok next => simp only [nonhalting,Assembly.driverSteps]

def certificate : StorageAccessCertificate where
  budget_zero := fun _ _ _ => rfl
  budget_one := fun _ _ _ => rfl
  read_charged := read_charged
  write_charged := write_charged
  continuation := continuation

/-- info: 'SolidityBridge.AccessBridge.Storage.read_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_charged
/-- info: 'SolidityBridge.AccessBridge.Storage.write_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_charged
/-- info: 'SolidityBridge.AccessBridge.Storage.continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms continuation
/-- info: 'SolidityBridge.AccessBridge.Storage.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate

end SolidityBridge.AccessBridge.Storage
