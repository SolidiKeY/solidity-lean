import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Exact charged numeric gate correspondence over twenty actual Backend ops.
The finite set describes this consumer; it is not a new source admission profile.
Costs come from the pinned relation. Source/world/Osaka adequacy stays open. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
/-- A finite set of actual numeric opcodes for this consumer, not a source profile. -/
def binaryPureOps : List Backend.Op := [.ADD,.MUL,.SUB,.DIV,.SDIV,.MOD,.SMOD,.SIGNEXTEND,.LT,.GT,.SLT,.SGT,.EQ,.AND,.OR,.XOR,.BYTE,.SHL,.SHR,.SAR]
theorem binary_gate_result (op : Backend.Op) (member : op ∈ binaryPureOps) (s : EVM.State) (valid : Array UInt256) :
    let target := DecoderAgreement.referenceOp op
    let cost := EVM.C' s target
    Assembly.driverGate valid s target =
      if s.gasAvailable.toNat < cost then .error .OutOfGass
      else if s.stack.length < 2 then .error .StackUnderflow
      else if 1024 < s.stack.length-2+1 then .error .StackOverflow
      else .ok (s,cost) := by
  have casesOp : op=.ADD ∨ op=.MUL ∨ op=.SUB ∨ op=.DIV ∨ op=.SDIV ∨ op=.MOD ∨ op=.SMOD ∨ op=.SIGNEXTEND ∨ op=.LT ∨ op=.GT ∨ op=.SLT ∨ op=.SGT ∨ op=.EQ ∨ op=.AND ∨ op=.OR ∨ op=.XOR ∨ op=.BYTE ∨ op=.SHL ∨ op=.SHR ∨ op=.SAR := by
    simpa only [binaryPureOps,List.mem_cons,List.not_mem_nil,or_false] using member
  have expansion : EVM.memoryExpansionCost s (DecoderAgreement.referenceOp op) = 0 := by
    rcases casesOp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [DecoderAgreement.referenceOp,EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have delta : EVM.δ (DecoderAgreement.referenceOp op) = some 2 := by
    rcases casesOp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have alpha : EVM.α (DecoderAgreement.referenceOp op) = some 1 := by
    rcases casesOp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _)]
  rcases casesOp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> cases s.executionEnv.perm <;> rfl
theorem binary_gate_wellformed (op : Backend.Op) (member : op ∈ binaryPureOps) (s : EVM.State)
    (valid : Array UInt256) (gas : EVM.C' s (DecoderAgreement.referenceOp op) ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (legal : s.stack.length ≤ 1024) :
    Assembly.driverGate valid s (DecoderAgreement.referenceOp op) = .ok (s,EVM.C' s (DecoderAgreement.referenceOp op)) := by
  have room : s.stack.length-2+1 ≤ 1024 := by omega
  rw [binary_gate_result op member]
  simp only [if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
theorem binary_checked_refusals (op : Backend.Op) (member : op ∈ binaryPureOps) (site : Site op) (fuel : Nat) (valid : Array UInt256) :
    (site.state.gasAvailable.toNat < EVM.C' site.state (DecoderAgreement.referenceOp op) →
      Assembly.driverSteps 1 (fuel+2) valid site.state = .error .OutOfGass ∧ EVM.X (fuel+2) valid site.state = .error .OutOfGass) ∧
    (EVM.C' site.state (DecoderAgreement.referenceOp op) ≤ site.state.gasAvailable.toNat → site.state.stack.length < 2 →
      Assembly.driverSteps 1 (fuel+2) valid site.state = .error .StackUnderflow ∧ EVM.X (fuel+2) valid site.state = .error .StackUnderflow) ∧
    (EVM.C' site.state (DecoderAgreement.referenceOp op) ≤ site.state.gasAvailable.toNat → 2 ≤ site.state.stack.length →
      1024 < site.state.stack.length-2+1 → Assembly.driverSteps 1 (fuel+2) valid site.state = .error .StackOverflow ∧ EVM.X (fuel+2) valid site.state = .error .StackOverflow) := by
  rw [Assembly.X_unfold (fuel+1),DecoderAgreement.decode_all]
  simp only [Assembly.driverSteps,DecoderAgreement.decode_all,Option.getD_some,Option.option,bind,Except.bind]
  simp only [binary_gate_result op member]
  refine ⟨?_,?_,?_⟩
  · intro gas
    simp only [if_pos gas,and_self]
  · intro gas under
    simp only [if_neg (Nat.not_lt_of_ge gas),if_pos under,and_self]
  · intro gas enough over
    simp only [if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_pos over,and_self]
theorem binary_short_fuel (op : Backend.Op) (member : op ∈ binaryPureOps) (site : Site op) (valid : Array UInt256) :
    Assembly.driverSteps 1 1 valid site.state = .error .OutOfFuel ∧
    EVM.X 1 valid site.state =
      (if site.state.gasAvailable.toNat < EVM.C' site.state (DecoderAgreement.referenceOp op) then .error .OutOfGass
       else if site.state.stack.length < 2 then .error .StackUnderflow
       else if 1024 < site.state.stack.length-2+1 then .error .StackOverflow
       else .error .OutOfFuel) := by
  refine ⟨rfl,?_⟩
  rw [Assembly.X_unfold 0,DecoderAgreement.decode_all]
  simp only [Option.getD_some]
  rw [binary_gate_result op member]
  by_cases gas : site.state.gasAvailable.toNat < EVM.C' site.state (DecoderAgreement.referenceOp op)
  · simp only [if_pos gas]
  · by_cases under : site.state.stack.length < 2
    · simp only [if_neg gas,if_pos under]
    · by_cases over : 1024 < site.state.stack.length-2+1
      · simp only [if_neg gas,if_neg under,if_pos over]
      · simp only [if_neg gas,if_neg under,if_neg over]
        rfl
#print axioms binary_gate_result
#print axioms binary_gate_wellformed
#print axioms binary_checked_refusals
#print axioms binary_short_fuel
end SolidityBridge.RoadmapV15.P10
