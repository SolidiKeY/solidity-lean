import SolidityBridge.RoadmapV15.P10.UintNotWords
import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Arbitrary-site charged NOT and the actual typed unsigned-not certificate.
The reference jump-array parameter is arbitrary; its global correctness is not assumed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem uint_not_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (enough : 1 ≤ s.stack.length)
    (room : s.stack.length-1+1 ≤ 1024) :
    Assembly.driverGate valid s .NOT = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .NOT = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' s .NOT = 3 := rfl
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

theorem uint_not_agreement :
∀ (valid : Array EvmYul.UInt256) (site : SolidityBridge.RoadmapV15.P10.Site .NOT) (a : Solidity.Backend.Scalar.Word) (tail : Solidity.Backend.Scalar.Stack)
 (_room : tail.length+1 ≤ 1024) (_gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat),
 let input := (SolidityBridge.RoadmapV15.P10.modularSite site (a::tail)).state;
 let next := (Solidity.Evm.External.Assembly.chargedPrepare input 3).replaceStackAndIncrPC
  ((~~~a::tail).map (fun w => EvmYul.UInt256.mk w.toFin));
 Solidity.Backend.Scalar.step (.op .NOT) (a::tail) = some (~~~a::tail) ∧
 Solidity.Evm.External.Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
 EvmYul.EVM.X (fuel+2) valid input = EvmYul.EVM.X (fuel+1) valid next
 := by
  intro valid site a tail room gas fuel
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::tail)).state
  have gate : Assembly.driverGate valid input .NOT = .ok (input,3) := by
    apply uint_not_gate valid input gas
    · change 1 ≤ ((a::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::tail).map (fun w => UInt256.mk w.toFin)).length-1+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.NOT,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        ((~~~a::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := uint_not_word a
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.NOT,none) :=
    DecoderAgreement.decode_all (modularSite site (a::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.NOT,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

/-- The full code image belongs to the actual selected uintNot certificate. -/
theorem uint_not_code (site : Site .NOT) :
    site.state.executionEnv.code.data.toList =
      Backend.encode (site.before ++ Scalar.uintNot.code ++ site.after) := by
  simpa only [Scalar.uintNot,List.append_assoc,List.singleton_append] using Site.code_bytes site

/-- The existing intrinsic uint source evaluator, selected code and native step.
This consumes an already evaluated typed value, not a source expression frame. -/
theorem selected_uint_not_agreement (valid : Array UInt256) (site : Site .NOT)
    (a : PrimTy.uint.Denote) (tail : Scalar.Stack) (room : tail.length+1 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((~~~Scalar.encodeValue .uint a)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.uintNot.code (Scalar.encodeValue .uint a::tail) =
      (UnOp.bnot.evalT (p := .uint) rfl a).map (fun r => Scalar.encodeValue .uint r::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨Scalar.uintNot.correct a tail,
    (uint_not_agreement valid site (Scalar.encodeValue .uint a) tail room gas fuel).2⟩

#print axioms uint_not_agreement
#print axioms uint_not_code
#print axioms selected_uint_not_agreement
end SolidityBridge.RoadmapV15.P10
