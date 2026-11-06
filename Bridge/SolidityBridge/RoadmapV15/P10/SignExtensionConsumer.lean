import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import Solidity.Backend.Scalar.Widths

/-! Actual fetched SIGNEXTEND. The all-index native result is separate from
Scalar agreement: the latter is proved here only for out-of-range byte indices. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem signextend_gate (s : EVM.State) (gas : 5 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s .SIGNEXTEND = .ok (s,5) := by
  have expansion : EVM.memoryExpansionCost s .SIGNEXTEND = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  have cost : EVM.C' s .SIGNEXTEND = 5 := rfl
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

/-- Every native index/value, preserving the actual complete state outside the
charged binary stack update. No execution/decoder/frame hypothesis is supplied. -/
theorem signextend_fetched (site : Site .SIGNEXTEND) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := UInt256.signextend ⟨a.toFin⟩ ⟨b.toFin⟩
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (result :: tail.map (fun w => UInt256.mk w.toFin))
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .SIGNEXTEND = .ok (input,5) := by
    apply signextend_gate input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 5 (some (.SIGNEXTEND,none)) input =
      .ok ((Assembly.chargedPrepare input 5).replaceStackAndIncrPC
        (UInt256.signextend ⟨a.toFin⟩ ⟨b.toFin⟩ :: tail.map (fun w => UInt256.mk w.toFin))) := by
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.SIGNEXTEND,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.SIGNEXTEND,none) 5
      decoded gate step (by unfold Assembly.NonhaltingOpcode;decide)

/-- Out-of-range indices leave the value unchanged, in the actual reference. -/
theorem signextend_large_word (a b : Scalar.Word) (large : 32 ≤ a.toNat) :
    UInt256.signextend ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨b.toFin⟩ := by
  unfold UInt256.signextend
  rw [if_neg (by change ¬a.toNat ≤ 31;omega)]

/-- Same boundary in the published intrinsic Scalar slice, including tail. -/
theorem signextend_large_scalar (a b : Scalar.Word) (tail : Scalar.Stack)
    (large : 32 ≤ a.toNat) : Scalar.step (.op .SIGNEXTEND) (a::b::tail) = some (b::tail) := by
  simp only [Scalar.step,Scalar.numericStep,Scalar.unary,Scalar.binary,Scalar.applyBinary,
    if_neg (by omega : ¬a.toNat < 32)]

/-- Concrete cross-representation boundary transport, without assuming it. -/
theorem signextend_large_agreement (site : Site .SIGNEXTEND) (a b : Scalar.Word)
    (tail : Scalar.Stack) (large : 32 ≤ a.toNat) (room : tail.length+2 ≤ 1024)
    (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((b::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SIGNEXTEND) (a::b::tail) = some (b::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  refine ⟨signextend_large_scalar a b tail large,?_⟩
  have h := signextend_fetched site a b tail room gas fuel
  dsimp only at h ⊢
  rw [signextend_large_word a b large] at h
  exact h

#print axioms signextend_fetched
#print axioms signextend_large_word
#print axioms signextend_large_scalar
#print axioms signextend_large_agreement
end SolidityBridge.RoadmapV15.P10
