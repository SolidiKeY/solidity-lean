import Solidity.Calculus.CallFunctionAffine

/-! # Compact call-family evaluation: positive and discriminating controls -/
namespace Solidity.Examples.Tactics.CallFunctionAffine
open Solidity.CallFunctionAffine Solidity.CallFunctionLeaf Solidity.CallFunctionTable
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private def name : Var := .fresh "same" 0
private def original (n : Nat) : State C Γ :=
  (({ State.init C with selfBalance := uintOfNat 5 }).push
    (t := .val .uint) (uintOfNat n)).push (t := .val .uint) (uintOfNat 99)
private def post (n : Nat) : Fml C Γ := .eq (.pvV .here) (.app0 (.lit (uintOfNat n)))
private def expectedSix : Nat := (5*3^64-1)/2

/-- Multiple actual coefficient levels, not expansion of 2^k calls. -/
theorem coefficientPins : coefficients 3 1 0 = (3,1) ∧
    coefficients 3 1 1 = (9,4) ∧ coefficients 3 1 2 = (81,40) ∧
    coefficients 3 1 3 = (6561,3280) ∧
    coefficients 3 1 6 = (3^64,(3^64-1)/2) ∧
    coefficients 3 1 7 = (3^128,(3^128-1)/2) := by decide +kernel

/-- Inhabited successful evaluations at multiple actual doubling levels. -/
theorem resultPins :
    power (Solidity.CallFunctionAffine.apply 3 1) 0 (uintOfNat 2) = some (uintOfNat 7) ∧
    power (Solidity.CallFunctionAffine.apply 3 1) 1 (uintOfNat 2) = some (uintOfNat 22) ∧
    power (Solidity.CallFunctionAffine.apply 3 1) 2 (uintOfNat 2) = some (uintOfNat 202) ∧
    power (Solidity.CallFunctionAffine.apply 3 1) 6 (uintOfNat 2) = some (uintOfNat expectedSix) := by
  simp only [power_eq 3 1 (by decide) (by decide)]
  decide +kernel

/-- A complete six-level shared leaf returns the unchanged observation in
both modalities, with its actual intrinsic caller state. -/
theorem sharedSix (m : Modality) : holds (original 2)
    (leaf m name name name (term (uintOfNat 3) (uintOfNat 1)) 6
      .here (.there .here) (post expectedSix)) := by
  apply (holds_shared_affine m name name name (uintOfNat 3) (uintOfNat 1)
    (by decide) 6 .here (.there .here) (post expectedSix) (original 2)).mpr
  rfl

/-- A false result is false at the same inhabited returning state. -/
theorem wrongSix (m : Modality) : ¬ holds (original 2)
    (leaf m name name name (term (uintOfNat 3) (uintOfNat 1)) 6
      .here (.there .here) (post (expectedSix+1))) := by
  intro hh
  have hp : afterOption m (Solidity.CallFunctionAffine.apply
      (coefficients 3 1 6).1 (coefficients 3 1 6).2 (uintOfNat 2))
      (fun r => holds ((original 2).setLocal .here r) (post (expectedSix+1))) := (holds_shared_affine m name name name (uintOfNat 3) (uintOfNat 1)
    (by decide) 6 .here (.there .here) (post (expectedSix+1)) (original 2)).mp hh
  have he : (some (uintOfNat expectedSix) : Option Key) = some (uintOfNat (expectedSix+1)) := hp
  have hn : (uintOfNat expectedSix).val = (uintOfNat (expectedSix+1)).val :=
    congrArg Subtype.val (Option.some.inj he)
  have hv : (uintOfNat expectedSix).val + 1 = (uintOfNat (expectedSix+1)).val := by decide +kernel
  omega

/-- Zero remains zero even at a level whose coefficient exceeds one word. -/
theorem zeroDeep : power (Solidity.CallFunctionAffine.apply 3 0) 8 (uintOfNat 0) = some (uintOfNat 0) := by
  rw [power_eq 3 0 (by decide) (by decide)]
  decide +kernel

/-- Exact upper-edge success and addition-only failure. -/
theorem wordEdge :
    Solidity.CallFunctionAffine.apply 1 0 (uintOfNat (2^256-1)) = some (uintOfNat (2^256-1)) ∧
    Solidity.CallFunctionAffine.apply 1 1 (uintOfNat (2^256-1)) = none := by decide +kernel

/-- Actual multiplication failure is retained before addition. -/
theorem multiplyFailure : (term (C := C) (Γ := Γ) (uintOfNat 3) (uintOfNat 0)).eval
    ((original 0).push (t := .val .uint) (uintOfNat (2^256-1))) = none := by
  rw [eval_term]
  decide +kernel

/-- The first application returns; its dependent successor fails. -/
theorem laterFailure :
    Solidity.CallFunctionAffine.apply 3 1 (uintOfNat (2^254)) = some (uintOfNat (3*2^254+1)) ∧
    power (Solidity.CallFunctionAffine.apply 3 1) 1 (uintOfNat (2^254)) = none := by
  constructor
  · decide +kernel
  · rw [power_eq 3 1 (by decide) (by decide)]
    decide +kernel

/-- Ordered composition differs from its reverse at an inhabited input. -/
theorem orderControl :
    (Solidity.CallFunctionAffine.apply 3 1 (uintOfNat 2)).bind (Solidity.CallFunctionAffine.apply 2 5) =
      some (uintOfNat 19) ∧
    (Solidity.CallFunctionAffine.apply 2 5 (uintOfNat 2)).bind (Solidity.CallFunctionAffine.apply 3 1) =
      some (uintOfNat 28) := by decide +kernel

/-- Dropping the nondecreasing-profile check would hide early failure.
Unsupported shrinking functions must keep ordinary handling. -/
theorem shrinkingCountermodel :
    (Solidity.CallFunctionAffine.apply 2 0 (uintOfNat (2^256-1))).bind
      (Solidity.CallFunctionAffine.apply 0 0) = none ∧
    Solidity.CallFunctionAffine.apply 0 0 (uintOfNat (2^256-1)) = some (uintOfNat 0) := by decide +kernel

/-- The identity profile remains an actual identity at a deep family level. -/
theorem identityDeep : power (Solidity.CallFunctionAffine.apply 1 0) 8
    (uintOfNat (2^256-1)) = some (uintOfNat (2^256-1)) := by
  rw [power_eq 1 0 (by decide) (by decide)]
  decide +kernel

/-- Addition-only overflow is also exercised on the actual intrinsic base. -/
theorem additionFailure : (term (C := C) (Γ := Γ) (uintOfNat 1) (uintOfNat 1)).eval
    ((original 0).push (t := .val .uint) (uintOfNat (2^256-1))) = none := by
  rw [eval_term]
  decide +kernel

/-- A deeper nonzero-offset family fails even at zero, while its preceding
level returns. No blanket deep-family failure is inferred (see zeroDeep). -/
theorem depthFailure :
    power (Solidity.CallFunctionAffine.apply 3 1) 7 (uintOfNat 0) =
      some (uintOfNat ((3^128-1)/2)) ∧
    power (Solidity.CallFunctionAffine.apply 3 1) 8 (uintOfNat 0) = none := by
  simp only [power_eq 3 1 (by decide) (by decide)]
  decide +kernel
end Solidity.Examples.Tactics.CallFunctionAffine
