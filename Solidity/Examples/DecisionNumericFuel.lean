import Solidity.Calculus.DecisionNumericFuel
import Solidity.Examples.Decision

/-! # Adjacent numeric flattener resource controls
Concrete typed numeric syntax at the unchanged511-node stage limit. The generic
API's formula-derived512 budget is a control, not a production admission change.
-/
namespace Solidity.Examples.DecisionNumericFuel
open Solidity.Decide Solidity.Examples.Decision

def samples : Nat → {φ : LFml Gaps // φ.UIntQF (fun _ => True) (fun _ => False)}
  | 0 => ⟨.eq (.var (p := .uint) 0) (.app0 (.lit (uintOfNat 5))),
      .eq (.var 0 True.intro) (.lit (uintOfNat 5))⟩
  | n + 1 => let x := samples n; ⟨.and x.val x.val, .and x.property x.property⟩

def fits : LFml Gaps := (samples 7).val
def oversize : LFml Gaps := .not fits
def unsupported : LFml Gaps := .all 0 .uint fits

def fitsGrammar : fits.UIntQF (fun _ => True) (fun _ => False) := (samples 7).property
def oversizeGrammar : oversize.UIntQF (fun _ => True) (fun _ => False) := .not fitsGrammar

def failedSeq : LTm Gaps (.val .uint) := .seq (.err : LTm Gaps (.val .uint)) (.app0 (.lit (uintOfNat 5)))

/-- info: [511, 512, 512, 3] -/
#guard_msgs in
#eval [fits.nodes, oversize.nodes, unsupported.nodes, failedSeq.nodes]
/-- info: [true, true, false, true, false] -/
#guard_msgs in
#eval [(flattenFormulaAt? 511 0 fits).isSome, (flattenFormulaAt? 511 27 fits).isSome,
  (flattenFormulaAt? 511 27 oversize).isSome, (flattenFormulaAt? 512 27 oversize).isSome,
  (flattenFormulaAt? 512 0 unsupported).isSome]
/-- info: [false, true] -/
#guard_msgs in
#eval [(flattenTermAt? 2 0 failedSeq).isSome, (flattenTermAt? 3 0 failedSeq).isSome]

theorem node_counts : fits.nodes = 511 ∧ oversize.nodes = 512 ∧
    unsupported.nodes = 512 ∧ failedSeq.nodes = 3 := by
  decide +kernel

theorem fits_at_arbitrary_start (start : Nat) :
    (flattenFormulaAt? 511 start fits).isSome = true := by
  rfl

theorem oversize_refused_at_511 (start : Nat) :
    flattenFormulaAt? 511 start oversize = none := by
  rfl

/-- Mathematical control of the already-parameterized API, not a new runtime cap. -/
theorem oversize_at_own_nodes (start : Nat) :
    (flattenFormulaAt? oversize.nodes start oversize).isSome = true := by
  rfl

theorem unsupported_refused (start : Nat) :
    flattenFormulaAt? 512 start unsupported = none := by
  rfl

theorem failed_seq_controls : (flattenTermAt? 2 0 failedSeq).isSome = false ∧
    (flattenTermAt? 3 0 failedSeq).isSome = true := by
  decide +kernel

/-- A concrete client of the symbolic resource theorem at every budget/start. -/
theorem fits_threshold (budget start : Nat) :
    (flattenFormulaAt? budget start fits).isSome = true ↔ 511 ≤ budget := by
  exact numeric_formula_flattenAt_iff_nodes fitsGrammar budget start

theorem oversize_threshold (budget start : Nat) :
    (flattenFormulaAt? budget start oversize).isSome = true ↔ 512 ≤ budget := by
  exact numeric_formula_flattenAt_iff_nodes oversizeGrammar budget start

#print axioms node_counts
#print axioms fits_at_arbitrary_start
#print axioms oversize_refused_at_511
#print axioms fits_threshold
#print axioms oversize_threshold
#print axioms failed_seq_controls

end Solidity.Examples.DecisionNumericFuel
