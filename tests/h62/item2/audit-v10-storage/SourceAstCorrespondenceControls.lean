import Solidity.Lowering.P8.SourceAstCorrespondence

/-! Kernel controls for list correspondence, with no compiler fixture clones.
Regression purpose: a matching output length must not allow omission, swapping
or skipping a failed child. These are algorithm controls, not Source adequacy. -/
namespace H62.StorageAudit.SourceAstCorrespondenceControls
open Solidity.Lowering.P8.SourceAstCorrespondence

def read (n : Nat) : Except String Nat := .ok n

theorem ordered : Each (fun x y => read x = .ok y) [0, 1] [0, 1] :=
  .cons rfl (.cons rfl .nil)

theorem cannot_drop : ¬ Each (fun x y => read x = .ok y) [0, 1] [0] := by
  intro h
  have bad := h.length_eq
  cases bad

theorem cannot_swap : ¬ Each (fun x y => read x = .ok y) [0, 1] [1, 0] := by
  intro h
  cases h with
  | cons first _ => cases first

def partialRead : Nat → Except String Nat
  | 0 => .ok 0
  | _ => .error "unsupported child"

theorem failed_child_not_skipped (outputs : List Nat) :
    ¬ Each (fun x y => partialRead x = .ok y) [0, 1] outputs := by
  intro h
  cases h with
  | cons _ tail =>
    cases tail with
    | cons bad _ => cases bad

/-- info: 'H62.StorageAudit.SourceAstCorrespondenceControls.ordered' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ordered
/-- info: 'H62.StorageAudit.SourceAstCorrespondenceControls.cannot_drop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cannot_drop
/-- info: 'H62.StorageAudit.SourceAstCorrespondenceControls.cannot_swap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms cannot_swap
/-- info: 'H62.StorageAudit.SourceAstCorrespondenceControls.failed_child_not_skipped' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms failed_child_not_skipped
end H62.StorageAudit.SourceAstCorrespondenceControls
