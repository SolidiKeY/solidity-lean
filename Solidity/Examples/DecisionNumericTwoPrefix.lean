import Solidity.Calculus.DecisionNumericTwoPrefix
import Solidity.Examples.Decision

/-! # Inhabited actual two-prefix translation controls
Both local positions occur in one arithmetic term. The foreign LFml atom is
refused by the actual exact-route test. No whole-prefix coverage theorem is
assumed, and the approved hash-collision unknown control is retained.
-/
namespace Solidity.Examples.DecisionNumericTwoPrefix
open Solidity.Decide Solidity.Examples.Decision
set_option Elab.async false

/-- A real two-input intrinsic source, with constructive syntax evidence. -/
def input (C : Contract) :
    {t : Tm C [.val .uint, .val .uint] (.val .uint) // t.UIntLinear} :=
  ⟨.app2 (.binop .add rfl) (.pvV .here) (.pvV (.there .here)),
    .add (.local .here) (.local (.there .here))⟩

def expected (C : Contract) : LTm C (.val .uint) :=
  .app2 (.binop .add rfl) (.var 1) (.var 0)

/-- The inner and outer locals become distinct actual atoms, in their real order. -/
theorem actual_translation (C : Contract) :
    (input C).val.toLT (((SymS.init (C := C)).pushQ .uint).pushQ .uint) =
      some (expected C) := by rfl

/-- The new producer is inhabited by a source using both binders. -/
theorem producer_client (C : Contract) :
    ∃ l : LTm C (.val .uint),
      (input C).val.toLT (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some l ∧
      l.Num (fun q => q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) (fun _ => False) ∧
      (l.elim : LTm C (.val .uint)) = l ∧ l.condSimp = l ∧ l.nodes ≤ (input C).val.size :=
  uintLinear_two_prefix_sourceBound (input C).property

/-- Two binders do not license an unbound third atom in the unchanged exact test. -/
theorem foreign_parameter_refused (C : Contract) :
    (LFml.all 0 .uint (.all 1 .uint
      (.eq (.var (p := .uint) 2) (.var 2))) : LFml C).inExact = false := by
  rfl

def positive : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint (.eq (input Gaps).val (input Gaps).val))
def negative : Fml Gaps [] :=
  .all (.user "x") .uint (.all (.user "y") .uint (.not (.eq (input Gaps).val (input Gaps).val)))

/-- These two actual sources lie in the unchanged target predicate. -/
theorem concrete_targets : positive.inTarget {} = true ∧ negative.inTarget {} = true := by
  decide +kernel

/-- These concrete leaves are covered independently of the open general bridge. -/
theorem concrete_coverage : positive.Covered = true ∧ negative.Covered = true := by
  decide +kernel

/-- info: ["proved", "refuted", "unknown"] -/
#guard_msgs in
#eval [verdict positive, verdict negative, verdict gapHashNegForall]

end Solidity.Examples.DecisionNumericTwoPrefix
