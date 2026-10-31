import Solidity.Tools.ProofTree
import Solidity.Tools.Counterexample
import Solidity.Calculus.Closers

/-!
# Conditional notation and signed-offset controls

Small AU03 fixtures, separate from the longer joined-family examples so
per-file checks stay focused. The theorem statements retain intrinsic
formulas and validity over every typed state.
-/

namespace Solidity.Examples.Tactics.JoinControls
local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/-! ## Conditional notation and normalized signed offsets -/

open Lean Meta in
run_meta do
  for n in ([-3, 0, 4] : List Int) do
    unless CloseJ.affine (toExpr n) == (none, n) do
      throwError "normalized integer literal was not recognized"
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let plus ← mkAppM ``HAdd.hAdd #[x, toExpr (-3 : Int)]
    let minus ← mkAppM ``HSub.hSub #[x, toExpr (-3 : Int)]
    unless CloseJ.affine plus == (some x, -3) do
      throwError "negative addition offset was lost"
    unless CloseJ.affine minus == (some x, 3) do
      throwError "negative subtraction offset was lost"
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let symbolic := mkApp (mkConst ``Int.negSucc) n
    unless CloseJ.affine symbolic == (some symbolic, 0) do
      throwError "a symbolic negative constructor was mistaken for a literal"

/-- Solidity `uint x = c ? 1 : 2;` agrees with the conditional in its postcondition. -/
theorem conditionalJoined : ⊨ᶠ dl!{ ∀ bool c;
    [ uint x = 0; if (c) { x = 1; } else { x = 2; }; ] x = (c ? 1 : 2) } := by
  sol_prove

/-- Solidity `uint x = true ? 7 : 1 / d;` does not read the zero divisor. -/
theorem conditionalLazy : ⊨ᶠ dl!{ ∀ uint d; d = 0 → (true ? 7 : 1 / d) = 7 } := by
  sol_close

/-- Solidity `uint x = false ? 7 : 1 / d;` fails at the inhabited input `d = 0`. -/
theorem conditionalFailure : ¬ (⊨ᶠ dl!{ ∀ uint d; d = 0 → (false ? 7 : 1 / d) = 7 }) := by
  intro h
  have h0 : (none : Option PrimTy.uint.Denote) = some (uintOfNat 7) :=
    h (State.ofStorage (Storage.init StandardExample)) (PrimTy.dflt .uint) rfl
  cases h0

/-- Solidity `x = c ? x + -1 : x + -2;` twice stays within four
of its input. The ordinary closer keeps the signed range checks. -/
theorem signedOffsets : ⊨ᶠ dl!{ ∀ int a; ∀ bool c; ∀ bool d;
    0 <= a ∧ a <= 10 → { x := a }
      { x := (c ? x + -1 : x + -2) }
      { x := (d ? x + -1 : x + -2) } x >= a + -4 } := by
  sol_close

/-- Solidity's two decrements need not stay within one of the input:
`a = 0`, `c = d = false` returns `-4`. -/
theorem signedOffsetsFalse : ¬ (⊨ᶠ dl!{ ∀ int a; ∀ bool c; ∀ bool d;
    0 <= a ∧ a <= 10 → { x := a }
      { x := (c ? x + -1 : x + -2) }
      { x := (d ? x + -1 : x + -2) } x >= a + -1 }) := by
  sol_refute

/-- info: 'Solidity.Examples.Tactics.JoinControls.conditionalJoined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditionalJoined
/-- info: 'Solidity.Examples.Tactics.JoinControls.conditionalLazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditionalLazy
/-- info: 'Solidity.Examples.Tactics.JoinControls.conditionalFailure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditionalFailure

end Solidity.Examples.Tactics.JoinControls
