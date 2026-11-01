import Solidity.Tools.ProofTree
import Solidity.Tools.Counterexample
import Solidity.Calculus.Closers
import Solidity.Calculus.Print

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

/-- Positive numerals in both arms are checked at the enclosing signed local. -/
theorem conditionalExpectedInt : ⊨ᶠ dl!{ ∀ bool c; ∀ int x;
    { x := (c ? 1 : 2) } x >= 1 } := by
  sol_auto

/-- A nested conditional propagates the signed sort through all its arms. -/
theorem conditionalNestedInt : ⊨ᶠ dl!{ ∀ bool c; ∀ bool d; ∀ int x;
    { x := (c ? (d ? 3 : 4) : (d ? -1 : 2)) } x >= -1 } := by
  sol_auto

/-- The accepted signed conditional still has an inhabited false-bound control. -/
theorem conditionalExpectedIntFalse : ¬ (⊨ᶠ dl!{ ∀ bool c; ∀ int x;
    { x := (c ? 1 : 2) } x <= 0 }) := by
  sol_refute

open Lean Meta in
run_meta do
  let t : NTerm StandardExample := NTerm.ite (NTerm.bool true) (NTerm.num 1) (NTerm.num 2)
  let .ok _ := t.check (.val .int) [] | throwError "signed expected sort was not propagated"
  let .ok ⟨.val .uint, _⟩ := t.resolve [] | throwError "conditional synthesis changed"
  let .ok _ := t.check .kint [] | throwError "existing whole-term widening changed"
  for c in [true, false] do
    let left : NTerm StandardExample := NTerm.ite (NTerm.bool c) (NTerm.bool true) (NTerm.num 2)
    let right : NTerm StandardExample := NTerm.ite (NTerm.bool c) (NTerm.num 2) (NTerm.bool true)
    let .error _ := left.check (.val .int) [] | throwError "mismatched left branch accepted"
    let .error _ := right.check (.val .int) [] | throwError "mismatched right branch accepted"

/-- info: signed and nested conditionals preserve their AST through both formula printers -/
#guard_msgs in
run_meta do
  let fixtures : List (Fml StandardExample []) := [
    cdl[StandardExample]{ ∀ bool c; ∀ int x; { x := (c ? 1 : 2) } x >= 1 },
    cdl[StandardExample]{ ∀ bool c; ∀ int x; { x := (c ? 1 : -2) } x = (c ? 1 : -2) },
    cdl[StandardExample]{ ∀ bool c; ∀ bool d; ∀ int x;
      { x := (c ? (d ? 3 : 4) : (d ? -1 : 2)) } x >= -1 },
    cdl[StandardExample]{ ∀ bool c; ∀ bool d; ∀ int x;
      { x := ((c ? true : d) ? 1 : -2) } x >= -2 }]
  let c := Lean.mkConst ``StandardExample
  for φ in fixtures do
    let original := Fml.quote c φ
    let printed ← Delab.withPrinter original false (Delab.ppFmlS [] original)
    for text in [← fmtCat `dl_fml printed, ← φ.show c []] do
      let .ok parsedSyntax := Lean.Parser.runParserCategory (← Lean.getEnv) `term
          s!"cdl[StandardExample]\{ {text} }"
        | throwError "conditional formula does not parse: {text}"
      let parsed ← Lean.Elab.Term.TermElabM.run' do
        let parsed ← Lean.Elab.Term.elabTermEnsuringType parsedSyntax (← Lean.Meta.inferType original)
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        pure parsed
      unless ← Lean.Meta.isDefEq original parsed do
        throwError "conditional formula roundtrip changed its AST: {text}"
  Lean.logInfo "signed and nested conditionals preserve their AST through both formula printers"

end Solidity.Examples.Tactics.JoinControls
