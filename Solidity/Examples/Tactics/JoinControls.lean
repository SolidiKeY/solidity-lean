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


/-! # Kernel Boolean-atom substitution and contradictory-fact controls
The original source pin is in TestSuite/Derived5.lean. These fixtures keep
partial terms, typed atom identities, binder shadowing and consistent facts
separate from the impossible branch of a joined Boolean mapping key. -/
namespace Solidity.Examples.Tactics.JoinControls.BoolAtomJoin
open Decide
open scoped Solidity.Scoped
private abbrev C := StandardExample
private def unequal : EqF C := ⟨.bool, .var 0, .tt⟩
private def consistent (n : Nat) : Facts C := { nes := List.replicate n unequal }

/-- Every size of the consistent list is inhabited by the false valuation. -/
theorem consistent_ok (n : Nat) (g : State C []) : (consistent n).Ok g AEnv.dflt := by
  refine ⟨(fun _ h => (nomatch h)), ?_, (fun _ h => (nomatch h)), (fun _ h => (nomatch h))⟩
  intro e he
  rcases List.mem_replicate.1 he with ⟨_, rfl⟩
  exact ⟨false, true, rfl, rfl, fun h => Bool.noConfusion h⟩

/-- The consistent controls have an explicit intrinsic state witness. -/
theorem consistent_inhabited (n : Nat) :
    ∃ g : State C [], (consistent n).Ok g AEnv.dflt :=
  ⟨State.init C, consistent_ok n (State.init C)⟩

/-- Positive raw signal, paired with the impossibility of a sound certificate. -/
theorem rawClash : ({ nes := [⟨.bool, .tt, .tt⟩] } : Facts C).clashRaw = true := rfl

/-- Manually equal sides cannot be inhabited as certified unequal values. -/
theorem rawClashImpossible (g : State C []) (ν : AEnv) :
    ¬ ({ nes := [⟨.bool, .tt, .tt⟩] } : Facts C).Ok g ν :=
  fun h => Facts.clashRaw_false h rawClash

private def haltedPremise : LFml C :=
  .imp (.not (.eq (.err : LTm C (.val .bool)) .err)) (.eq .tt (.app0 (.lit false)))

/-- A true negative equality on halting terms cannot prove a false target. -/
theorem haltedPremiseNoExplosion : haltedPremise.close = false := rfl

/-- The partial-term combination is actually false in every intrinsic state. -/
theorem haltedPremiseCountermodel (g : State C []) (ν : AEnv) :
    ¬ haltedPremise.holds g ν := by
  intro h
  have hn : ¬ (LFml.eq (.err : LTm C (.val .bool)) .err).holds g ν := by
    intro he
    obtain ⟨v, hv, _⟩ := (LFml.holds_eq_iff g ν _ _).1 he
    cases hv
  have hb : (LFml.eq (.tt : LTm C (.val .bool)) (.app0 (.lit false))).holds g ν := h hn
  obtain ⟨v, hv, hw⟩ := (LFml.holds_eq_iff g ν _ _).1 hb
  cases hv
  cases hw

/-- Halting operands do not create certified returning disequalities. -/
theorem haltedNotStored :
    (({} : Facts C).addNe1 (.err : LTm C (.val .bool)) .err).nes = [] := rfl

/-- The same numeric atom at another primitive type remains different. -/
theorem typedAtomIdentity :
    ((.var 0 : LTm C (.val .bool)).beqR (.var 0 : LTm C (.val .uint))) = false := rfl

/-- A shadowed atom's old disequality is removed, rather than reused. -/
theorem shadowDropsFact : ((consistent 1).drop 0).nes = [] := rfl

/-- Every consistent list size has a false target; proved semantically rather
than forcing large reflective normal forms past the existing recursion limit. -/
theorem consistentTargetAll (n : Nat) :
    Facts.proveEqN (.var 1 : LTm C (.val .bool)) .tt closeFuel (consistent n) = false := by
  cases hres : Facts.proveEqN (.var 1 : LTm C (.val .bool)) .tt closeFuel (consistent n) with
  | false => rfl
  | true =>
    have hp : (LFml.eq (.var 1 : LTm C (.val .bool)) .tt).holds (State.init C) AEnv.dflt :=
      Facts.proveEqN_sound _ _ closeFuel (consistent_ok n (State.init C)) hres
    obtain ⟨v, hv, hw⟩ := (LFml.holds_eq_iff (State.init C) AEnv.dflt _ _).1 hp
    cases hv
    cases hw

/-- A retained consistent disequality cannot close an unrelated false target. -/
theorem consistentTarget :
    Facts.proveEqN (.var 1 : LTm C (.val .bool)) .tt closeFuel (consistent 8) = false := rfl

/-- Undefined equality is not turned into a positive equality by the fallback. -/
theorem haltedTarget :
    Facts.proveEqN (.err : LTm C (.val .bool)) .tt closeFuel {} = false := rfl

/-- The old returning equality fast path still succeeds without scanning. -/
theorem ordinaryDirect :
    Facts.proveEqN (.var 0 : LTm C (.val .uint)) (.var 0) closeFuel (consistent 32) = true := rfl

private def BoolKeys : Contract := contract!{ mapping(bool => uint) values; }
local instance : InContract := ⟨BoolKeys⟩

/-- Both symbolic Boolean keys return one of the two written values. -/
theorem mappingEither : ⊢ dl!{ ∀ bool b;
    ⟨ values[true] = 1; values[false] = 2; uint r = values[b];
      assert(r == 1 || r == 2); ⟩ true } := by
  sol_prove

/-- Writing two does not justify the changed assertion that it is three. -/
theorem mappingWrong : ¬ (⊢ dl!{ ∀ bool b;
    ⟨ values[true] = 1; values[false] = 2; uint r = values[b];
      assert(r == 1 || r == 3); ⟩ true }) := by
  sol_refute
/-- An outer false hypothesis does not constrain the newly bound source b. -/
theorem shadowedEither : ⊢ dl!{ ∀ bool b; b = false → ∀ bool b;
    ⟨ values[true] = 1; values[false] = 2; uint r = values[b];
      assert(r == 1 || r == 2); ⟩ true } := by
  sol_prove
/-- Reusing the outer fact would falsely prove this inner-key assertion. -/
theorem shadowedWrong : ¬ (⊢ dl!{ ∀ bool b; b = false → ∀ bool b;
    ⟨ values[true] = 1; values[false] = 2; uint r = values[b];
      assert(r == 2); ⟩ true }) := by
  sol_refute

end Solidity.Examples.Tactics.JoinControls.BoolAtomJoin
