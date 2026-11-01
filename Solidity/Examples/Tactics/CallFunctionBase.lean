import Solidity.Calculus.CallFunctionBase

/-! # Actual base-definition models and corrupted-entry controls
The term reads original caller locals for its factor/offset, under new
input/result/table slots. All full-domain witnesses remain opaque proofs.
-/
namespace Solidity.Examples.Tactics.CallFunctionBase
open Solidity.CallFunctionBase Solidity.CallFunctionTable
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private abbrev Inputs : Ctx := .val .uint :: Γ
private def original : State C Γ :=
  ((({ State.init C with selfBalance := uintOfNat 5, net := [(uintOfNat 5, 19)] }).push
    (t := .val .uint) (uintOfNat 1)).push (t := .val .uint) (uintOfNat 3))
private def baseTerm : Tm C Inputs (.val .uint) :=
  (Val.binop .add rfl rfl
    (.binop .mul rfl rfl (.simple (.local .here)) (.simple (.local (.there .here))))
    (.simple (.local (.there (.there .here))))).lower
private def observed (x : Key) : Option Key :=
  baseTerm.eval (original.push (t := .val .uint) x)
private def name : Var := .fresh "same" 0
private def definition : Fml C (.oldNet :: Γ) := clause name name baseTerm

/-- Evaluation agreement is checked from the actual arithmetic term. -/
theorem agreement : baseTerm.agreeB = true := rfl

/-- The same typed term has distinct results and a genuine checked overflow. -/
theorem observations : observed (uintOfNat 2) = some (uintOfNat 7) ∧
    observed (uintOfNat 3) = some (uintOfNat 10) ∧
    observed (uintOfNat (2^256-1)) = none := ⟨rfl, rfl, rfl⟩

/-- Arbitrary table data and a fresh result value do not change original reads. -/
theorem readsOriginal (L : Ledger) (x r : Key) :
    (resultTerm baseTerm).denote (((original.push (t := .oldNet) L).push
      (t := .val .uint) x).push (t := .val .uint) r) = observed x :=
  (result_reads baseTerm original L x r).trans
    (Tm.agreeB_denote agreement (original.push (t := .val .uint) x))

/-- The definition is inhabited and all three observed entries match evaluation. -/
theorem inhabited : ∃ L : Ledger,
    holds (original.push (t := .oldNet) L) definition ∧
    L.at (uintOfNat 2) = 7 ∧ L.at (uintOfNat 3) = 10 ∧
    L.at (uintOfNat (2^256-1)) = -1 := by
  obtain ⟨L, hL⟩ := exists_represents observed
  refine ⟨L, (holds_clause_eval name name baseTerm agreement original L).mpr hL, ?_, ?_, ?_⟩
  · exact (returns_iff hL (uintOfNat 2) (uintOfNat 7)).mpr rfl
  · exact (returns_iff hL (uintOfNat 3) (uintOfNat 10)).mpr rfl
  · exact (failure_iff hL (uintOfNat (2^256-1))).mpr rfl

/-- Corrupting just the overflowing entry is rejected by the actual definition. -/
theorem failureEntryRejected : ∃ L : Ledger,
    holds (original.push (t := .oldNet) L) definition ∧
    ¬ holds (original.push (t := .oldNet)
      (Semantics.setBy (uintOfNat (2^256-1)) (-2) L)) definition := by
  obtain ⟨L, hL⟩ := satisfiable name name baseTerm original
  refine ⟨L, hL, ?_⟩
  intro hBad
  have hr : Represents (Semantics.setBy (uintOfNat (2^256-1)) (-2) L) observed :=
    (holds_clause_eval name name baseTerm agreement original _).mp hBad
  have bad : Ledger.at (Semantics.setBy (uintOfNat (2^256-1)) (-2) L)
      (uintOfNat (2^256-1)) = -1 :=
    (failure_iff hr (uintOfNat (2^256-1))).mpr rfl
  simp only [Ledger.at, Semantics.lookupBy_setBy_self, Option.getD_some] at bad
  omega

/-- Corrupting one returning entry is rejected independently of the failure code. -/
theorem returnEntryRejected : ∃ L : Ledger,
    holds (original.push (t := .oldNet) L) definition ∧
    ¬ holds (original.push (t := .oldNet) (Semantics.setBy (uintOfNat 2) 8 L)) definition := by
  obtain ⟨L, hL⟩ := satisfiable name name baseTerm original
  refine ⟨L, hL, ?_⟩
  intro hBad
  have hr : Represents (Semantics.setBy (uintOfNat 2) 8 L) observed :=
    (holds_clause_eval name name baseTerm agreement original _).mp hBad
  have bad : Ledger.at (Semantics.setBy (uintOfNat 2) 8 L) (uintOfNat 2) = (7 : Int) :=
    (returns_iff hr (uintOfNat 2) (uintOfNat 7)).mpr rfl
  simp only [Ledger.at, Semantics.lookupBy_setBy_self, Option.getD_some] at bad
  omega

/-- A constant-zero ledger cannot claim this nonconstant partial function. -/
theorem emptyRejected : ¬ holds (original.push (t := .oldNet) []) definition := by
  intro h
  have hr : Represents [] observed :=
    (holds_clause_eval name name baseTerm agreement original []).mp h
  have bad : Ledger.at [] (uintOfNat 2) = (7 : Int) :=
    (returns_iff hr (uintOfNat 2) (uintOfNat 7)).mpr rfl
  change (0 : Int) = 7 at bad
  omega

/-- The new function slot leaves caller/global observations intact. -/
theorem callerFrame (L : Ledger) :
    (original.push (t := .oldNet) L).drop (.push .refl) = original ∧
    (original.push (t := .oldNet) L).selfBalance = uintOfNat 5 ∧
    (original.push (t := .oldNet) L).net.at (uintOfNat 5) = 19 := ⟨rfl, rfl, rfl⟩

/-- The complete actual base clause counts both five-node term occurrences. -/
theorem actualSize : definition.tmSize = 34 := rfl

private def zeroTerm : Tm C Inputs (.val .uint) := .app0 (.lit (uintOfNat 0))

/-- An actual total constant-zero definition has the concrete empty ledger model. -/
theorem totalZero : holds (original.push (t := .oldNet) []) (clause name name zeroTerm) := by
  apply (holds_clause_eval name name zeroTerm rfl original []).mpr
  intro x
  rfl

/-- Replacing that successful zero by failure is a distinct rejected model. -/
theorem zeroFailureRejected : ¬ holds (original.push (t := .oldNet)
    (Semantics.setBy (uintOfNat 2) (-1) [])) (clause name name zeroTerm) := by
  intro h
  have hr : Represents (Semantics.setBy (uintOfNat 2) (-1) [])
      (fun x => zeroTerm.eval (original.push (t := .val .uint) x)) :=
    (holds_clause_eval name name zeroTerm rfl original _).mp h
  have bad : Ledger.at (Semantics.setBy (uintOfNat 2) (-1) []) (uintOfNat 2) = (0 : Int) :=
    (returns_iff hr (uintOfNat 2) (uintOfNat 0)).mpr rfl
  simp only [Ledger.at, Semantics.lookupBy_setBy_self, Option.getD_some] at bad
  omega

end Solidity.Examples.Tactics.CallFunctionBase
