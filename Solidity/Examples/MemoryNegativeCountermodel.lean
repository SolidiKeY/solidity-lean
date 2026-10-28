import Solidity.Examples.DecisionMemory

/-!
# The original negative memory block's empty-array countermodel

The original statement stays unchanged. At every initial
state, allocating an empty primitive array makes the negative block's
premise vacuous and its concluding read halt. This is semantic evidence;
the exact closer certificate is in `MemoryNegativeDecision.lean`.
-/

namespace Solidity.Examples.MemoryNegativeCountermodel

open Solidity.Decide Solidity.Examples.Decision

/-- The original exact formula fails at every base state, with an empty
fresh array as its intrinsic allocation witness. -/
theorem gapMemInnerNeg_falseAt (σ : State Gaps []) : ¬ holds σ gapMemInnerNeg := by
  intro h
  let o : MObj σ.H UA := ⟨[], by change 0 < 2 ^ 256; decide⟩
  let τ : State Gaps [.mem UA] := σ.allocPush o
  have hlen : (mlenG .here : Tm Gaps [.mem UA] (.val .uint)).denote τ = some (uintOfNat 0) := by
    change (MxOrig.len (C := Gaps) .here).tm.denote τ = some (uintOfNat 0)
    rw [MxOrig.denote_eq]
    simpa only [MObj.elems_dyn] using mxLenNew_eval σ o
  have hread : (mrdG .dyn .here (litU 0) : Tm Gaps [.mem UA] (.val .uint)).denote τ = none := by
    change (MxOrig.elem (C := Gaps) .here .dyn (litU 0) rfl).tm.denote τ = none
    rw [MxOrig.denote_eq]
    simpa only [Tm.wk_app0, MObj.elems_dyn] using
      (mxReadNew_eval σ o .dyn (litU 0) rfl rfl)
  have hc : (mrdG .dyn .here (litU 0) : Tm Gaps [.mem UA] (.val .uint)).denote τ = some (uintOfNat 0) :=
    (h o) (by
      intro i hi
      have hl : (mlenG (.there .here) : Tm Gaps [.val .uint, .mem UA] (.val .uint)).denote
          (τ.push (t := .val .uint) i) = some (uintOfNat 0) := by
        change ((mlenG (Γ := [.mem UA]) .here).wk (.drop .refl)).denote
          (τ.push (t := .val .uint) i) = some (uintOfNat 0)
        rw [Tm.denote_wk, mxThin_drop_push]
        exact hlen
      change ((mlenG (.there .here) : Tm Gaps [.val .uint, .mem UA] (.val .uint)).denote
        (τ.push (t := .val .uint) i)).bind (fun n => binopT .gt rfl n (some i)) = some true at hi
      rw [hl] at hi
      change some (decide ((0 : Int) > i.1)) = some true at hi
      have hi0 : 0 ≤ i.1 := mxUint_nonneg i
      have hn : ¬ ((0 : Int) > i.1) := by omega
      simp only [hn, decide_false, Option.some.injEq, Bool.false_eq_true] at hi)
  rw [hread] at hc
  cases hc

/-- A concrete typed base state refutes the original formula. -/
theorem gapMemInnerNeg_countermodel : ¬ holds (State.init Gaps) gapMemInnerNeg :=
  gapMemInnerNeg_falseAt (State.init Gaps)

/-- The original formula is not valid, independently of the current closer. -/
theorem gapMemInnerNeg_notValid : ¬ Fml.Valid gapMemInnerNeg :=
  fun h => gapMemInnerNeg_countermodel (h (State.init Gaps))

#print axioms gapMemInnerNeg_falseAt
#print axioms gapMemInnerNeg_countermodel
#print axioms gapMemInnerNeg_notValid

end Solidity.Examples.MemoryNegativeCountermodel
