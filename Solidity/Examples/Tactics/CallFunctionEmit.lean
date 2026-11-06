import Solidity.Calculus.CallFunctionEmit
import Solidity.Calculus.CallFunctionLeafMetrics

/-! # Checked-plan acceptance, refusal and semantic controls
Concrete producer results, not only generic laws for hypothetical plans.
-/
namespace Solidity.Examples.Tactics.CallFunctionEmit
open Solidity.CallFunctionPlan Solidity.CallFunctionTable Solidity.CallFunctionEmit
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private def name : Var := .fresh "same" 0
private def affine {Δ : Ctx} (x : Val C Δ .uint) : Val C Δ .uint :=
  .binop .add rfl rfl (.binop .mul rfl rfl x (.simple (.lit 3 rfl))) (.simple (.lit 1 rfl))
private def base : Tm C (.val .uint :: Γ) (.val .uint) :=
  (affine (.simple (.local .here))).lower
private def nested (n : Nat) (v : Val C Γ .uint) : Val C Γ .uint :=
  match n with
  | 0 => v
  | n+1 => affine (nested n v)
private def oldTerm (k : Nat) : Tm C Γ (.val .uint) :=
  (nested (2^k) (.simple (.local (.there .here)))).lower
private def original (n : Nat) : State C Γ :=
  (({ State.init C with selfBalance := uintOfNat 5 }).push
    (t := .val .uint) (uintOfNat n)).push (t := .val .uint) (uintOfNat 99)
private def post (n : Nat) : Fml C Γ := .eq (.pvV .here) (.app0 (.lit (uintOfNat n)))

private def expectedSix : Nat := (5*3^64-1)/2

/-- Actual checked old-term evaluation supplies the result used by semantic
emission controls; this is not injected into a future interface. -/
theorem valueSix : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := by
  decide +kernel

/-- Small families keep their old smaller leaf rather than paying table overhead. -/
theorem smallRefusal :
    (emit? .box .here (oldTerm 1) (post 22)).isSome = false ∧
    (emit? .box .here (oldTerm 5) (post 22)).isSome = false := by decide +kernel

/-- The first crossover family produces a real emission for either modality. -/
theorem emitsSix (m : Modality) :
    (emit? m .here (oldTerm 6) (post expectedSix)).isSome = true := by
  cases m <;> decide +kernel

/-- Actual selected full formula sizes and contexts, not a walk-node proxy. -/
theorem actualSizes :
    (emit? .box .here (oldTerm 6) (post expectedSix)).map (fun e =>
      (e.formula.tmSize, Solidity.CallFunctionLeaf.contextPeak e.formula)) = some (256,11) ∧
    (emit? .diamond .here (oldTerm 6) (post expectedSix)).map (fun e =>
      (e.formula.tmSize, Solidity.CallFunctionLeaf.contextPeak e.formula)) = some (257,11) ∧
    (Solidity.CallFunctionEmit.original .box .here (oldTerm 6) (post expectedSix)).tmSize = 262 := by
  decide +kernel

/-- Actual emissions have inhabited successful old-observation semantics. -/
theorem emittedReturns (m : Modality) : ∃ e : Emission m .here (oldTerm 6) (post expectedSix),
    emit? m .here (oldTerm 6) (post expectedSix) = some e ∧ holds (original 2) e.formula := by
  have hf : (emit? m .here (oldTerm 6) (post expectedSix)).isSome = true := emitsSix m
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hf hv ⊢
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hf
  refine ⟨e, he, ?_⟩
  exact (e.holds (original 2)).mpr
    ((holds_original_of_eval m .here t (post expectedSix) (original 2)
      (uintOfNat expectedSix) hv).mpr rfl)

/-- The wrong result is false for every emitted formula for that exact old leaf. -/
theorem emittedWrong (m : Modality)
    (e : Emission m .here (oldTerm 6) (post (expectedSix+1))) :
    ¬ holds (original 2) e.formula := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at e hv
  intro hh
  have hu : holds (original 2)
      (Solidity.CallFunctionEmit.original m .here t (post (expectedSix+1))) :=
    (e.holds (original 2)).mp hh
  have hp : holds ((original 2).setLocal .here (uintOfNat expectedSix)) (post (expectedSix+1)) :=
    (holds_original_of_eval m .here t (post (expectedSix+1)) (original 2)
      (uintOfNat expectedSix) hv).mp hu
  have neq : uintOfNat expectedSix ≠ uintOfNat (expectedSix+1) := by decide +kernel
  exact neq (Option.some.inj hp)

/-- The wrong-post emission is actually produced for both modalities, so
the negative observation control is not vacuous. -/
theorem emitsWrongSix (m : Modality) :
    (emit? m .here (oldTerm 6) (post (expectedSix+1))).isSome = true := by
  cases m <;> decide +kernel

/-- An actual returned wrong-post formula has the original inhabited state
as a kernel-certified countermodel. -/
theorem emittedWrongWitness (m : Modality) :
    ∃ e : Emission m .here (oldTerm 6) (post (expectedSix+1)),
      emit? m .here (oldTerm 6) (post (expectedSix+1)) = some e ∧
      ¬ holds (original 2) e.formula := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (emitsWrongSix m)
  exact ⟨e, he, emittedWrong m e⟩

private def bigPost : Fml C Γ := Nat.rec Fml.tt (fun _ φ => .and .tt φ) 200

/-- A real candidate would shrink but exceeds the complete output cap. -/
theorem capRefusal :
    (Solidity.CallFunctionSearch.search? (oldTerm 6)).isSome = true ∧
    ((Solidity.CallFunctionSearch.search? (oldTerm 6)).map (fun p =>
      (p.leaf .box tableName inputName resultName .here bigPost).tmSize)) = some 654 ∧
    (Solidity.CallFunctionEmit.original .box .here (oldTerm 6) bigPost).tmSize = 660 ∧
    (emit? .box .here (oldTerm 6) bigPost).isSome = false := by decide +kernel

private def boundaryPost : Fml C Γ := Nat.rec Fml.tt (fun _ φ => .and .tt φ) 129

/-- The exact complete-output boundary accepts512 and rejects513, even
though the larger candidate would still shrink its original leaf. -/
theorem capBoundary :
    (emit? .box .here (oldTerm 6) boundaryPost).map (fun e => e.formula.tmSize) = some 512 ∧
    (Solidity.CallFunctionSearch.search? (oldTerm 6)).map (fun p =>
      (p.leaf .box tableName inputName resultName .here (.not boundaryPost)).tmSize) = some 513 ∧
    (emit? .box .here (oldTerm 6) (.not boundaryPost)).isSome = false := by decide +kernel

/-- Refused replacement is definitionally the actual original formula. -/
theorem refusedUnchanged : replace .box .here (oldTerm 1) (post 22) =
    Solidity.CallFunctionEmit.original .box .here (oldTerm 1) (post 22) := by
  rfl

end Solidity.Examples.Tactics.CallFunctionEmit
