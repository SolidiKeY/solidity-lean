import Solidity.Calculus.CallFunctionTransform
import Solidity.Calculus.CallFunctionLeafMetrics

/-! # Checked-plan acceptance, refusal and semantic controls
Concrete producer results, not only generic laws for hypothetical plans.
-/
namespace Solidity.Examples.Tactics.CallFunctionTransform
open Solidity.CallFunctionPlan Solidity.CallFunctionTable Solidity.CallFunctionEmit Solidity.CallFunctionTransform
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

/-- Checked actual evaluation shared by the contextual semantic controls. -/
theorem valueSix : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := by decide +kernel

private def oldLeaf (m : Modality) (out : Tm C Γ (.val .uint)) (φ : Fml C Γ) : Fml C Γ :=
  Solidity.CallFunctionEmit.original m .here out φ
private def combination (m : Modality) (out : Tm C Γ (.val .uint)) : Fml C Γ :=
  .and (oldLeaf m out .tt) (.not (oldLeaf m out .ff))

/-- Negative and positive formula positions both receive actual full replacements. -/
theorem contextualSizes :
    (combination .box (oldTerm 6)).tmSize = 523 ∧
    (transform (combination .box (oldTerm 6))).tmSize = 511 ∧
    (combination .diamond (oldTerm 6)).tmSize = 523 ∧
    (transform (combination .diamond (oldTerm 6))).tmSize = 513 := by decide +kernel

/-- The original inhabited state satisfies the combined positive/negative
context, and therefore its actual transformed complete leaf. -/
theorem combinedTrue (m : Modality) : holds (original 2)
    (transform (combination m (oldTerm 6))) := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hv ⊢
  apply (holds_transform (combination m t) (original 2)).mpr
  constructor
  · exact (holds_original_of_eval m .here t .tt (original 2) (uintOfNat expectedSix) hv).mpr trivial
  · intro hh
    exact ((holds_original_of_eval m .here t .ff (original 2) (uintOfNat expectedSix) hv).mp hh) trivial

/-- A false observation stays false through a surrounding conjunction. -/
theorem combinedFalse (m : Modality) : ¬ holds (original 2)
    (transform (.and (oldLeaf m (oldTerm 6) .tt) (oldLeaf m (oldTerm 6) .ff))) := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hv ⊢
  intro hh
  have ho : holds (original 2) (.and (oldLeaf m t .tt) (oldLeaf m t .ff)) :=
    (holds_transform (.and (oldLeaf m t .tt) (oldLeaf m t .ff)) (original 2)).mp hh
  exact ((holds_original_of_eval m .here t .ff (original 2) (uintOfNat expectedSix) hv).mp ho.2) trivial

/-- A parallel pair is not silently reinterpreted as one call-result update. -/
theorem parallelRefusal :
    (classify? (C := C)
      ((Upd.nil.snoc (.local (.here : Idx Γ (.val .uint)) (.val (oldTerm 6)))).snoc
        (.local (.there .here) (.val (.app0 (.lit (uintOfNat 13))))))).isSome = false := rfl

private abbrev IΓ : Ctx := [.val .int]
private def intUpdate : Upd C IΓ IΓ :=
  Upd.nil.snoc (.local .here (.val (.app0 (.lit (p := .int) ⟨-7, rfl⟩))))

/-- Unsupported primitive profile retains its actual original formula. -/
theorem signedRefusal : (classify? intUpdate).isSome = false ∧
    transform (Fml.upd .box intUpdate (.tt : Fml C IΓ)) = .upd .box intUpdate .tt := ⟨rfl, rfl⟩

private def declPost : Fml C (.val .uint :: Γ) :=
  .and (.eq (.pvV .here) (.app0 (.lit (uintOfNat 17))))
    (.eq (.pvV (.there .here)) (.app0 (.lit (uintOfNat 99))))
private def declLeaf (m : Modality) : Fml C Γ :=
  .upd m (CallResultCapture.capture name (.app0 (.lit (uintOfNat 17)))) declPost

/-- A real context-extending declaration remains correctly typed and keeps
its new head distinct from a same-named original target. -/
theorem declaredHead (m : Modality) : holds (original 2) (transform (declLeaf m)) := by
  apply (holds_transform (declLeaf m) (original 2)).mpr
  apply (CallFunctionOperationalBase.capture_of_eval m name (.app0 (.lit (uintOfNat 17)))
    declPost (original 2) (uintOfNat 17) rfl).mpr
  exact ⟨rfl, rfl⟩

/-- Actual classification distinguishes context extension from assignment. -/
theorem declarationRefusal :
    (classify? (CallResultCapture.capture name
      (Tm.app0 (C := C) (Γ := Γ) (.lit (uintOfNat 17))))).isSome = false := rfl

private def boundLeaf (m : Modality) (out : Tm C Γ (.val .uint))
    (φ : Fml C (.oldNet :: Γ)) : Fml C Γ :=
  .bind m name .oldNet
    (.upd m (Upd.nil.snoc (.local (.there .here) (.val (out.wk (.drop .refl))))) φ)

/-- A real old-net binder changes the context around the emitted call leaf;
its full formula shrinks while keeping the old post in its own context. -/
theorem binderSizes : (boundLeaf .box (oldTerm 6) .tt).tmSize = 261 ∧
    (transform (boundLeaf .box (oldTerm 6) .tt)).tmSize = 255 ∧
    Solidity.CallFunctionLeaf.contextPeak (transform (boundLeaf .box (oldTerm 6) .tt)) = 12 := by
  decide +kernel

/-- Arbitrary fresh ledger data cannot change original input evaluation. -/
theorem underBinderTrue (m : Modality) :
    holds (original 2) (transform (boundLeaf m (oldTerm 6) .tt)) := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hv ⊢
  apply (holds_transform (boundLeaf m t .tt) (original 2)).mpr
  intro L
  have he : (t.wk (.drop .refl)).eval ((original 2).push (t := .oldNet) L) =
      some (uintOfNat expectedSix) :=
    (Tm.eval_wk_push (t := .oldNet) (original 2) L t).trans hv
  exact (holds_original_of_eval m (.there .here) (t.wk (.drop .refl)) .tt
    ((original 2).push (t := .oldNet) L) (uintOfNat expectedSix) he).mpr trivial

/-- The same binder has a real inhabited ledger instance refuting a false post. -/
theorem underBinderFalse (m : Modality) :
    ¬ holds (original 2) (transform (boundLeaf m (oldTerm 6) .ff)) := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hv ⊢
  intro hh
  have ho : holds (original 2) (boundLeaf m t .ff) :=
    (holds_transform (boundLeaf m t .ff) (original 2)).mp hh
  have he : (t.wk (.drop .refl)).eval ((original 2).push (t := .oldNet) ([] : Ledger)) =
      some (uintOfNat expectedSix) :=
    (Tm.eval_wk_push (t := .oldNet) (original 2) ([] : Ledger) t).trans hv
  exact ((holds_original_of_eval m (.there .here) (t.wk (.drop .refl)) .ff
    ((original 2).push (t := .oldNet) ([] : Ledger)) (uintOfNat expectedSix) he).mp (ho [])) trivial

/-- Contravariant placement is preserved, not merely positive occurrences. -/
theorem antecedentTrue (m : Modality) : holds (original 2)
    (transform (.imp (oldLeaf m (oldTerm 6) .ff) .ff)) := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hv ⊢
  apply (holds_transform (.imp (oldLeaf m t .ff) .ff) (original 2)).mpr
  intro hh
  exact (holds_original_of_eval m .here t .ff (original 2) (uintOfNat expectedSix) hv).mp hh

/-- A true original antecedent cannot become a false one to hide a countermodel. -/
theorem antecedentFalse (m : Modality) : ¬ holds (original 2)
    (transform (.imp (oldLeaf m (oldTerm 6) .tt) .ff)) := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hv ⊢
  intro hh
  have ho : holds (original 2) (.imp (oldLeaf m t .tt) .ff) :=
    (holds_transform (.imp (oldLeaf m t .tt) .ff) (original 2)).mp hh
  have hp : holds (original 2) (oldLeaf m t .tt) :=
    (holds_original_of_eval m .here t .tt (original 2) (uintOfNat expectedSix) hv).mpr trivial
  exact ho hp trivial

/-- A genuine typed program modality retains its caller and frames while its
post's actual call leaf is replaced. The program body itself is untouched. -/
theorem underProgramModal (m : Modality) : holds (original 2)
    (transform (.modal m (.nil : Prog C Γ Γ) .nil (oldLeaf m (oldTerm 6) .tt))) := by
  have hv : (oldTerm 6).eval (original 2) = some (uintOfNat expectedSix) := valueSix
  generalize ht : oldTerm 6 = t at hv ⊢
  apply (holds_transform (.modal m (.nil : Prog C Γ Γ) .nil (oldLeaf m t .tt)) (original 2)).mpr
  change holds (original 2) (oldLeaf m t .tt) ∧ _
  exact ⟨(holds_original_of_eval m .here t .tt (original 2) (uintOfNat expectedSix) hv).mpr trivial,
    by intro hh; cases hh⟩

end Solidity.Examples.Tactics.CallFunctionTransform
