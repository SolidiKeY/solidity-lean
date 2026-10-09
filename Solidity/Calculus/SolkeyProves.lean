import Solidity.Calculus.SolkeyFragment
import Solidity.Calculus.Sound

/-!
# solkey's rules and the judgement

Today's `Proves.solkey_iff` and `Proves.solkey_lt_calculus`
(`Calculus/SolkeyFragment`, deleted at W4 `calc-del`) on the scoped
sequent, now that a step of `⊢ₖ` asks its rule to be solkey's
(`RuleSet.admits`, decision 36):

* a derivation of `⊢ₖ` is one of `⊢` (`Proves.toAll`);
* on the fragment a derivation of `⊢` is one of `⊢ₖ` (`Proves.toSolkey`):
  every step is admitted (`Stmt.keyStep_of_inSolkey`), and solkey's rules
  keep the goal in the fragment (`Taclet.premise_inSolkey`), so on it the
  two derive the same (`Proves.solkey_iff`);
* off it they differ (`Proves.solkey_lt_calculus`): `⊢` derives
  `[ while (false) { } ] true` by `loopExit`, and `⊢ₖ` does not, since a
  step it cannot take leaves it only `closeFalse` (`Proves.solkey_blocked`),
  which its soundness refutes.
-/

namespace Solidity

open Solidity (Modality RuleSet)

variable {C : Contract}

/-- **A derivation by solkey's rules is one of the calculus.** -/
theorem Proves.toAll {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (h : Proves C R Γ₀ H φ) : Proves C .all Γ₀ H φ := by
  induction h with
  | intro _ ih => exact .intro ih
  | allIntro _ ih => exact .allIntro ih
  | updIntro _ ih => exact .updIntro ih
  | bindIntro _ ih => exact .bindIntro ih
  | update d _ _ ih => exact .update d ih
  | unfold d _ _ ih => exact .unfold d ih
  | bind d _ _ ih => exact .bind d ih
  | split d _ _ _ ihT ihE => exact .split d ihT ihE
  | check d _ _ _ ihT ihE => exact .check d ihT ihE
  | done d _ _ ih => exact .done d ih
  | branches d hne _ _ ih => exact .branches d hne ih
  | cases d hne _ _ _ ihF ihU => exact .cases d hne ihF ihU
  | inv d _ _ _ _ ihI ihT ihE => exact .inv d ihI ihT ihE
  | inline d _ _ ih => exact .inline d ih
  | empty _ ih => exact .empty ih
  | closeTrue h => exact .closeTrue h
  | closeFalse _ ih => exact .closeFalse ih
  | close ns hlen hnd h hc hB => exact .close ns hlen hnd h hc hB
  | merge hU hW _ ih => exact .merge hU hW ih
  | updRw q hq _ ih => exact .updRw q hq ih
  | rewrite q hq _ ih => exact .rewrite q hq ih
  | closeHolds h hm => exact .closeHolds h hm

/-- A Theory rewrite keeps a formula in the fragment: it changes only the
sides of its equations. -/
theorem Fml.inSolkey_rwEqC (q : Solidity.Term C × Solidity.Term C) :
    {Γ : Ctx} → (φ : Fml C Γ) → (φ.rwEqC q).inSolkey = φ.inSolkey
  | _, .tt | _, .eq .. | _, .defined _ => rfl
  | _, .not φ => Fml.inSolkey_rwEqC q φ
  | _, .and φ ψ | _, .imp φ ψ => by
    simp only [Fml.rwEqC_and, Fml.rwEqC_imp, Fml.inSolkey, Fml.inSolkey_rwEqC q φ,
      Fml.inSolkey_rwEqC q ψ]
  | _, .upd _ _ φ | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ _ φ | _, .anon _ φ =>
    Fml.inSolkey_rwEqC q φ
  | _, .modal m P κ φ => by
    simp only [Fml.rwEqC_modal, Fml.inSolkey, Fml.inSolkey_rwEqC q φ]

/-- The first statement of a modality in the fragment is in it, and so are
the rest, the frames and the postcondition. -/
theorem Fml.inSolkey_modal_cons {m : Modality} {Γ Γ' Γ₁ Γ₂ : Ctx} {s : Stmt C Γ Γ'}
    {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
    (h : (Fml.modal m (.cons s ω) κ φ).inSolkey = true) :
    s.inSolkey m = true ∧ (Fml.modalK m ω κ φ).inSolkey = true := by
  have h' : ((s.inSolkey m && Prog.inSolkey m ω) && κ.inSolkey m && φ.inSolkey) = true := h
  simp only [Bool.and_eq_true] at h'
  refine ⟨h'.1.1.1, ?_⟩
  rw [Fml.modalK_inSolkey]
  simp only [h'.1.1.2, h'.1.2, h'.2, Bool.and_self]

/-- The premise's rule is solkey's, and the premise in the fragment, for a
statement in it. -/
theorem Stmt.premise_inSolkey_of_step {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (hs : s.inSolkey m = true) (d : s.step k m = p) :
    p.inSolkey m = true :=
  (Stmt.step_taclet hs d).premise_inSolkey hs

/-- **On the fragment, a derivation of the calculus is solkey's**: whatever
`⊢` derives about a goal whose programs are in the fragment, solkey's rules
derive alone. -/
theorem Proves.toSolkey {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (h : Proves C R Γ₀ H φ) (hφ : φ.inSolkey = true) : Proves C .solkey Γ₀ H φ := by
  induction h with
  | intro _ ih =>
    have h' : (_ && _) = true := hφ
    exact .intro (ih (Bool.and_eq_true _ _ ▸ h').2)
  | allIntro _ ih => exact .allIntro (ih hφ)
  | updIntro _ ih => exact .updIntro (ih hφ)
  | bindIntro _ ih => exact .bindIntro (ih hφ)
  | update d _ _ ih =>
    obtain ⟨hs, hω⟩ := Fml.inSolkey_modal_cons hφ
    exact .update d (ih hω) (Stmt.keyStep_of_inSolkey hs)
  | @unfold Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ _ ih =>
    obtain ⟨hs, hω⟩ := Fml.inSolkey_modal_cons hφ
    have hP : Prog.inSolkey m P = true := Stmt.premise_inSolkey_of_step hs d
    rw [Fml.modalK_inSolkey] at hω
    refine .unfold d (ih ?_) (Stmt.keyStep_of_inSolkey hs)
    show (Prog.inSolkey m P && (Prog.inSolkey m ω && κ.inSolkey m) && φ.inSolkey) = true
    simp only [Bool.and_eq_true] at hω ⊢
    exact ⟨⟨hP, hω.1⟩, hω.2⟩
  | @bind Γ Γ' Γ₁ Γ₂ H m s ω κ φ x t P d _ _ ih =>
    obtain ⟨hs, hω⟩ := Fml.inSolkey_modal_cons hφ
    have hP : Prog.inSolkey m P = true := Stmt.premise_inSolkey_of_step hs d
    rw [Fml.modalK_inSolkey] at hω
    refine .bind d (ih ?_) (Stmt.keyStep_of_inSolkey hs)
    show (Prog.inSolkey m P && (Prog.inSolkey m ω && κ.inSolkey m) && φ.inSolkey) = true
    simp only [Bool.and_eq_true] at hω ⊢
    exact ⟨⟨hP, hω.1⟩, hω.2⟩
  | @split Γ Γ₁ Γ₂ Δ₁ Δ₂ H m s ω κ φ b c c' P Q d _ _ _ ihT ihE =>
    obtain ⟨hs, hω⟩ := Fml.inSolkey_modal_cons hφ
    have hp : (c.inSolkey && c'.inSolkey && Prog.inSolkey m P && Prog.inSolkey m Q) = true :=
      Stmt.premise_inSolkey_of_step hs d
    rw [Fml.modalK_inSolkey] at hω
    simp only [Bool.and_eq_true] at hp hω
    refine .split d (ihT ?_) (ihE ?_) (Stmt.keyStep_of_inSolkey hs) <;>
      rw [Fml.modalK_inSolkey] <;>
      show (_ && (Frames.inSolkey m (.seq ω κ)) && φ.inSolkey) = true <;>
      simp only [Frames.inSolkey, Bool.and_eq_true]
    · exact ⟨⟨hp.1.2, hω.1⟩, hω.2⟩
    · exact ⟨⟨hp.2, hω.1⟩, hω.2⟩
  | @check Γ Γ₁ Γ₂ H m s ω κ φ c d _ _ _ ihT ihE =>
    obtain ⟨hs, hω⟩ := Fml.inSolkey_modal_cons hφ
    have hc : c.inSolkey = true := Stmt.premise_inSolkey_of_step hs d
    exact .check d (ihT hω) (ihE hc) (Stmt.keyStep_of_inSolkey hs)
  | @done Γ Γ' Γ₁ Γ₂ H m s ω κ φ b d _ _ ih =>
    obtain ⟨hs, _⟩ := Fml.inSolkey_modal_cons hφ
    exact .done d (ih (by cases b <;> rfl)) (Stmt.keyStep_of_inSolkey hs)
  | branches d _ _ _ _ =>
    obtain ⟨hs, _⟩ := Fml.inSolkey_modal_cons hφ
    exact absurd (Stmt.premise_inSolkey_of_step hs d) Bool.false_ne_true
  | @cases Γ Γ₁ Γ₂ H m s ω κ φ fs us d hne _ _ _ ihF ihU =>
    obtain ⟨hs, hω⟩ := Fml.inSolkey_modal_cons hφ
    have hf : fs.all Fml.inSolkey = true := Stmt.premise_inSolkey_of_step hs d
    rw [List.all_eq_true] at hf
    exact .cases d hne (fun f hm => ihF f hm (hf f hm)) (fun U hU => ihU U hU hω)
      (Stmt.keyStep_of_inSolkey hs)
  | inv d _ _ _ _ _ _ _ =>
    obtain ⟨hs, _⟩ := Fml.inSolkey_modal_cons hφ
    exact absurd (Stmt.premise_inSolkey_of_step hs d) Bool.false_ne_true
  | @inline Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ _ ih =>
    obtain ⟨hs, hω⟩ := Fml.inSolkey_modal_cons hφ
    have hP : Prog.inSolkey m P = true := Stmt.premise_inSolkey_of_step hs d
    rw [Fml.modalK_inSolkey] at hω
    refine .inline d (ih ?_) (Stmt.keyStep_of_inSolkey hs)
    show (Prog.inSolkey m P && (Prog.inSolkey m ω && κ.inSolkey m) && φ.inSolkey) = true
    simp only [Bool.and_eq_true] at hω ⊢
    exact ⟨⟨hP, hω.1⟩, hω.2⟩
  | @empty Γ Γ₂ H m κ φ _ ih =>
    have h' : ((Prog.inSolkey m (.nil : Prog C Γ Γ) && κ.inSolkey m) && φ.inSolkey) = true := hφ
    exact .empty (ih (by rw [Frames.exit_inSolkey]; simpa only [Prog.inSolkey, Bool.true_and] using h'))
  | closeTrue h => exact .closeTrue h
  | closeFalse _ ih => exact .closeFalse (ih rfl)
  | close ns hlen hnd h hc hB => exact .close ns hlen hnd h hc hB
  | merge hU hW _ ih => exact .merge hU hW (ih hφ)
  | updRw q hq _ ih => exact .updRw q hq (ih hφ)
  | rewrite q hq _ ih => exact .rewrite q hq (ih (by rw [Fml.inSolkey_rwEqC]; exact hφ))
  | closeHolds h hm => exact .closeHolds h hm

/-- **On the fragment, solkey's rules derive exactly what the calculus
does** (today's `Proves.solkey_iff`). -/
theorem Proves.solkey_iff {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (hφ : φ.inSolkey = true) :
    Proves C .solkey Γ₀ H φ ↔ Proves C .all Γ₀ H φ :=
  ⟨Proves.toAll, fun h => h.toSolkey hφ⟩

/-! ## Off the fragment -/

/-- A modality whose first statement `⊢ₖ` has no rule for. -/
def Fml.blockedK : {Γ : Ctx} → Fml C Γ → Bool
  | _, .modal m (.cons s _) _ _ => !s.keyStep m
  | _, _ => false

/-- A sequent with no modality left has none in its formula. -/
theorem Hyps.modalFree_wrap {Γ₀ : Ctx} : {Γ : Ctx} → (H : Hyps C Γ₀ Γ) → {φ : Fml C Γ} →
    (H.wrap φ).modalFree = true → φ.modalFree = true
  | _, .nil, _, h => h
  | _, .pre H a, φ, h => by
    have h' : (Fml.imp a φ).modalFree = true := Hyps.modalFree_wrap H h
    exact (Bool.and_eq_true _ _ ▸ h').2
  | _, .upd H _ _, _, h => Hyps.modalFree_wrap H (φ := .upd _ _ _) h
  | _, .havoc H, _, h => Hyps.modalFree_wrap H (φ := .havoc _) h
  | _, .all H _ _, _, h => Hyps.modalFree_wrap H (φ := .all _ _ _) h
  | _, .bind H _ _ _, _, h => Hyps.modalFree_wrap H (φ := .bind _ _ _ _) h
  | _, .anon H _, _, h => Hyps.modalFree_wrap H (φ := .anon _ _) h

/-- A sequent `close` takes has no modality left in its formula. -/
theorem Hyps.closable_wrap {Γ₀ : Ctx} : {Γ : Ctx} → (H : Hyps C Γ₀ Γ) → {φ : Fml C Γ} →
    {ns : List Var} → (H.wrap φ).Closable ns → ∃ ns', φ.Closable ns'
  | _, .nil, _, _, h => ⟨_, h⟩
  | _, .pre H a, _, _, h => by
    obtain ⟨_, h'⟩ := Hyps.closable_wrap H h
    exact ⟨_, (h' : _ ∧ _).2⟩
  | _, .upd H _ _, _, _, h => by
    obtain ⟨_, h'⟩ := Hyps.closable_wrap H h
    exact ⟨_, (h' : _ ∧ _ ∧ _ ∧ _).2.2.2⟩
  | _, .havoc H, _, _, h => Hyps.closable_wrap H (φ := .havoc _) h
  | _, .anon H _, _, _, h => Hyps.closable_wrap H (φ := .anon _ _) h
  | _, .all H _ _, _, _, h | _, .bind H _ _ _, _, _, h => by
    obtain ⟨_, h'⟩ := Hyps.closable_wrap H h
    exact ⟨_, (h' : _ ∧ _ ∧ _).2.2⟩

/-- **A step `⊢ₖ` cannot take leaves it nothing but `closeFalse`**: a
derivation by solkey's rules of a modality whose first statement has no rule
of solkey's is a refutation of its context. -/
theorem Proves.solkey_blocked {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (h : Proves C .solkey Γ₀ H φ) (hφ : φ.blockedK = true) : Proves C .solkey Γ₀ H .ff := by
  induction h with
  | update _ _ hR _ | unfold _ _ hR _ | bind _ _ hR _ | split _ _ _ hR _ _ | check _ _ _ hR _ _
  | done _ _ hR _ | branches _ _ _ hR _ | cases _ _ _ _ hR _ _ | inv _ _ _ _ hR _ _ _
  | inline _ _ hR _ =>
    have h' : (!RuleSet.admits .solkey _ _) = true := hφ
    rw [hR] at h'
    exact absurd h' Bool.false_ne_true
  | intro | allIntro | updIntro | bindIntro | empty | closeTrue =>
    exact absurd hφ Bool.false_ne_true
  | closeFalse h _ => exact h
  | @close Γ H φ ns _ _ _ hc _ =>
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hc
    obtain ⟨_, hφ'⟩ := Hyps.closable_wrap H (Fml.bindsB_sound _ hB).1
    cases φ with
    | modal => exact hφ'.elim
    | _ => exact absurd hφ Bool.false_ne_true
  | @closeHolds Γ H φ _ hm =>
    have hφ' := Hyps.modalFree_wrap H hm
    cases φ with
    | modal => exact absurd hφ' Bool.false_ne_true
    | _ => exact absurd hφ Bool.false_ne_true
  | merge hU hW _ ih => exact .merge hU hW (ih hφ)
  | updRw q hq _ ih => exact .updRw q hq (ih hφ)
  | @rewrite Γ H φ q hq _ ih =>
    refine .rewrite q hq (ih ?_)
    cases φ with
    | modal m P κ ψ => cases P <;> exact hφ
    | _ => exact absurd hφ Bool.false_ne_true

/-- `[ while (false) { } ] true`, the loop unwound at most `0` times. -/
def loopFalse : Fml C [] :=
  .modal .box (.cons (.loop (.unwind 0) (.simple (.bool false)) .nil) .nil) .nil .tt

/-- The calculus derives it: `loopExit`, the rest (nothing) with the
condition false assumed, and that it is false. -/
theorem loopFalse_derived : Proves C .all [] .nil (loopFalse (C := C)) := by
  refine .check (LeanTaclet.toStep .loopExit) (.closeTrue rfl)
    (.closeHolds (fun _ => ⟨⟨_, rfl⟩, ⟨_, rfl⟩, Theory.StValue.Equiv.refl _⟩))

/-- **Off the fragment solkey's rules fall short**: the calculus derives
`[ while (false) { } ] true`, solkey's rules do not (today's
`Proves.solkey_lt_calculus`). -/
theorem Proves.solkey_lt_calculus :
    ∃ φ : Fml C [], Proves C .all [] .nil φ ∧ ¬ Proves C .solkey [] .nil φ :=
  ⟨loopFalse, loopFalse_derived, fun h =>
    (Proves.sound (h.solkey_blocked rfl) (State.init C) : ¬ True) trivial⟩

end Solidity
