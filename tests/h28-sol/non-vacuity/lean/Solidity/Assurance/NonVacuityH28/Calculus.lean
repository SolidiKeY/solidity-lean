import Solidity.Theorems

/-! Nonempty assertion derivations, not a hypothesis implying itself. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

def assertion : Prog C [] [] := .cons (.assert (.simple (.bool true))) .nil
def assertionSpec : Spec C [] := .diamond (assertion C) .tt

theorem assertion_runs (σ : State C []) :
    Prog.run σ (assertion C) = .ok ⟨σ, List.prefix_refl _⟩ := rfl

theorem assertion_derivation (R : RuleSet) :
    Proves C R [] .nil (assertionSpec C).toFml :=
  .check rfl (.closeTrue rfl) (.closeHolds (fun _ => rfl) rfl) (by cases R <;> rfl)

theorem calculus_application : Fml.Valid (assertionSpec C).toFml :=
  Main.soundness (assertion_derivation C .all)

theorem direct_application : Spec.Valid (assertionSpec C) :=
  Main.soundness' (assertion_derivation C .all)

theorem solkey_application : Spec.Valid (assertionSpec C) :=
  Main.solkey_soundness (assertion_derivation C .solkey)

theorem callback_application : Spec.ValidC (Invariant.top (C := C)) (assertionSpec C) true :=
  Main.callback_soundness (.plain (assertion_derivation C .all) rfl)

theorem noCallback_application : Spec.ValidC (Invariant.top (C := C)) (assertionSpec C) false :=
  Main.noCallback_soundness (.plain (assertion_derivation C .all) rfl)

theorem noCallback_equivalence : ValidC (Invariant.top (C := C)) (assertionSpec C).toFml false :=
  (Main.noCallback_iff rfl).2 (calculus_application C)

theorem cleanTail_application : holds (State.init C) (assertionSpec C).toFml :=
  Main.cleanTail_holds (φ := (assertionSpec C).toFml)
    (fun σ _ => calculus_application C σ) (State.init C)
    (Storage.init_cleanTail C)

theorem symex_application (σ : State C []) : holds σ (assertionSpec C).toFml :=
  Main.symex_sound 1 σ ⟨fun _ => True.intro, rfl⟩

theorem solkey_equivalence :
    Proves C .solkey [] .nil (assertionSpec C).toFml ↔
      Proves C .all [] .nil (assertionSpec C).toFml :=
  Main.solkey_eq_calculus rfl

theorem solkey_strict : ∃ φ : Fml C [], Proves C .all [] .nil φ ∧
    ¬ Proves C .solkey [] .nil φ := Main.solkey_lt_calculus

theorem solkey_rule_application :
    Taclet C 0 .diamond (.assert (.simple (.bool true)) : Stmt C [] [])
      ((Stmt.assert (.simple (.bool true)) : Stmt C [] []).step 0 .diamond) :=
  Main.solkey_rule_exists rfl rfl

theorem solkey_admission_application :
    Taclet C 0 .diamond (.assert (.simple (.bool true)) : Stmt C [] [])
      ((Stmt.assert (.simple (.bool true)) : Stmt C [] []).step 0 .diamond) :=
  Main.solkey_step_taclet rfl rfl

theorem zero_unwind_strict (m : Modality) :
    (∃ p, Rule C 0 m (.loop (.unwind 0) (.simple (.bool false)) (.nil : Prog C [] [])) p) ∧
      ∀ p, ¬ Taclet C 0 m (.loop (.unwind 0) (.simple (.bool false)) (.nil : Prog C [] [])) p :=
  Main.solkey_rule_lt_calculus 0 m (.simple (.bool false)) .nil

/-- In particular a false invariant cannot discharge the entry obligation. -/
theorem false_invariant_entry_rejected : ¬ Proves C .all [] .nil .ff := by
  intro h
  exact Main.soundness h (State.init C) True.intro

def falseAnnotatedLoop : Prog C [] [] :=
  .cons (.loop (.inv (.simple (.bool false)) none false []) (.simple (.bool false)) .nil) .nil

theorem false_annotation_run (σ : State C []) :
    Prog.run σ (falseAnnotatedLoop C) = .ok ⟨σ, List.prefix_refl _⟩ := by
  have hl : Stmt.run σ
      (.loop (.inv (.simple (.bool false)) none false []) (.simple (.bool false))
        (.nil : Prog C [] [])) = .ok ⟨σ, List.prefix_refl _⟩ :=
    TLoop.run_of_iterN (n := 1) rfl
  change TRun.seq (Stmt.runR
    (.loop (.inv (.simple (.bool false)) none false []) (.simple (.bool false))
      (.nil : Prog C [] []))) TRun.nil σ = _
  simp only [TRun.seq, hl]
  rfl

/-- The false annotated invariant fails its entry proof even for a terminating loop. -/
theorem false_annotation_entry :
    ¬ Proves C .all [] .nil (Fml.isBool (Simple.lower (.bool false)) true) := by
  intro h
  have hb : holds (State.init C) (Fml.isBool (Simple.lower (.bool false)) true) :=
    Main.soundness h (State.init C)
  change (some false : Option Bool) = some true at hb
  cases hb

theorem false_annotation_rule (k : Nat) :
    (Stmt.loop (.inv (.simple (.bool false)) none false []) (.simple (.bool false))
      (.nil : Prog C [] [])).step k .box =
      .inv (invFml (.simple (.bool false)) []) none [] (some [])
        (Upd.nil.decl (fse k) (.val (p := .bool) (Simple.lower (.bool false))))
        (.isBool (.pvV (p := .bool) .here) true) (.isBool (.pvV (p := .bool) .here) false)
        .refl (.push .refl) .nil (invFml (.simple (.bool false)) []) := rfl

theorem false_annotation_init_rejected :
    ¬ Proves C .all [] .nil ((invFml (.simple (.bool false)) []).invHyp none) :=
  false_annotation_entry C

/-- The rule's semantic implication is applied with a true antecedent. -/
theorem assertion_rule_semantics (σ : State C []) :
    holds σ (((Stmt.assert (.simple (.bool true)) : Stmt C [] []).step 0 .diamond).fml
      .diamond .nil .nil .tt) ∧ holds σ (assertionSpec C).toFml := by
  have hp : holds σ (((Stmt.assert (.simple (.bool true)) : Stmt C [] []).step 0 .diamond).fml
      .diamond .nil .nil .tt) := ⟨fun _ => True.intro, rfl⟩
  exact ⟨hp, Main.rule_sound (Main.rule_exists 0 .diamond
    (Stmt.assert (.simple (.bool true)) : Stmt C [] [])) σ .nil .nil .tt hp⟩

theorem competing_assertion_rule_rejected :
    ¬ Rule C 0 .diamond (.assert (.simple (.bool true)) : Stmt C [] []) (.done false) := by
  intro h
  have heq : (Stmt.assert (.simple (.bool true)) : Stmt C [] []).step 0 .diamond = .done false :=
    Main.rule_is_step h
  cases heq

theorem symex_actual_progress : symex 1 (assertionSpec C).toFml ≠ (assertionSpec C).toFml := by
  intro h
  cases h

end Solidity.Assurance.NonVacuityH28
