import Solidity.Calculus.Core.TLogic
import Solidity.Calculus.Core.CloseErase

/-!
# A goal closed by its erasure's validity, over the typed state

`tholds_of_erase_valid`: `Calculus/Core/CloseErase.lean`'s
`holds_of_erase_valid` gives a leaf in M3's state the typed state erases to
(`TState.erase`), and a leaf (`Fml.Leaf`, `Calculus/Core/Closable.lean`)
holds over the typed state where it holds over its erasure
(`tholds_of_holds`): every binder of the typed reading ranges over values
whose erasures M3's ranges over, an update's typed reading asks of the
states that erase to the one M3's reaches, and a first-order formula
(`Fml.FO`, where a leaf assumes) reads the same on both
(`tholds_iff_holds`).  `Proves.close` (`Calculus/Core/Proves.lean`) is this,
behind a context.
-/

namespace Solidity.Core

open Solidity (Modality Avoids)

variable {C : Contract}

/-! ## The typed state erased -/

theorem _root_.Solidity.PrimTy.admits_erase : {p : PrimTy} → (v : p.Denote) → p.admits (PrimTy.erase v)
  | .bool, _ => trivial
  | .uint, ⟨_, h⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h
  | .int, ⟨_, h⟩ => by
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h

theorem _root_.Solidity.PrimTy.exists_of_admits :
    {p : PrimTy} → {v : Semantics.Value} → p.admits v → ∃ w : p.Denote, PrimTy.erase w = v
  | .bool, .bool b, _ => ⟨b, rfl⟩
  | .uint, .int n, h =>
    ⟨(⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h⟩ :
      {n : Int // PrimTy.uint.inRange n = true}), rfl⟩
  | .int, .int n, h =>
    ⟨(⟨n, by
        simp only [PrimTy.inRange, decide_eq_true_eq]
        exact h⟩ :
      {n : Int // PrimTy.int.inRange n = true}), rfl⟩
  | .bool, .int _, h | .uint, .bool _, h | .int, .bool _, h => h.elim

theorem LTy.boolOK_erase {H : HTy} : (t : LTy) → (v : t.TDenote C H) →
    LTy.BoolOK (C := C) t (LTy.TDenote.erase t v)
  | .val .bool, v => ⟨v, rfl⟩
  | .val .uint, _ | .val .int, _ | .alias _, _ | .mem _, _ | .old, _ | .oldNet, _ => trivial

theorem TEnv.erase_boolOK {H : HTy} : (Γ : Ctx) → (e : TEnv C H Γ) →
    Env.All (LTy.BoolOK (C := C)) (TEnv.erase Γ e)
  | [], _ => trivial
  | t :: Γ, e => ⟨LTy.boolOK_erase t e.1, TEnv.erase_boolOK Γ e.2⟩

/-- A typed state's `bool` locals hold `bool`s. -/
theorem TState.erase_boolOK {Γ : Ctx} (σ : TState C Γ) : σ.erase.BoolOK :=
  TEnv.erase_boolOK Γ σ.env

theorem TState.havoc_erase {Γ : Ctx} (σ : TState C Γ) (st : Storage C) (nt : List (Int × Int)) :
    (σ.havoc st nt).erase = σ.erase.withGlob (σ.erase.glob.havoc st.erase nt) := rfl

theorem TState.anon_erase {Γ : Ctx} (σ : TState C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.TDenote C σ.H) :
    (σ.anon xs b).erase = σ.erase.anon xs fun x => LTy.TDenote.erase x.1 (b x) := by
  have key : ∀ (ys : List ((t : LTy) × Idx Γ t)) (e : TEnv C σ.H Γ),
      (σ.withEnv (ys.foldl (fun e x => TEnv.set x.2 (b x) e) e)).erase =
        ys.foldl (fun τ x => τ.setLocal x.2 (LTy.TDenote.erase x.1 (b x))) (σ.withEnv e).erase := by
    intro ys
    induction ys with
    | nil => intro e; rfl
    | cons x ys ih =>
      intro e
      rw [List.foldl_cons, List.foldl_cons, ih]
      exact congrArg (fun τ => List.foldl _ τ ys) (TState.setLocal_erase (σ.withEnv e) x.2 (b x))
  exact key xs σ.env

/-! ## Typed and erased readings -/

theorem _root_.Solidity.Modality.afterC_imp {α : Type} {m : Modality} {p q : α → Prop}
    {r : Semantics.Res α} (h : m.afterC p r) (hpq : ∀ a, p a → q a) : m.afterC q r := by
  cases r with
  | ok a => exact hpq a h
  | error _ => exact h

/-- **A first-order formula reads the same** over a typed state and its
erasure. -/
theorem tholds_iff_holds : {Γ : Ctx} → (φ : Fml C Γ) → φ.FO = true → (σ : TState C Γ) →
    (tholds σ φ ↔ holds σ.erase φ)
  | _, .tt, _, _ => Iff.rfl
  | _, .eq _ _, _, _ => Iff.rfl
  | _, .defined _, _, _ => Iff.rfl
  | _, .not φ, h, σ => not_congr (tholds_iff_holds φ h σ)
  | _, .and φ ψ, h, σ => by
    have h' : φ.FO = true ∧ ψ.FO = true := Bool.and_eq_true_iff.mp h
    exact and_congr (tholds_iff_holds φ h'.1 σ) (tholds_iff_holds ψ h'.2 σ)
  | _, .imp φ ψ, h, σ => by
    have h' : φ.FO = true ∧ ψ.FO = true := Bool.and_eq_true_iff.mp h
    exact imp_congr (tholds_iff_holds φ h'.1 σ) (tholds_iff_holds ψ h'.2 σ)
  | _, .all _ p φ, h, σ => by
    show (∀ v : p.Denote, tholds (σ.push (t := .val p) v) φ) ↔
      ∀ v, p.admits v → holds (σ.erase.push (t := .val p) v) φ
    constructor
    · intro hv v ha
      obtain ⟨w, rfl⟩ := PrimTy.exists_of_admits ha
      exact (tholds_iff_holds φ h (σ.push (t := .val p) w)).1 (hv w)
    · intro hv w
      exact (tholds_iff_holds φ h (σ.push (t := .val p) w)).2 (hv _ (PrimTy.admits_erase w))
  | _, .upd .., h, _ | _, .modal .., h, _ | _, .havoc _, h, _ | _, .bind .., h, _
  | _, .anon .., h, _ => nomatch h

/-- **A leaf that holds over the erasure holds over the typed state.** -/
theorem tholds_of_holds : {Γ : Ctx} → (φ : Fml C Γ) → φ.Leaf = true → (σ : TState C Γ) →
    holds σ.erase φ → tholds σ φ
  | _, .tt, _, _, h => h
  | _, .eq _ _, _, _, h => h
  | _, .defined _, _, _, h => h
  | _, .not φ, hl, σ, h => fun hφ => h ((tholds_iff_holds φ hl σ).1 hφ)
  | _, .and φ ψ, hl, σ, h => by
    have hl' : φ.Leaf = true ∧ ψ.Leaf = true := Bool.and_eq_true_iff.mp hl
    exact ⟨tholds_of_holds φ hl'.1 σ h.1, tholds_of_holds ψ hl'.2 σ h.2⟩
  | _, .imp φ ψ, hl, σ, h => by
    have hl' : φ.FO = true ∧ ψ.Leaf = true := Bool.and_eq_true_iff.mp hl
    exact fun hφ => tholds_of_holds ψ hl'.2 σ (h ((tholds_iff_holds φ hl'.1 σ).1 hφ))
  | _, .upd m U φ, hl, σ, h => by
    have h' := (Modality.afterT_iff.1 h) fun _ => σ.erase_boolOK
    show m.afterC (fun τ => ∀ σ' : TState C _, σ'.erase = τ → tholds σ' φ) (U.apply σ.erase)
    refine Modality.afterC_imp h' fun τ hτ σ' e => ?_
    subst e
    refine tholds_of_holds φ hl σ' ?_
    cases m with
    | box => exact hτ
    | diamond => exact hτ.2
  | _, .modal .., hl, _, _ => nomatch hl
  | _, .havoc φ, hl, σ, h => fun st nt => by
    refine tholds_of_holds φ hl (σ.havoc st nt) ?_
    rw [TState.havoc_erase]
    exact h st.erase nt
  | _, .all _ p φ, hl, σ, h => fun w =>
    tholds_of_holds φ hl (σ.push (t := .val p) w) (h _ (PrimTy.admits_erase w))
  | _, .bind _ t φ, hl, σ, h => fun v => tholds_of_holds φ hl (σ.push v) (h _)
  | _, .anon xs φ, hl, σ, h => fun b => by
    refine tholds_of_holds φ hl (σ.anon xs b) ?_
    rw [TState.anon_erase]
    exact h _

/-- **A leaf closed by its erasure's validity**, over the typed state
(`holds_of_erase_valid`, then `tholds_of_holds`). -/
theorem tholds_of_erase_valid {Γ : Ctx} (φ : Fml C Γ) {ns : List Var} (hlen : ns.length = Γ.length)
    (hnd : ns.Nodup) (hc : φ.Closable ns) (hB : Avoids φ.bindNames ns) (hl : φ.Leaf = true)
    (h : Solidity.Valid (φ.erase ns)) (σ : TState C Γ) : tholds σ φ :=
  tholds_of_holds φ hl σ
    (holds_of_erase_valid φ hc hB (Agree.erase σ.erase hnd hlen) fun τ _ => h τ)

end Solidity.Core
