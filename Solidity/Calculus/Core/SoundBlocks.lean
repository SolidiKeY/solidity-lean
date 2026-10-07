import Solidity.Calculus.Core.SoundKit
import Solidity.Theory.Bridge.Denote

/-!
# The rules of the statements that hold blocks are sound

Soundness of `Calculus/Core/Blocks.lean`'s arms against M3's interpreter
(`Core.Stmt.run`), in the shape of `Calculus/Core/Logic.lean`'s
`Stmt.step_sound_*`: the premise put in front of the rest `ω`, the frames
`κ` and the postcondition `φ` gives `⟨ s; ω κ ⟩ φ` (`docs/intrinsic.md`,
M6a).

* **Loops.**  `whileUnwind` is one turn of `Loop.run` (`Loop.run_unfold`),
  `loopExit` its exit; `whileClose`, `whileNoVariantDiamond` and the
  diamond's `try` close to `false`, which gives anything.
* **`try`** under the box: each clause's goal, for every value its outcome
  binds (`Binders.all`), is the run of that clause; the values the
  transaction's data decodes to are of their types (`Binders.decode_fits`).
-/

namespace Solidity.Core

open Semantics (Value Res Halt lookupBy bind_ok_inv)
open Solidity (Modality Srt NoPanic)
open Theory Theory.StValue

variable {C : Contract}

/-! ## States -/

section States

variable {Γ : Ctx}

theorem State.withEnv_self (σ : State C Γ) : σ.withEnv σ.env = σ := by cases σ; rfl

theorem State.drop_refl (σ : State C Γ) : σ.drop .refl = σ := State.withEnv_self σ

theorem map_drop_refl (r : Res (State C Γ)) : r.map (State.drop .refl) = r := by
  cases r <;> simp only [Except.map, State.drop_refl]

theorem bind_run_nil (r : Res (State C Γ)) : r.bind (Prog.run · .nil) = r := by
  cases r <;> rfl

end States

/-! ## Lowering keeps meaning

A lowered value reads what the interpreter evaluates, and a term that
returns denotes its value (`Theory/Bridge/Denote.lean`'s bridge, on scoped
terms). -/

section Lowering

variable {Γ : Ctx}

/-- **The term bridge** on scoped terms: a term's denotation agrees with its
reading wherever the reading returns. -/
theorem Tm.denote_eval (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) →
    Srt.Bridge s (t.denote σ) (t.eval σ)
  | _, .pvV _ => by intro x h; cases h; rfl
  | _, .pvP i => by
    intro r segs h
    have h' : aliasPath σ i = .ok (r, segs) := h
    simp only [Tm.denote, h']
  | _, .pvS _ => by intro τ h; cases h; exact StValue.Equiv.refl _
  | _, .pvI _ => trivial
  | _, .netOf i a => by
    intro x h
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    obtain ⟨n, hn, h⟩ := bind_ok_inv h
    cases h
    cases va with
    | bool => cases hn
    | int n' =>
      cases hn
      simp only [Tm.denote, Tm.denote_eval σ a _ ha]
  | _, .app0 o => Op0.denote_eval o
  | _, .app1 o _ a => Op1.denote_eval o (Tm.denote_eval σ a)
  | _, .app2 o a b => Op2.denote_eval o (Tm.denote_eval σ a) (Tm.denote_eval σ b)
  | _, .app3 o a b c =>
    Op3.denote_eval o (Tm.denote_eval σ a) (Tm.denote_eval σ b) (Tm.denote_eval σ c)

/-- `t ≐ b` holds where `t` returns `b`. -/
theorem holds_isBoolD (t : Tm C Γ .val) (σ : State C Γ) (b : Bool) :
    holds σ (Fml.isBoolD t b) ↔ t.eval σ = .ok (.bool b) := by
  constructor
  · rintro ⟨⟨x, hx⟩, _, he⟩
    have he' : Theory.StValue.Equiv (.prim x) (.prim (.bool b)) := by
      rw [← Tm.denote_eval σ t x hx]; exact he
    rw [Theory.StValue.Equiv.prim_iff] at he'
    cases he'
    exact hx
  · intro h
    refine ⟨⟨_, h⟩, ⟨_, rfl⟩, ?_⟩
    show Theory.StValue.Equiv (t.denote σ) (.prim (.bool b))
    rw [Tm.denote_eval σ t _ h]
    exact Theory.StValue.Equiv.refl _

/-- `c ≐ b` of a lowered condition holds where it evaluates to `b`. -/
theorem holds_isBoolD_lower (c : Val C Γ .bool) (σ : State C Γ) (b : Bool) :
    holds σ (Fml.isBoolD c.lower b) ↔ c.eval σ = .ok (.bool b) := by
  rw [holds_isBoolD, Val.eval_lower]

end Lowering

/-! ## Loops -/

namespace Loop

variable {α : Type} {body : α → Res α} {c : α → Res Value}

/-- **One turn of a loop**: the loop is its first step, then the loop again
from where the body left it. -/
theorem run_unfold (σ : α) :
    run body c σ = match step body c σ with
      | .inl τ => run body c τ
      | .inr r => r := by
  cases hs : step body c σ with
  | inr r =>
    show run body c σ = r
    exact run_of_iterN (n := 1) (by simp only [iterN, hs])
  | inl τ =>
    show run body c σ = run body c τ
    have hshift : ∀ n, iterN body c (n + 1) σ = iterN body c n τ := fun n => by
      simp only [iterN, hs]
    by_cases hex : ∃ r n, iterN body c n τ = .inr r
    · obtain ⟨r, n, h⟩ := hex
      rw [run_of_iterN h, run_of_iterN ((hshift n).trans h)]
    · have hex' : ¬ ∃ r n, iterN body c n σ = .inr r := by
        rintro ⟨r, n, h⟩
        cases n with
        | zero => simp only [iterN, reduceCtorEq] at h
        | succ n => exact hex ⟨r, n, (hshift n).symm.trans h⟩
      simp only [run, hex, hex', dite_false]

end Loop

section Loops

variable {Γ Γ₁ : Ctx} {m : Modality}

/-- `whileUnwind`: `⟨[ while (nse) body ]⟩ ⇝ ⟨[ if (nse) { { body } while (nse) body } ]⟩`. -/
theorem Premise.Sound.whileUnwind (n : Nat) (c : Val C Γ .bool) (body : Prog C Γ Γ₁)
    (σ : State C Γ) :
    Premise.Sound m (.loop (.unwind (n + 1)) c body)
      (.unfold (.cons (.ite c (.cons (.block body) (.cons (.loop (.unwind n) c body) .nil)) .nil)
        .nil) .refl) σ := by
  refine Premise.Sound.unfold ?_
  rw [map_drop_refl, Prog.run_cons, bind_run_nil, Stmt.run_ite, Stmt.run_loop, Loop.run_unfold]
  simp only [Run.ite, Loop.step]
  cases c.eval σ with
  | error e => rfl
  | ok v =>
    cases v with
    | int => rfl
    | bool b =>
      cases b with
      | false => exact map_drop_refl (.ok σ)
      | true =>
        show (Prog.run σ (.cons (.block body) (.cons (.loop (.unwind n) c body) .nil))).map
          (State.drop .refl) = _
        rw [map_drop_refl, Prog.run_cons, Stmt.run_block]
        cases (Prog.run σ body).map (State.drop body.ext) with
        | error e => rfl
        | ok τ =>
          show Prog.run τ (.cons (.loop (.unwind n) c body) .nil) = _
          rw [Prog.run_cons, bind_run_nil, Stmt.run_loop]

/-- `loopExit`: `⟨[ while (nse) body ]⟩ ⇝ nse = FALSE ⟹ ⟨[ ]⟩ ; nse = FALSE`. -/
theorem Premise.Sound.loopExit (c : Val C Γ .bool) (body : Prog C Γ Γ₁) (σ : State C Γ) :
    Premise.Sound m (.loop (.unwind 0) c body) (.check (Fml.isBoolD c.lower false)) σ :=
  fun ω κ φ => Premise.sound_check σ (fun h => by
    rw [Stmt.run_loop, Loop.run_unfold]
    simp only [Loop.step, (holds_isBoolD_lower c σ false).1 h]) ω κ φ

/-- A rule that closes its goal to `false` is sound: `false` gives nothing
to prove from (`whileClose`, `whileNoVariantDiamond`, `tryCallDiamond`). -/
theorem Premise.Sound.fail {Γ' : Ctx} (s : Stmt C Γ Γ') (σ : State C Γ) :
    Premise.Sound m s (.done false) σ :=
  fun ω κ φ => Premise.sound_done σ false (fun h => absurd h (by decide)) ω κ φ

end Loops

/-! ## `try` -/

section Try

variable {Γ : Ctx}

/-- The locals a binder list binds hold values of their types. -/
def Binders.Fits : {ρ : Ctx} → Binders ρ → Env C ρ → Prop
  | _, .nil, _ => True
  | _, .snoc bs p _, r => p.admits (r.1 : Value) ∧ Binders.Fits bs r.2

/-- The data an external call returns decodes to values of the binders'
types. -/
theorem Binders.decode_fits {ρ : Ctx} (bs : Binders ρ) :
    ∀ {vs : List Value} {r : Env C ρ} {rest : List Value},
      bs.decode vs = .ok (r, rest) → bs.Fits r := by
  induction bs with
  | nil => intros; trivial
  | snoc bs p x ih =>
    intro vs r rest h
    obtain ⟨⟨e, rest'⟩, he, h⟩ := bind_ok_inv h
    cases rest' with
    | nil => cases h
    | cons v rest' =>
      simp only at h
      split at h
      · cases h
        exact ⟨(PrimTy.admits_iff_fits p v).2 ‹_›, ih he⟩
      · cases h

/-- Decoding reverts, never panics. -/
theorem Binders.decode_noPanic {ρ : Ctx} (bs : Binders ρ) (vs : List Value) :
    NoPanic (bs.decode (C := C) vs) := by
  induction bs generalizing vs with
  | nil => exact NoPanic.pure _
  | snoc bs p x ih =>
    refine NoPanic.bind (ih vs) fun ⟨e, rest⟩ _ => ?_
    simp only
    split
    · split <;> no_panic
    · no_panic

theorem CodeBinder.decode_fits {κ : Ctx} (code : CodeBinder κ) {c : Value} {r : Env C κ}
    (h : code.decode c = .ok r) : code.binders.Fits r := by
  cases code with
  | none => trivial
  | some x =>
    simp only [CodeBinder.decode] at h
    split at h
    · cases h; exact ⟨(PrimTy.admits_iff_fits .uint c).2 ‹_›, trivial⟩
    · cases h

theorem CodeBinder.decode_noPanic {κ : Ctx} (code : CodeBinder κ) (c : Value) :
    NoPanic (code.decode (C := C) c) := by
  cases code with
  | none => exact NoPanic.pure _
  | some x => simp only [CodeBinder.decode]; no_panic

/-- An external call's key never panics: its parts are simple. -/
theorem ExtCall.key_noPanic' (σ : State C Γ) (c : ExtCall C Γ) : NoPanic (c.key σ) := by
  have hs : ∀ {p : PrimTy} (s : Simple C Γ p), NoPanic (s.eval σ) := by
    intro p s; cases s <;> exact NoPanic.pure _
  have hm : NoPanic (c.args.mapM fun a => a.2.eval σ) := NoPanic.mapM (fun _ => hs _) _
  have ha : NoPanic (c.addr.eval σ) := hs _
  unfold ExtCall.key; no_panic

/-- `∀ xs. ψ` holds at every value of the binders' types. -/
theorem holds_binders_all {ρ : Ctx} (bs : Binders ρ) :
    ∀ (σ : State C Γ) (ψ : Fml C (ρ ++ Γ)) (r : Env C ρ), bs.Fits r → holds σ (bs.all ψ) →
      holds (σ.withEnv (Env.append ρ r σ.env)) ψ := by
  induction bs with
  | nil => intro σ ψ _ _ h; rw [show Env.append [] _ σ.env = σ.env from rfl, State.withEnv_self]; exact h
  | snoc bs p x ih =>
    intro σ ψ r hr h
    exact ih σ (.all x p ψ) r.2 hr.2 h r.1 hr.1

variable {m : Modality}

/-- A block's goal, its locals popped by `h`: the block's run, then the rest. -/
theorem holds_modalK_pop {Γ₂ Γ₀ Δ Γ₁ : Ctx} (τ : State C Δ) (P : Prog C Δ Γ₁) (h : Ext Γ Γ₁)
    (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) :
    holds τ (Fml.modalK m P (.pop .block h (.seq ω κ)) φ) →
      m.afterRunC (holds · φ)
        (do let υ ← (Prog.run τ P).map (State.drop h); Frames.run (← Prog.run υ ω) κ) := by
  rw [holds_modalK]
  cases Prog.run τ P <;> exact id

/-- `tryCallNoCallbackBox`: under the box, a goal per clause, each for every
value its outcome binds. -/
theorem Premise.Sound.tryCallBox {ρ κc Γ₁ Γe Γ₃ Γ₄ : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe) (code : CodeBinder κc)
    (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (σ : State C Γ) :
    Premise.Sound .box (.tryCall call rets ok err code pnc other)
      (.branches [⟨rets, ok⟩, ⟨Binders.nil, err⟩, ⟨code.binders, pnc⟩, ⟨Binders.nil, other⟩]) σ := by
  intro _ _ ω κ φ
  rintro ⟨h1, h2, h3, h4⟩
  show Modality.afterRunC .box _ _
  rw [run_cons_frames]
  have herr : ∀ {α : Type} {e : Halt} (r : Res α), NoPanic r → r = .error e →
      Modality.afterRunC .box (holds · φ)
        (do let τ ← (Except.error e : Res (State C Γ)); Frames.run (← Prog.run τ ω) κ) :=
    fun r hr he => ⟨trivial, fun h => hr (he.trans (by cases h; rfl))⟩
  show Modality.afterRunC .box _ (Except.bind (Run.tryCall call rets ok.ext ok.runR err.ext err.runR
    code pnc.ext pnc.runR other.ext other.runR σ) _)
  unfold Run.tryCall
  cases hk : call.key σ with
  | error e => exact herr _ (ExtCall.key_noPanic' σ call) hk
  | ok k =>
    show Modality.afterRunC .box _ (Except.bind (match lookupBy k σ.tx.ext with
      | none => _ | some (.ok vs) => _ | some .error => _ | some (.panic c) => _
      | some .other => _) _)
    cases lookupBy k σ.tx.ext with
    | none => exact ⟨trivial, fun h => by cases h⟩
    | some res =>
      cases res with
      | ok vs =>
        show Modality.afterRunC .box _ (Except.bind (Except.bind (rets.decode vs) _) _)
        cases hd : rets.decode vs with
        | error e => exact herr _ (Binders.decode_noPanic rets vs) hd
        | ok p =>
          obtain ⟨r, rest⟩ := p
          exact holds_modalK_pop _ ok _ ω κ φ
            (holds_binders_all rets σ _ r (Binders.decode_fits rets hd) h1)
      | error =>
        have h2' := holds_modalK_pop σ err ((Ext.append Γ []).trans err.ext) ω κ φ h2
        rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at h2'
        exact h2'
      | panic c =>
        show Modality.afterRunC .box _ (Except.bind (Except.bind (code.decode c) _) _)
        cases hd : code.decode c with
        | error e => exact herr _ (CodeBinder.decode_noPanic code c) hd
        | ok r =>
          exact holds_modalK_pop _ pnc _ ω κ φ
            (holds_binders_all code.binders σ _ r (CodeBinder.decode_fits code hd) h3)
      | other =>
        have h4' := holds_modalK_pop σ other ((Ext.append Γ []).trans other.ext) ω κ φ h4
        rw [show (Ext.append Γ []).trans other.ext = other.ext from Subsingleton.elim _ _] at h4'
        exact h4'

/-- **The rule of a `try` is sound**: a goal per clause under the box, `false`
under the diamond. -/
theorem Stmt.stepSound_tryCall (k : Nat) (m : Modality) {ρ κc Γ₁ Γe Γ₃ Γ₄ : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γe)
    (code : CodeBinder κc) (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄) :
    Stmt.StepSound k m (.tryCall call rets ok err code pnc other) := by
  cases m with
  | box => exact Stmt.StepSound.of_eq rfl fun σ _ => Premise.Sound.tryCallBox call rets ok err code pnc other σ
  | diamond => exact Stmt.StepSound.of_eq rfl fun σ _ => Premise.Sound.fail _ σ

end Try

end Solidity.Core
