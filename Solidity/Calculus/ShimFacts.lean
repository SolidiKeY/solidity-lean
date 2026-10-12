import Solidity.Calculus.NoPanic
import Solidity.Theory.Bridge.Denote

/-!
# Facts about the reader's shim

The SolKey reader's interface (`Surface.Tm`, `Surface.UpdElem`,
`Surface.Upd`, `Update.lean`) is frozen, and nothing in the prover reads it
(`docs/intrinsic.md`, W9.6N).  What was proved of it is kept here, apart, for
an external reader: that a term and an update never panic
(`Calculus/NoPanic.lean` proves it of the scoped ones), and the term bridge
(`Theory/Bridge/Denote.lean`'s symbol bridge, read over a term).
-/

namespace Solidity

open Semantics Theory Theory.StValue

variable {C : Contract}

/-- **A term never panics.** -/
theorem Surface.Tm.eval_noPanic (σ : State) {s : Srt} : (t : Surface.Tm C s) → s.NoPanic (t.eval σ)
  | .pvV x => by simp only [Surface.Tm.eval, Srt.NoPanic]; no_panic
  | .pvP x => by simp only [Surface.Tm.eval, Srt.NoPanic]; no_panic
  | .pvS x => by simp only [Surface.Tm.eval, Srt.NoPanic]; no_panic
  | .pvI x => by simp only [Surface.Tm.eval, Srt.NoPanic]; no_panic
  | .app0 o => Op0.eval_noPanic σ o
  | .app1 o a => Op1.eval_noPanic σ o (Surface.Tm.eval_noPanic σ a)
  | .app2 o a b => Op2.eval_noPanic σ o (Surface.Tm.eval_noPanic σ a) (Surface.Tm.eval_noPanic σ b)
  | .app3 o a b c =>
    Op3.eval_noPanic σ o (Surface.Tm.eval_noPanic σ a) (Surface.Tm.eval_noPanic σ b) (Surface.Tm.eval_noPanic σ c)

theorem Surface.UpdElem.write_noPanic (σ₀ : State) (e : Surface.UpdElem C) (τ : State) :
    NoPanic (e.write σ₀ τ) := by
  have hv : ∀ t : Term C, NoPanic (t.eval σ₀) := fun t => Surface.Tm.eval_noPanic σ₀ t
  have hp : ∀ t : PTerm C, NoPanic (t.eval σ₀) := fun t => Surface.Tm.eval_noPanic σ₀ t
  have hi : ∀ t : ITerm C, NoPanic (t.eval σ₀) := fun t => Surface.Tm.eval_noPanic σ₀ t
  have hs : ∀ t : STerm C, NoPanic (t.eval σ₀) := fun t => Surface.Tm.eval_noPanic σ₀ t
  have hm : ∀ t : MTerm C, NoPanic (t.eval σ₀) := fun t => Surface.Tm.eval_noPanic σ₀ t
  cases e <;> simp only [Surface.UpdElem.write] <;> no_panic

/-- **An update never panics**: what it reads are terms. -/
theorem Surface.Upd.apply_ne_panic (U : Surface.Upd C) (σ : State) : U.apply σ ≠ .error .panic := by
  unfold Surface.Upd.apply
  suffices h : ∀ (V : Surface.Upd C) (τ : State),
      NoPanic (V.foldlM (fun τ e => e.write σ τ) τ) from h U σ
  intro V
  induction V with
  | nil => intro τ; simp only [List.foldlM_nil, ne_eq, NoPanic.pure, not_false_eq_true]
  | cons e V ih =>
    intro τ
    simp only [List.foldlM_cons]
    exact NoPanic.bind (Surface.UpdElem.write_noPanic σ e τ) fun τ' _ => ih τ'

/-- **The term bridge**: a term's denotation agrees with its reading
wherever the reading returns (`Srt.Bridge`). -/
theorem Surface.Tm.denote_eval {s : Srt} {σ : State} : (t : Surface.Tm C s) → Srt.Bridge s (t.denote σ) (t.eval σ)
  | .pvV y => by
    intro x h
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    cases b <;> cases h
    simp only [Surface.Tm.denote, hb]
  | .pvP y => by
    intro r segs h
    have h' : aliasPath σ y = .ok (r, segs) := h
    simp only [Surface.Tm.denote, h']
  | .pvS y => by
    intro τ h
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    cases b with
    | store st =>
      cases h
      simp only [Surface.Tm.denote, hb]
      exact StValue.Equiv.refl _
    | _ => cases h
  | .pvI _ => trivial
  | .app0 o => o.denote_eval
  | .app1 o a => o.denote_eval a.denote_eval
  | .app2 o a b => o.denote_eval a.denote_eval b.denote_eval
  | .app3 o a b c => o.denote_eval a.denote_eval b.denote_eval c.denote_eval

/-- A stored value that returns denotes it, up to `Equiv`. -/
theorem SValT.denote_eval {σ : State} {v : SValT C} {w : SVal} (h : v.eval σ = .ok w) :
    StValue.Equiv (v.denote σ) w.abs := Surface.Tm.denote_eval v w h

end Solidity
