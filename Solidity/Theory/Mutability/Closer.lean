import Solidity.Theory.Mutability.View
import Solidity.Calculus.Transient
import Solidity.Calculus.Logic

/-!
# Frame facts for proofs (S3.3)

`docs/feature-work/semantics-extensions.md`, S3.3: a proof about a read-only
body gets its frame for free.  Each lemma below takes a modal fact a proof
already has (the calculus's `holds` of a box or diamond, a `Spec.sat` box,
the transient layer's `Holds`) and adds, at every successful end state,
that the globals (storage with its transient roots, ledger, balance) and,
on the transient layer, the transient cells are the entry's.  No program
analysis is repeated: the premise is the decidable `Prog.within`, and the
fact is `Prog.committed_readOnly` / `Transient.Program.readOnly_preserves`
(S3.1).

They replace the per-example frame checks of
`Examples/Tactics/TransientStorage.lean` (a write refused in a `view`
context, a `pure` read refused, a read-only call of a `nonpayable` callee
refused, and the static/read-only frame itself).
-/

namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

/-- **A read-only body's modal fact, with its frame.**  If `[P]φ` (or
`⟨P⟩φ`) holds in `σ` and `P` is within `view` or `pure`, every successful run
ends where `φ` holds and the globals are `σ`'s. -/
theorem holds_modal_readOnly {μ : Mutability} {m : Modality} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) {σ : State C Γ} {φ : Fml C Γ'}
    (hφ : holds σ (.modal m P .nil φ)) {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) :
    holds o.st φ ∧ globals o.st = globals σ := by
  refine ⟨?_, frame_globals (Prog.run_frame P hw 0 h).1 hμ⟩
  have hr : Prog.runFrames σ P .nil = .ok o.st := by
    unfold Prog.runFrames
    rw [h]
    rfl
  have := hφ.1
  rw [hr] at this
  exact this

/-- The same for an ordinary `Spec` box (`Calculus/Correct.lean`). -/
theorem Spec.box_readOnly {μ : Mutability} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) {σ : State C Γ} {φ : Spec C Γ'}
    (hφ : Spec.sat σ (.box P φ)) {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) :
    Spec.sat o.st φ ∧ globals o.st = globals σ := by
  refine ⟨?_, frame_globals (Prog.run_frame P hw 0 h).1 hμ⟩
  simp only [Spec.sat, h] at hφ
  exact hφ

namespace Transient

open Solidity.Transient

/-- **The transient layer's modal fact, with its frame.**  In a read-only
context, a proved `Holds m body post` strengthens to one whose postcondition
also says both stores are the entry's. -/
theorem holds_readOnly {L : Layout} {α : Type} {m : Modality} {body : Program C L α}
    {post : α → FrameState C L → Prop} {ctx : Context} {s : FrameState C L}
    (hμ : ctx.mutability ≠ .nonpayable) (proved : Holds m body post ctx s) :
    Holds m body (fun v t => post v t ∧ t.cells = s.cells ∧ globals t.base = globals s.base)
      ctx s := by
  unfold Holds at proved ⊢
  cases ran : Program.run body ctx s with
  | error e =>
    rw [ran] at proved
    exact proved
  | ok result =>
    obtain ⟨v, t⟩ := result
    rw [ran] at proved
    exact ⟨⟨proved.1, Program.readOnly_preserves body hμ ran⟩, proved.2⟩

/-- The frame alone, for any read-only body that does not panic: `Holds .box`
with `post := True` is the halt policy only. -/
theorem holds_frame {L : Layout} {α : Type} {body : Program C L α} {ctx : Context}
    {s : FrameState C L} (hμ : ctx.mutability ≠ .nonpayable)
    (noPanic : Program.run body ctx s ≠ .error .panic) :
    Holds .box body (fun _ t => t.cells = s.cells ∧ globals t.base = globals s.base) ctx s := by
  have h : Holds .box body (fun _ _ => True) ctx s := by
    unfold Holds
    cases ran : Program.run body ctx s with
    | error e => exact ⟨trivial, by rw [← ran]; exact noPanic⟩
    | ok _ => exact ⟨trivial, by intro p; cases p⟩
  have h' := holds_readOnly hμ h
  unfold Holds at h' ⊢
  cases ran : Program.run body ctx s with
  | error e => rw [ran] at h'; exact h'
  | ok result => rw [ran] at h'; exact ⟨h'.1.2, h'.2⟩

end Transient

end Solidity.Theory.Mutability
