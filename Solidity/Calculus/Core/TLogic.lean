import Solidity.Calculus.Core.Logic
import Solidity.Semantics.Core.TypedRunFrame

/-!
# What a scoped formula means over the typed state

`Calculus/Core/Logic.lean`'s `holds`, read over the typed state (`TState`,
`Semantics/Core/TypedState.lean`) and the typed run (`Prog.trun`,
`Frames.trun`), beside it until the calculus is moved over (`docs/intrinsic.md`,
W2 lane `sound`):

* a term means what it means on the state's erasure (`TState.erase`): its
  symbols are `Update.lean`'s, untyped until the closer is ported (M6c);
* an update is applied to the erasure, and what follows it is read in every
  typed state that erases to the state it ends in.  The rules' updates end in
  the erasure of the state the statement's typed run ends in, so that state
  is one of them; an update that ends in no typed state (a value of another
  type) says nothing;
* a modality runs the program and its frames with the typed run: a `bool`
  local holds a `bool`, so a branch is never stuck and the diamond needs no
  guard (M3's `State.BoolOK`);
* the binders range over typed values: `∀ x` over the values of its type, a
  hidden binder over what a local of its type may hold in the state's heap,
  `{anon(xs)}` over typed values of the locals, `{havoc}` over typed
  storages.

A hidden binder at a memory type ranges over the references the heap
typing gives that type, which may be none (`docs/intrinsic.md`, W2 lane
`sound`, "the hidden binder"): under the diamond it asks for one
(`Modality.forallB`, decision 12), so a premise over an empty type is not
vacuously true there; under the box it is universal.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- `p` after a typed run under `m` (`Modality.afterRunC`): `p` of the state
it ends in, `m.onTHalt` on a halt (both modalities accept `exhausted`,
decision 15), and no panic. -/
def _root_.Solidity.Modality.afterRunTR {α : Type} (m : Modality) (p : α → Prop) (r : TRes α) :
    Prop :=
  (match r with
    | .ok a => p a
    | .error e => m.onTHalt e) ∧ r ≠ .error .panic

/-- The state a modality's program, then its frames, end in. -/
def Prog.trunFrames {Γ Γ₁ Γ₀ : Ctx} (σ : TState C Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    TRes (TState C Γ₀) := do
  let o ← Prog.trun σ P
  let o' ← Frames.trun o.st κ
  pure o'.st

/-- **Whether `φ` holds in the typed state `σ`.** -/
def tholds : {Γ : Ctx} → TState C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase)
  | _, σ, .defined t => ∃ x, t.eval σ.erase = .ok x
  | _, σ, .not φ => ¬ tholds σ φ
  | _, σ, .and φ ψ => tholds σ φ ∧ tholds σ ψ
  | _, σ, .imp φ ψ => tholds σ φ → tholds σ ψ
  | _, σ, .upd m U φ =>
    m.afterC (fun τ => ∀ σ' : TState C _, σ'.erase = τ → tholds σ' φ) (U.apply σ.erase)
  | _, σ, .modal m P κ φ => m.afterRunTR (tholds · φ) (Prog.trunFrames σ P κ)
  | _, σ, .havoc φ => ∀ st nt, tholds (σ.havoc st nt) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, tholds (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => tholds (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, tholds (σ.anon xs b) φ

/-- A type `LTy.inhabited` names has a value in every typed state. -/
theorem LTy.tdenote_nonempty {H : HTy} : (t : LTy) → t.inhabited = true →
    Nonempty (t.TDenote C H)
  | .val p, _ => ⟨PrimTy.dflt p⟩
  | .alias _, _ => ⟨none⟩
  | .mem _, h => nomatch h
  | .old, _ => ⟨Storage.init C⟩
  | .oldNet, _ => ⟨[]⟩

/-- Valid over the typed states: true in every typed state of the empty
context. -/
def TValid (φ : Fml C []) : Prop := ∀ σ : TState C [], tholds σ φ

end Solidity.Core
