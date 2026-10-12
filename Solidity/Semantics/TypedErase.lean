import Solidity.Semantics.StepErase

/-!
# The value-level erasure the soundness reads

What the rules' soundness (`Calculus/Sound*.lean`) needs of the erasure
below the terms: a typed result against an untyped one (`TRes.Agrees`), and
the storage, heap and state operations each against its untyped namesake
(`Semantics/StorageErase.lean`, `Semantics/HeapErase.lean`,
`Semantics/State.lean`, and the value-level lemmas of
`Semantics/StepErase.lean`: `SRef.erase_field`, `MAddr.erase`,
`writeAddr_erase`, `opStoreT_erase`, …).  None of it reads a program
evaluator of `Semantics/Erased.lean`: the typed run is read against the
rules' terms directly (`Calculus/LowerRun.lean`).

This module is the seam: the soundness imports it, not `StepErase`, whose
value-level lemmas move below it when the erased evaluators go (W9.6.4).
-/

namespace Solidity

open Semantics (Value Res)

variable {C : Contract}

namespace TRes.Agrees

variable {α β γ : Type} {f : α → β}

/-- An agreement ending in a value: the untyped side ends there too. -/
theorem eq_ok {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {a : α} (ht : t = .ok a) :
    u = .ok (f a) := by
  subst ht; exact h

/-- An agreement with a typed halt that is not a divergence nor an
exhaustion: the untyped side halts too. -/
theorem eq_error {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {e : THalt}
    (ht : t = .error e) (hd : e ≠ .diverge) (hx : e ≠ .exhausted) : ∃ e', u = .error e' := by
  subst ht
  cases e with
  | revert => exact ⟨_, h⟩
  | panic => exact ⟨_, h⟩
  | diverge => exact absurd rfl hd
  | exhausted => exact absurd rfl hx

/-- An agreement read through an equation of the untyped side. -/
theorem of_eq_right {t : TRes α} {u u' : Res β} (h : TRes.Agrees f t u) (e : u = u') :
    TRes.Agrees f t u' := e ▸ h

/-- A pair's agreement read at its first component. -/
theorem bind_fst {α₁ α₂ β₁ β₂ : Type} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {t : TRes (α₁ × α₂)}
    {u : Res (β₁ × β₂)} (h : TRes.Agrees (fun x => (f₁ x.1, f₂ x.2)) t u) :
    TRes.Agrees f₁ (t >>= fun x => Pure.pure x.1) (u >>= fun y => Pure.pure y.1) :=
  TRes.Agrees.bind h fun _ => rfl

end TRes.Agrees

end Solidity
