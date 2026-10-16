import Solidity.Semantics.Ends
import Solidity.Semantics.NoPanic

/-!
# Pure argument evaluation preserves failure priority

Values and reference paths either return or revert. In particular, no
argument expression can panic, diverge or exhaust resources. This lets
the calculus capture a pure primitive argument before an earlier reference
read without changing the failure, including an unset reference.
Allocations and source effects remain in the ordered caller prefix.
-/

namespace Solidity
variable {C : Contract}

def TRes.RevertOnly {α : Type} (t : TRes α) : Prop := t.Ends ∧ t.NoPanic

theorem TRes.RevertOnly.ok {α : Type} (a : α) : TRes.RevertOnly (Except.ok a : TRes α) :=
  ⟨TRes.Ends.ok _, TRes.NoPanic.ok _⟩

theorem TRes.RevertOnly.bind {α β : Type} {t : TRes α} {k : α → TRes β}
    (h : t.RevertOnly) (hk : ∀ a, (k a).RevertOnly) : (t >>= k).RevertOnly :=
  ⟨h.1.bind (fun a => (hk a).1), h.2.bind (fun a => (hk a).2)⟩

theorem TRes.RevertOnly.error {α : Type} {t : TRes α} (h : t.RevertOnly)
    {e : THalt} (he : t = .error e) : e = .revert := by
  cases he
  cases e with
  | revert => rfl
  | panic => exact False.elim (h.2 rfl)
  | diverge => exact False.elim (h.1.1 rfl)
  | exhausted => exact False.elim (h.1.2 rfl)

/-- Pure arguments commute even when an earlier reference is invalid. -/
theorem TRes.RevertOnly.bind_comm {α β γ : Type} {t : TRes α} {u : TRes β}
    (ht : t.RevertOnly) (hu : u.RevertOnly) (k : α → β → TRes γ) :
    (t >>= fun a => u >>= fun b => k a b) = (u >>= fun b => t >>= fun a => k a b) := by
  cases t with
  | ok a => cases u <;> rfl
  | error e =>
    have he : e = .revert := ht.error rfl
    cases he
    cases u with
    | ok b => rfl
    | error f =>
      have hf : f = .revert := hu.error rfl
      cases hf
      rfl

theorem Val.evalT_revertOnly {Γ : Ctx} (σ : State C Γ) {p : PrimTy} (e : Val C Γ p) :
    (e.evalT σ).RevertOnly := ⟨e.evalT_ends σ, e.evalT_noPanic σ⟩

theorem SPath.resolveT_revertOnly {Γ : Ctx} (σ : State C Γ) {T : Ty} (e : SPath C Γ T) :
    (e.resolveT σ).RevertOnly := ⟨e.resolveT_ends σ, e.resolveT_noPanic σ⟩

theorem MPath.mvalT_revertOnly {Γ : Ctx} (σ : State C Γ) {T : Ty} (e : MPath C Γ T) :
    (e.mvalT σ).RevertOnly := ⟨e.mvalT_ends σ, e.mvalT_noPanic σ⟩

theorem Args.evalT_revertOnly {Γ : Ctx} (σ : State C Γ) :
    {ps : Ctx} → (args : Args C Γ ps) → (args.evalT σ).RevertOnly
  | _, .nil => TRes.RevertOnly.ok _
  | _, .snoc as _ _ e => (as.evalT_revertOnly σ).bind fun _ =>
      (e.evalT_revertOnly σ).bind fun _ => TRes.RevertOnly.ok _
  | _, .snocStorage as _ _ e => (as.evalT_revertOnly σ).bind fun _ =>
      (e.resolveT_revertOnly σ).bind fun _ => TRes.RevertOnly.ok _
  | _, .snocMemory as _ _ e => (as.evalT_revertOnly σ).bind fun _ =>
      (e.mvalT_revertOnly σ).bind fun _ => TRes.RevertOnly.ok _

end Solidity
