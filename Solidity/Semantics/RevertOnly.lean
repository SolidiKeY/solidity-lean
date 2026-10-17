import Solidity.Semantics.Ends

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

end Solidity
