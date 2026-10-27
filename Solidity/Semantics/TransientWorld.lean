import Solidity.Semantics.ContractWorld

/-!
# Opt-in transient transaction boundary for typed owner/library frames

The existing world methods and Operation.run remain frame operations. This
adapter is selected explicitly: one complete operation tree shares each
owner's logical cells (a delegated library body uses the caller's product),
then normalizes all owners at exit. Failure restores the complete entry world,
with transient cells discarded. Source-world admission remains separate.
-/

namespace Solidity.ContractWorld
variable {K : Type} {contracts : K → Contract}

/-- Normalize each installed owner at its own contract type; code identity,
funds, roles and time remain unchanged. This is never a nested-call operation. -/
def World.resetTransient (w : World contracts) : World contracts :=
  { w with accounts := fun address => (w.accounts address).map fun ⟨k, st⟩ =>
      ⟨k, Storage.resetTransient st⟩ }

/-- Account identity cannot change when its transaction-local region is reset. -/
theorem World.resetTransient_accounts (w : World contracts) (a : Address) :
    w.resetTransient.accounts a =
      (w.accounts a).map (fun ⟨k, st⟩ => ⟨k, Storage.resetTransient st⟩) := rfl

/-- Repeated transaction normalization is pointwise idempotent for every owner. -/
theorem World.resetTransient_accounts_idem (w : World contracts) (a : Address) :
    w.resetTransient.resetTransient.accounts a = w.resetTransient.accounts a := by
  change Option.map _ (Option.map _ (w.accounts a)) = Option.map _ (w.accounts a)
  cases h : w.accounts a with
  | none => rfl
  | some account =>
    obtain ⟨k, st⟩ := account
    change some (⟨k, Storage.resetTransient (Storage.resetTransient st)⟩ : Account contracts) =
      some (⟨k, Storage.resetTransient st⟩ : Account contracts)
    rw [Storage.resetTransient_idem]

/-- Bookkeeping is outside the transient projection. -/
theorem World.resetTransient_funds (w : World contracts) :
    w.resetTransient.funds = w.funds ∧ w.resetTransient.roles = w.roles := ⟨rfl, rfl⟩

variable [DecidableEq K]

/-- Explicit outer entry/exit around the existing typed operation tree.
Exhaustion/divergence remain errors and never produce a successful commit. -/
def Operation.transact (op : Operation contracts) (w : World contracts) :
    World contracts × TRes Unit :=
  match op.run w.resetTransient with
  | .ok next => (next.resetTransient, .ok ())
  | .error e => (w.resetTransient, .error e)

/-- A successful commit requires the actual complete tree to succeed. -/
theorem Operation.transact_ok {op : Operation contracts} {w : World contracts}
    (success : (op.transact w).2 = .ok ()) :
    ∃ next, op.run w.resetTransient = .ok next ∧
      (op.transact w).1 = next.resetTransient := by
  unfold Operation.transact at *
  cases h : op.run w.resetTransient with
  | error e => rw [h] at success; cases success
  | ok next => exact ⟨next, rfl, rfl⟩

/-- Every descendant's persistent and transient writes roll back together;
only normalization of the input transient region survives a failed transaction. -/
theorem Operation.transact_failure {op : Operation contracts} {w : World contracts}
    {e : THalt} (failed : op.run w.resetTransient = .error e) :
    op.transact w = (w.resetTransient, .error e) := by
  unfold Operation.transact
  rw [failed]

end Solidity.ContractWorld
