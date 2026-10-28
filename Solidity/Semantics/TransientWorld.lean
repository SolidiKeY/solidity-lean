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

/-- A typed outer transaction boundary for a composition of source frames.
Invoke once around the whole composition, never between sibling/nested frames.
The supplied frame retains its actual result and exact halt; this adapter does
not certify source admission or constructor reachability. -/
def World.transact {α : Type} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) :
    World contracts × TRes α :=
  match frame w.resetTransient with
  | .ok (next, result) => (next.resetTransient, .ok result)
  | .error e => (w.resetTransient, .error e)

/-- Successful composition commits exactly its returned world and result,
with only the transaction-local region discarded. -/
theorem World.transact_commit {α : Type} (w next : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (result : α)
    (success : frame w.resetTransient = .ok (next, result)) :
    w.transact frame = (next.resetTransient, .ok result) := by
  unfold World.transact
  rw [success]

/-- An uncaught failure rolls back every completed descendant, including code
installation and payments. Divergence/exhaustion retain their exact halt. -/
theorem World.transact_failure {α : Type} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (e : THalt)
    (failed : frame w.resetTransient = .error e) :
    w.transact frame = (w.resetTransient, .error e) := by
  unfold World.transact
  rw [failed]

/-- Success of the boundary witnesses an actual complete frame success;
normalization cannot turn a failed run into a successful transaction. -/
theorem World.transact_ok {α : Type} {w : World contracts}
    {frame : World contracts → TRes (World contracts × α)} {result : α}
    (success : (w.transact frame).2 = .ok result) :
    ∃ next, frame w.resetTransient = .ok (next, result) ∧
      (w.transact frame).1 = next.resetTransient := by
  unfold World.transact at *
  cases h : frame w.resetTransient with
  | error e => rw [h] at success; cases success
  | ok pair =>
    obtain ⟨next, value⟩ := pair
    rw [h] at success
    have same : value = result := Except.ok.inj success
    subst value
    exact ⟨next, rfl, rfl⟩

variable [DecidableEq K]

/-- Reset checks the same installed code identity and normalizes only that
owner's storage at the catalog's contract type. -/
theorem World.resetTransient_storage? (w : World contracts) {k : K} (r : Handle k) :
    w.resetTransient.storage? r = (w.storage? r).map Storage.resetTransient := by
  unfold World.storage? World.resetTransient
  cases h : w.accounts r.address with
  | none => simp only [h, Option.map_none, bind, Option.bind_none]
  | some account =>
    obtain ⟨j, st⟩ := account
    by_cases same : j = k
    · subst j
      simp only [h, Option.map_some, bind, Option.bind_some, dite_true]
    · simp only [h, Option.map_some, bind, Option.bind_some, same, dite_false, Option.map_none]

/-- Every persistent path of each installed owner, including aggregate paths,
retains its exact observation at the transaction boundary. -/
theorem World.resetTransient_persistent (w : World contracts) {k : K} (r : Handle k)
    (path : SRef (contracts k) U) (persistent : path.root ∉ (contracts k).transientRoots) :
    (w.resetTransient.storage? r).bind (fun st => st.find path) =
      (w.storage? r).bind (fun st => st.find path) := by
  rw [World.resetTransient_storage?]
  cases h : w.storage? r with
  | none => rfl
  | some st =>
    change (Storage.resetTransient st).find path = st.find path
    rw [Storage.resetTransient_find, if_neg persistent]

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
