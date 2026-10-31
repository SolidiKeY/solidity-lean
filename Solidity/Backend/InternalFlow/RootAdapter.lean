import Solidity.Semantics.Run
import Solidity.Backend.Failure.Unwind

/-!
# Actual logical root projections at a local byte-emission checkpoint

The existing Failure checkpoint is instantiated with typed projections of the
published joint Storage product. No new storage, world, rollback or byte
semantics is introduced. Restoring these projections does not reconstruct a
whole State or prove that a source call rolls back.
-/
namespace Solidity.Backend.InternalFlow

open Backend.Failure

variable {C : Contract} {P T : Ty}

/-- Extract separately typed persistent/transient root values and an actual
checked-slice machine. The region certificates forbid aliasing the roots. -/
def rootJournal (persistent : Storage.RegionRoot C false P)
    (transient : Storage.RegionRoot C true T) (store : Storage C)
    (machine : Slice.Machine) : Local.Journal (SVal P) (SVal T) :=
  ⟨store.get persistent.declared, store.get transient.declared, machine⟩

/-- An actual emitted failure restores both certified root projections and
the saved machine, while returning the original immutable bytes. Remaining
roots and whole-state reconstruction are outside this projection theorem. -/
theorem root_failure (persistent : Storage.RegionRoot C false P)
    (transient : Storage.RegionRoot C true T) (saved live : Storage C)
    (caller machine : Slice.Machine) (offset : Nat) (bytes : List UInt8)
    (fits : Fits offset bytes) (stack : machine.stack.length + 2 ≤ 1024) :
    Local.execute (Local.save (rootJournal persistent transient saved caller)) offset
      (.custom bytes) (rootJournal persistent transient live machine) =
      some (rootJournal persistent transient saved caller, .revert bytes) :=
  Local.execute_failure _ offset bytes _ fits stack

/-- Actual successful payload emission retains the live root projections. -/
theorem root_return (persistent : Storage.RegionRoot C false P)
    (transient : Storage.RegionRoot C true T) (saved live : Storage C)
    (caller machine : Slice.Machine) (offset : Nat) (bytes : List UInt8)
    (fits : Fits offset bytes) (stack : machine.stack.length + 2 ≤ 1024) :
    Local.execute (Local.save (rootJournal persistent transient saved caller)) offset
      (.returned bytes) (rootJournal persistent transient live machine) =
      some (rootJournal persistent transient live
        { machine with memory := Slice.putBytes machine.memory offset bytes }, .success bytes) :=
  Local.execute_return _ offset bytes _ fits stack

/-- The persistent projection is invariant under a transient root update. -/
theorem root_write_noninterference (persistent : Storage.RegionRoot C false P)
    (transient : Storage.RegionRoot C true T) (store : Storage C)
    (machine : Slice.Machine) (value : SVal T) :
    (rootJournal persistent transient (store.set transient.declared value) machine).persistent =
      (rootJournal persistent transient store machine).persistent :=
  persistent.persistent_write transient store value

/-- Transaction entry is idempotent for the actual intrinsic state, including
fresh empty heap typing, memory and locals. -/
theorem transaction_entry_idempotent (state : State C []) :
    state.transactionEntry.transactionEntry = state.transactionEntry := by
  simp only [State.transactionEntry, Storage.resetTransient_idem]

/-- Local scope unwind and transaction normalization agree on all surviving
fields. Internal calls do not perform this transaction operation. -/
theorem transaction_after_unwind {Γ : Ctx} (scope : Ext [] Γ) (state : State C Γ) :
    (state.drop scope).transactionEntry = state.glob.transactionEntry := rfl

/-- Reset acts on the restored store, never on a discarded live store. This
uses the existing withStorage operation, not a new source failure semantics. -/
theorem reset_restored_store (state : State C []) (saved : Storage C) :
    (state.withStorage saved).transactionEntry =
      state.transactionEntry.withStorage (Storage.resetTransient saved) := rfl

/-- Reset keeps persistent roots and defaults transient roots, at their exact
published storage types. Membership follows from the region certificates. -/
theorem reset_root_pair (persistent : Storage.RegionRoot C false P)
    (transient : Storage.RegionRoot C true T) (store : Storage C)
    :
    (Storage.resetTransient store).get persistent.declared = store.get persistent.declared ∧
    (Storage.resetTransient store).get transient.declared = (Storage.init C).get transient.declared := by
  have hp : persistent.name ∉ C.transientRoots := by
    intro h
    have impossible : C.transientRoots.contains persistent.name = true := List.contains_iff.mpr h
    rw [persistent.region] at impossible
    cases impossible
  have ht : transient.name ∈ C.transientRoots := List.contains_iff.mp transient.region
  constructor
  · rw [Storage.resetTransient_get, if_neg hp]
  · rw [Storage.resetTransient_get, if_pos ht]

end Solidity.Backend.InternalFlow
