import Solidity.Backend.FailurePaths.TransientSharing
import Solidity.Backend.Transient.Mixed

/-! G39 actual target composition: transient write, ordinary persistent/memory
instructions, and a later observed same-owner read. This target theorem does
not supply Source persistent/memory lowering or G24/full-world representation. -/
namespace Solidity.Backend.FailurePaths.TransientComposition
open Source

def mixed (parent child : Fr) (key value : Transient.Word) (entry : Transient.State) :
    Option (Transient.Result × Option Evm.Word) :=
  match Transient.callbackInFrame parent (Transient.storeCode key value) entry with
  | .error _ _ => none
  | .ok next => do
      let reached ← Transient.Mixed.execute next
      pure (TransientSharing.observed child (Transient.loadCode key) reached)

def reached (parent : Fr) (key value : Transient.Word) (entry : Transient.State) : Transient.State :=
  let written := Transient.write entry parent.this key value
  ⟨Transient.Mixed.afterMachine entry.machine, written.bank, written.journal⟩

/-- The ordinary instructions really execute between the two framed bodies.
The observed transient word survives; caller machine restoration keeps the
ordinary writes because their reached machine is the child's actual entry. -/
theorem mixed_run (parent child : Fr) (normal : parent.static = false)
    (sameOwner : child.this = parent.this) (key value : Transient.Word) (entry : Transient.State) :
    mixed parent child key value entry =
      some (.ok (reached parent key value entry), some (.val value)) := by
  simp only [mixed, Transient.framed_store parent normal, Transient.Mixed.execute_exact,
    bind, Option.bind, pure]
  rw [TransientSharing.load_observed, sameOwner]
  simp only [reached, Transient.write, Transient.put_same]

/-- Executed mixed writes retain distinct roots at reset. The persistent root
may have the same numeric key as a transient slot without aliasing that bank. -/
theorem reset_distinct_roots (parent : Fr) (key value : Transient.Word) (entry : Transient.State) :
    (Transient.endTx (reached parent key value entry)).machine.store (.root 7) = 0x5566 ∧
    (Transient.endTx (reached parent key value entry)).machine.mem 3 = .val ⟨0xa1ff, by decide⟩ ∧
    (Transient.endTx (reached parent key value entry)).bank parent.this key = ⟨0, by decide⟩ ∧
    (Transient.endTx (reached parent key value entry)).journal = [] := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact Evm.WordStore.write_same _ _ _
  · change Evm.upd entry.machine.mem 3 (.val ⟨0xa1ff, by decide⟩) 3 = .val ⟨0xa1ff, by decide⟩
    exact Evm.upd_same entry.machine.mem 3 (.val ⟨0xa1ff, by decide⟩)

def mixedReset (parent child : Fr) (key value : Transient.Word) (entry : Transient.State) :
    Option Transient.State :=
  match mixed parent child key value entry with
  | some (.ok next, _) => some (Transient.endTx next)
  | _ => none

theorem mixed_reset_run (parent child : Fr) (normal : parent.static = false)
    (sameOwner : child.this = parent.this) (key value : Transient.Word) (entry : Transient.State) :
    mixedReset parent child key value entry = some (Transient.endTx (reached parent key value entry)) := by
  simp only [mixedReset, mixed_run parent child normal sameOwner]

#print axioms mixed_run
#print axioms reset_distinct_roots
#print axioms mixed_reset_run
end Solidity.Backend.FailurePaths.TransientComposition
