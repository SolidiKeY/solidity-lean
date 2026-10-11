import Solidity.SortCheck.Faithfulness

/-!
# The sort claims stand on well-typed storage

Does `select<[alphaPrim]>(storage, total)` need a well-formed storage to
return a number where `total : uint`?  Split by what the question is about:

- **In the KeY calculus: no.**  A read on a mismatching store degrades to an
  underspecified cast (`selectOnStore` yields `cast<[alpha]>(v)`, which
  `cast.key` gives no axioms at the mismatch), and an underspecified value
  proves nothing false.  The calculus is sort-sound with no well-formedness
  predicate.
- **Of the values the interpreter finds: yes.**  `RunWT` minus its storage
  conjunct does not carry the claim: `readSelect_needs_storage` is a state
  meeting every other conjunct, where `total` holds a `bool` and the current
  `storageRootReadSelect` row — the one `faithful_storageRootReadSelect`
  proves under `RunWT` — is false.

So any claim that a sorted read denotes the value really stored needs
`wellFormed(storage)` in the proof obligation and its preservation by every
write: `State.erase_wt` (`Typing/TypedWT.lean`) is that fact, by
construction.
-/

namespace Solidity
namespace Counterexamples
namespace WellTypedNecessity

open Semantics
open SemanticsProperties (HeapWellFormed)
open TacletAnnotations
open SortFaithfulness

/-- One `uint` root. -/
def Total : Contract := contract!{ uint total; }

/-- The minimal ill-typed store: `total` holds a `bool`. -/
def badStore : Semantics.State := { storage := [("total", .bool true)] }

/-- `badStore`, as a scoped state with the local `uint x` the read binds. -/
def badCore : EState Total [.val .uint] := EState.ofGlob badStore (.int 0, ())

/-- `x = total;`, as `storageRootReadSelect` matches it. -/
def totalRead : Stmt Total [.val .uint] [.val .uint] :=
  stmtOf (@Taclet.storageRootReadSelect Total 0 .box [.val .uint] .uint .here "total" rfl)

/-- The row is the live table's: one value read, `\hasSort`-generic. -/
theorem readSelect_row :
    (tacletReadAnns.find? (·.keyName == "storageRootReadSelect")).map valueReads =
      some [⟨.storage, .value, .generic .hasSort⟩] := by
  decide +kernel

/-- **Storage well-typedness is the boundary.**  `badStore` meets every
conjunct of `RunWT` but `storage` (with `x`, the local the read binds, a
`uint`), and there `x = total;` finds a `bool` where the row's `\hasSort`
read promises a `uint`. -/
theorem readSelect_needs_storage :
    nodupKeysB Total.vars = true ∧
    nodupKeysB ([] : HeapTy) = true ∧ heapTypedB [] badStore.heap = true ∧
    HeapWellFormed badStore ∧
    wellTypedStorageB Total.layout badStore.storage = false ∧
    Stmt.read? totalRead = some (.storage (.prim .uint) (.loc (.root "total" rfl))) ∧
    ¬ (Read.storage (.prim .uint) (.loc (.root "total" rfl)) : Read Total [.val .uint]).SortOk
      badCore [] (.generic .hasSort) := by
  refine ⟨by decide, rfl, rfl, (fun _ _ => rfl), by decide, rfl, ?_⟩
  intro h
  exact absurd (h "total" [] (.bool true) rfl rfl) (by decide)

end WellTypedNecessity
end Counterexamples
end Solidity
