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
- **Of the values the interpreter finds: yes.**  Well-typedness minus its
  storage conjunct does not carry the claim: `readSelect_needs_storage` is
  an untyped state meeting every other conjunct, where `total` holds a `bool`
  and the current `storageRootReadSelect` row — the one
  `faithful_storageRootReadSelect` proves of every typed state — is false of
  what the read finds.

So any claim that a sorted read denotes the value really stored needs
`wellFormed(storage)` in the proof obligation and its preservation by every
write: a typed state is that fact, by construction (`State.glob_wt`,
`Typing/TypedWT.lean`), and no typed state is `badStore`.
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

/-- `x = total;`, as `storageRootReadSelect` matches it. -/
def totalRead : Stmt Total [.val .uint] [.val .uint] :=
  stmtOf (@Taclet.storageRootReadSelect Total 0 .box [.val .uint] .uint .here "total" rfl)

/-- The row is the live table's: one value read, `\hasSort`-generic. -/
theorem readSelect_row :
    (tacletReadAnns.find? (·.keyName == "storageRootReadSelect")).map valueReads =
      some [⟨.storage, .value, .generic .hasSort⟩] := by
  decide +kernel

/-- **Storage well-typedness is the boundary.**  `badStore` meets every
conjunct of `StateWT` but `storage` (with `x`, the local the read binds, a
`uint`), and there the read of `x = total;` finds a `bool` where the row's
`\hasSort` read promises a `uint`. -/
theorem readSelect_needs_storage :
    nodupKeysB Total.vars = true ∧
    nodupKeysB ([] : HeapTy) = true ∧ heapTypedB [] badStore.heap = true ∧
    HeapWellFormed badStore ∧
    wellTypedStorageB Total.layout badStore.storage = false ∧
    Env.All (LTy.WT Total []) (Γ := [.val .uint]) (.int 0, ()) ∧
    Stmt.read? totalRead = some (.storage (.prim .uint) (.loc (.root "total" rfl))) ∧
    badStore.findStorage "total" [] = .ok (.bool true) ∧
    SortOkS (.generic .hasSort) (.prim .uint) (.bool true) = false :=
  ⟨by decide, rfl, rfl, (fun _ _ => rfl), by decide, ⟨rfl, trivial⟩, rfl, rfl, rfl⟩

end WellTypedNecessity
end Counterexamples
end Solidity
