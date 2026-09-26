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
write: `Prog.run_wt` is that preservation.
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
def badStore : State := { storage := [("total", .bool true)] }

/-- `x = total;`, as `storageRootReadSelect` matches it. -/
def totalRead : Stmt Total :=
  stmtOf (@Taclet.storageRootReadSelect Total 0 .box (.user "x") "total" .uint rfl)

/-- The row is the live table's: one value read, `\hasSort`-generic. -/
theorem readSelect_row :
    (tacletReadAnns.find? (·.keyName == "storageRootReadSelect")).map valueReads =
      some [⟨.storage, .value, .generic .hasSort⟩] := by
  decide +kernel

/-- **Storage well-typedness is the boundary.**  `badStore` meets every
conjunct of `RunWT` but `storage`, and there `x = total;` finds a `bool`
where the row's `\hasSort` read promises a `uint`. -/
theorem readSelect_needs_storage :
    nodupKeysB Total.vars = true ∧ EnvWT [] Total.layout [] badStore.env ∧
    nodupKeysB ([] : HeapTy) = true ∧ heapTypedB [] badStore.heap = true ∧
    HeapWellFormed badStore ∧
    wellTypedStorageB Total.layout badStore.storage = false ∧
    Stmt.read? totalRead = some (.storage (.prim .uint) (.loc (.root "total" rfl))) ∧
    ¬ (Read.storage (.prim .uint) (.loc (.root "total" rfl)) : Read Total).SortOk badStore []
      (.generic .hasSort) := by
  refine ⟨by decide, (fun _ _ h => nomatch h), rfl, rfl, (fun _ _ => rfl), by decide, rfl, ?_⟩
  intro h
  exact absurd (h "total" [] (.bool true) rfl rfl) (by decide)

end WellTypedNecessity
end Counterexamples
end Solidity
