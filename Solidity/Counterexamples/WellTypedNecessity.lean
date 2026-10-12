import Solidity.SortCheck.Faithfulness
import Solidity.Calculus.Lands

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
  an untyped state meeting every other conjunct, where `total` holds a
  `bool`.  The read `x = total;` matches is the path `total`, lowered to the
  symbol `root(total)` (`SPath.lower`, the term `Calculus/LowerRun.lean`
  proves the typed run reads); the symbols of `find(storage, root(total))`,
  evaluated on `badStore` (`Op2.eval`, `Op0.eval`), give that `bool`, and
  so would the term reader (`Tm.evalT`) on any typed state whose global
  part were `badStore`.  The `storageRootReadSelect` row — the one
  `faithful_storageRootReadSelect` proves of every typed state — is false
  of that value.

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

/-- The path `total`. -/
def totalPath : SPath Total [.val .uint] (.prim .uint) := .loc (.root "total" rfl)

/-- `x = total;`, as `storageRootReadSelect` matches it. -/
def totalRead : Stmt Total [.val .uint] [.val .uint] :=
  stmtOf (@Taclet.storageRootReadSelect Total 0 .box [.val .uint] .uint .here "total" rfl)

/-- The row is the live table's: one value read, `\hasSort`-generic. -/
theorem readSelect_row :
    (tacletReadAnns.find? (·.keyName == "storageRootReadSelect")).map valueReads =
      some [⟨.storage, .value, .generic .hasSort⟩] := by
  decide +kernel

/-- **Storage well-typedness is the boundary.**  `badStore` meets every
conjunct of a well-typed global state but `storage`, and the local `x` the
read binds may be a `uint` (`.int 0`).  The read of `x = total;` is the path
`total`, lowered to `root(total)`; `find(storage, root(total))`'s symbols,
evaluated on `badStore`, give a `bool`, as `Tm.evalT` would on a typed state
whose global part were `badStore` (no typed state is: the implication is
vacuous there, which is the point), where the row's `\hasSort` read
promises a `uint`. -/
theorem readSelect_needs_storage :
    nodupKeysB Total.vars = true ∧
    nodupKeysB ([] : HeapTy) = true ∧ heapTypedB [] badStore.heap = true ∧
    HeapWellFormed badStore ∧
    wellTypedStorageB Total.layout badStore.storage = false ∧
    LTy.WT Total [] (.val .uint) (.int 0) ∧
    Stmt.read? totalRead = some (.storage (.prim .uint) totalPath) ∧
    totalPath.lower = .app0 (.root "total") ∧
    Op2.eval badStore .find (Op0.eval badStore .storage) (Op0.eval badStore (.root "total")) =
      .ok (.bool true) ∧
    (∀ σ : State Total [.val .uint], σ.globE = badStore →
      (Tm.app2 .find (.app0 .storage) totalPath.lower).evalT σ = .ok (.bool true)) ∧
    SortOkS (.generic .hasSort) (.prim .uint) (.prim (.bool true)) = false :=
  ⟨by decide, rfl, rfl, (fun _ _ => rfl), by decide, rfl, rfl, rfl, rfl,
    fun σ h => by simp only [Tm.evalT, totalPath, SPath.lower, h]; rfl, rfl⟩

end WellTypedNecessity
end Counterexamples
end Solidity
