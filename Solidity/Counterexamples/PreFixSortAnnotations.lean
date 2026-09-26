import Solidity.SortCheck.Faithfulness

/-!
# The `12e72a1b4b` sort bug, caught

solkey commit `12e72a1b4b` ("removed find<int> to be more generic") replaced
`find<[int]>` reads that values of other sorts could reach.  The rows it
changed are kept as data (`TacletAnnotations.preFixTacletReadAnns`); this
module shows the faithfulness layer refutes them, so a table updated to
match the buggy taclets would not build against `Faithfulness.lean`:

- `preFix_rootCopy_not_faithful` — the pre-fix `storageRootWriteCopySource`
  (`find<[int]>` on the copy source) at `alice = bob;`: the rule reads a
  `Person`, a `Struct` node, not an `int`;
- `preFix_readSelect_not_faithful` — the pre-fix varcond-less
  `storageRootReadSelect` (`find<[int]>`) at `x = flag;` on a `bool` root.

The typed syntax moves the old witness.  Before, the bug was `flag = flag2`
over two `bool` roots, matched by the copy rule; here a `bool` is written
by value (`Src.val`, `storageRootWriteStore`), and only a reference type
reaches the copy rule.  So the pre-fix *struct* twin,
`storageRootWriteCopySource_struct` (`find<[Struct]>`), which the fix deleted
as half of a mis-split pair, is faithful at every statement the copy rule
fires on (`preFix_rootCopyStruct_faithful`): the split the pre-fix pair
attempted is the one the syntax now makes.
-/

namespace Solidity
namespace Counterexamples
namespace PreFixSortAnnotations

open Semantics
open TacletAnnotations
open SortFaithfulness

/-! ## Two small contracts and their stores -/

/-- Two `Person` roots. -/
def People : Contract := contract!{ Person alice; Person bob; }

/-- Two `bool` roots, the fix commit's `storageBoolRootCopy()` test. -/
def Flags : Contract := contract!{ bool flag; bool flag2; }

/-- A `Person` with its members at zero. -/
def person0 : SVal :=
  .struct [("account", .struct [("balance", .int 0), ("token", .struct [("value", .int 0)])]),
    ("age", .int 0)]

/-- `alice` and `bob` at zero. -/
def peopleStore : State := { storage := [("alice", person0), ("bob", person0)] }

/-- The flags, and the local `x` the read binds, declared. -/
def flagStore : State :=
  { storage := [("flag", .bool false), ("flag2", .bool true)],
    env := [(.user "x", .val (.bool false))] }

/-- `bool x;` -/
def flagCtx : Ctx := [(.user "x", .stack (.prim .bool))]

/-- `People`'s store is well-typed. -/
theorem peopleStore_wt : RunWT People [] [] peopleStore :=
  (StateWT.ofB (L := People.layout) (s := peopleStore) (by decide)).toRunWT

/-- `Flags`'s store is well-typed. -/
theorem flagStore_wt : RunWT Flags flagCtx [] flagStore :=
  (StateWT.ofB (Γ := flagCtx) (H := []) (L := Flags.layout) (s := flagStore) (by decide)).toRunWT

/-! ## The copy rule -/

/-- `alice = bob;`, as `storageRootWriteCopySource` matches it. -/
def aliceCopy : Stmt People :=
  stmtOf (@Taclet.storageRootWriteCopySource People 0 .box "alice" (.struct "Person") rfl
    (.loc (.root "bob" rfl)) rfl)

/-- The pre-fix `storageRootWriteCopySource` row is not faithful: at
`alice = bob;` from a well-typed store the copy source is a `Person` node,
where the row declares `find<[int]>`. -/
theorem preFix_rootCopy_not_faithful :
    ¬ RowFaithful preFixStorageRootWriteCopySource aliceCopy := by
  intro h
  obtain ⟨R, hR, _, hall⟩ := h ⟨.storage, .value, .fixed .int⟩ (by decide)
  cases hR
  have := hall [] [] [] peopleStore peopleStore_wt (by decide) "bob" [] person0 rfl rfl
  exact absurd this (by decide)

/-- The fixed row (sort-free `find<[StValue]>`) is faithful there, as
`faithful_storageRootWriteCopySource` says of every instance. -/
theorem current_rootCopy_faithful :
    CtorFaithful ``Taclet.storageRootWriteCopySource aliceCopy :=
  faithful_storageRootWriteCopySource

/-- The pre-fix struct twin (`find<[Struct]>`) is faithful at every statement
the copy rule fires on: `alice = bob;` copies a reference, never a `bool`. -/
theorem preFix_rootCopyStruct_faithful {C : Contract} {k : Nat} {m : Modality} {gsp : Name}
    {R : RefTy} {hgsp : C.rootType gsp = some (.ref R)} {sp : SPath C (.ref R)}
    {hm : (Ty.ref R).mapFree = true} :
    RowFaithful preFixStorageRootWriteCopySourceStruct
      (stmtOf (@Taclet.storageRootWriteCopySource C k m gsp R hgsp sp hm)) :=
  rowFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide)

/-! ## The read rule -/

/-- `x = flag;`, as `storageRootReadSelect` matches it. -/
def flagRead : Stmt Flags :=
  stmtOf (@Taclet.storageRootReadSelect Flags 0 .box (.user "x") "flag" .bool rfl)

/-- The pre-fix `storageRootReadSelect` row (`find<[int]>`, no varcond) is not
faithful: `x = flag;` reads a `bool`. -/
theorem preFix_readSelect_not_faithful :
    ¬ RowFaithful preFixStorageRootReadSelect flagRead := by
  intro h
  obtain ⟨R, hR, _, hall⟩ := h ⟨.storage, .value, .fixed .int⟩ (by decide)
  cases hR
  have := hall flagCtx flagCtx [] flagStore flagStore_wt (by decide) "flag" [] (.bool false) rfl rfl
  exact absurd this (by decide)

/-- The current row (`\hasSort`) is faithful there. -/
theorem current_readSelect_faithful :
    CtorFaithful ``Taclet.storageRootReadSelect flagRead :=
  faithful_storageRootReadSelect

end PreFixSortAnnotations
end Counterexamples
end Solidity
