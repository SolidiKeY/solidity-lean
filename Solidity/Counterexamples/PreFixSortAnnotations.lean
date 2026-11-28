import Solidity.SortCheck.Faithfulness

/-!
# Sort annotation counterexamples

- `preFix_rootCopy_not_faithful` — the pre-fix `storageRootWriteCopySource`
  (`find<[int]>` on the copy source) at `alice = bob;`: the rule reads a
  `Person`, a `Struct` node, not an `int`;
- `preFix_readSelect_not_faithful` — the pre-fix varcond-less
  `storageRootReadSelect` (`find<[int]>`) at `x = flag;` on a `bool` root.

-/

namespace Solidity
namespace Counterexamples
namespace PreFixSortAnnotations

open TacletAnnotations
open SortFaithfulness

/-! ## Two small contracts -/

/-- Two `Person` roots. -/
def People : Contract := contract!{ Person alice; Person bob; }

/-- Two `bool` roots. -/
def Flags : Contract := contract!{ bool flag; bool flag2; }

/-- A `Person` is a `Struct` node, never an `int`. -/
theorem person_not_int (v : SVal (.ref (.struct "Person"))) :
    SortOkS (.fixed .int) v = false := by
  cases v with
  | struct fs => rfl

/-- A `bool` is not an `int`. -/
theorem bool_not_int (v : SVal (.prim .bool)) :
    SortOkS (.fixed .int) v = false := by
  cases v with
  | prim b => rfl

/-! ## The copy rule -/

/-- `alice = bob;`, as `storageRootWriteCopySource` matches it. -/
def aliceCopy : Stmt People [] [] :=
  stmtOf (@Taclet.storageRootWriteCopySource People 0 .box [] "alice" (.struct "Person") rfl
    (.loc (.root "bob" rfl)) rfl rfl)

/-- The pre-fix `storageRootWriteCopySource` row is not faithful: at
`alice = bob;` from the initial state the copy source is a `Person` node,
where the row declares `find<[int]>`. -/
theorem preFix_rootCopy_not_faithful :
    ¬ RowFaithful preFixStorageRootWriteCopySource aliceCopy := by
  intro h
  obtain ⟨R, hR, _, hall⟩ := h ⟨.storage, .value, .fixed .int⟩ (by decide)
  cases hR
  have := hall (State.init People) (SRef.ofRoot "bob" rfl) _ rfl rfl
  rw [person_not_int] at this
  exact Bool.false_ne_true this

/-- The fixed row (sort-free `find<[StValue]>`) is faithful there, as
`faithful_storageRootWriteCopySource` says of every instance. -/
theorem current_rootCopy_faithful :
    CtorFaithful ``Taclet.storageRootWriteCopySource aliceCopy :=
  faithful_storageRootWriteCopySource

/-- The pre-fix struct twin (`find<[Struct]>`) is faithful at every statement
the copy rule fires on: `alice = bob;` copies a reference, never a `bool`. -/
theorem preFix_rootCopyStruct_faithful {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx}
    {gsp : Name} {R : RefTy} {hgsp : C.rootType gsp = some (.ref R)}
    {sp : SPath C Γ (.ref R)} {hm : (Ty.ref R).mapFree = true} {hsp : sp.isSimple = true} :
    RowFaithful preFixStorageRootWriteCopySourceStruct
      (stmtOf (@Taclet.storageRootWriteCopySource C k m Γ gsp R hgsp sp hm hsp)) :=
  rowFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide)

/-! ## The read rule -/

/-- `x = flag;`, as `storageRootReadSelect` matches it. -/
def flagRead : Stmt Flags [.val .bool] [.val .bool] :=
  stmtOf (@Taclet.storageRootReadSelect Flags 0 .box [.val .bool] .bool .here "flag" rfl)

/-- The pre-fix `storageRootReadSelect` row (`find<[int]>`, no varcond) is not
faithful: `x = flag;` reads a `bool`. -/
theorem preFix_readSelect_not_faithful :
    ¬ RowFaithful preFixStorageRootReadSelect flagRead := by
  intro h
  obtain ⟨R, hR, _, hall⟩ := h ⟨.storage, .value, .fixed .int⟩ (by decide)
  cases hR
  have := hall ((State.init Flags).push (t := .val .bool) (false : Bool))
    (SRef.ofRoot "flag" rfl) _ rfl rfl
  rw [bool_not_int] at this
  exact Bool.false_ne_true this

/-- The current row (`\hasSort`) is faithful there. -/
theorem current_readSelect_faithful :
    CtorFaithful ``Taclet.storageRootReadSelect flagRead :=
  faithful_storageRootReadSelect

end PreFixSortAnnotations
end Counterexamples
end Solidity
