import Solidity.SortCheck.Faithfulness

/-!
# The `12e72a1b4b` sort bug, caught

Concrete refutations showing that the sort-faithfulness layer catches
the bug solkey commit `12e72a1b4b` ("removed find<int> to be more
generic") fixed — and would have caught it *before* the fix, had the
layer existed:

- `preFix_rootCopy_not_sortFaithful` — the pre-fix
  `storageRootWriteCopySource` annotation (`find<[int]>` on a
  `Path[storage,simple]` source) fails on the exact bug scenario
  `flag = flag2` over two `bool` storage roots: the interpreter finds
  `SVal.bool true` where the taclet declares an int-sorted read.
- `preFix_readSelect_not_sortFaithful` — same failure for the pre-fix
  varcond-less `storageRootReadSelect`.
- `current_rootCopy_sortFaithful` — the *fixed* annotation (sort-free
  `find<[StValue]>`) is faithful, as `sortFaithful_all` already
  implies.

And the **former open findings**: the same failure shape reproduced
against the two `find<[Struct]>` reads that survived the fix until
solkey `29c44e225b` (`storageFieldWriteCopySource`,
`storagePushValueCopySource`), whose `Path[storage,simple]` sources can
be primitive-typed. That commit replaced both by the sort-free
`find<[StValue]>`, so `SortFaithfulness.openFindings` is empty; the
refutations stay as the record of what the table's rows claimed, and
the closing `example` checks the table's current rows for the two
taclets are the fixed shape.
-/

namespace Solidity
namespace Counterexamples
namespace PreFixSortAnnotations

open Semantics
open TacletAnnotations
open SortFaithfulness

/-! ## The bug witness: `flag = flag2` on two bool storage roots -/

def flagLayout : Layout :=
  ⟨[("flag", Ty.bool), ("flag2", Ty.bool)]⟩

def flagState : State :=
  { storage := [("flag", SVal.bool false), ("flag2", SVal.bool true)] }

def flagField : Field :=
  Field.primitive "flag" Ty.bool (some StorageOrigin.global)

def flag2Field : Field :=
  Field.primitive "flag2" Ty.bool (some StorageOrigin.global)

def flagPlace : PlaceExpr :=
  PlaceExpr.var Kind.storage Ty.bool flagField

def flag2Expr : WrappedExpr :=
  WrappedExpr.var Kind.storage Ty.bool flag2Field

/-- The bug scenario: copy one bool storage root into another
(solkey's `storageBoolRootCopy()` test, added by the fix commit). -/
def flagStmt : Stmt :=
  Stmt.assign flagPlace flag2Expr

theorem resolveS_flag2 :
    resolveS flagState flag2Expr =
      Except.ok (flagState, "flag2", ([] : List Seg)) := by
  show resolveS flagState
    (WrappedExpr.var Kind.storage Ty.bool flag2Field) = _
  rw [resolveS]
  rfl

/-- The pre-fix `storageRootWriteCopySource` (`find<[int]>` on the
copy source) is NOT sort-faithful: on `flag = flag2` the interpreter
finds `SVal.bool true` where the taclet declares an int-sorted read.
This is the `12e72a1b4b` bug, caught. -/
theorem preFix_rootCopy_not_sortFaithful :
    ¬ SortFaithful preFixStorageRootWriteCopySource := by
  intro h
  have hclaim := h flagLayout flagState flagStmt
    .storageRootWriteCopySource rfl
    (by native_decide) (by native_decide)
    ⟨rfl, rfl, rfl⟩
    ⟨.storage, .value, .fixed .int⟩ (List.Mem.head _) rfl
    flag2Expr rfl (by native_decide)
    flagState "flag2" [] (SVal.bool true) resolveS_flag2 rfl
  exact Bool.noConfusion hclaim

/-- The deleted `storageRootWriteCopySource_struct` half of the pre-fix
rule pair fails on the same witness (`Struct`-sorted read of a bool). -/
theorem preFix_rootCopyStruct_not_sortFaithful :
    ¬ SortFaithful preFixStorageRootWriteCopySourceStruct := by
  intro h
  have hclaim := h flagLayout flagState flagStmt
    .storageRootWriteCopySource rfl
    (by native_decide) (by native_decide)
    ⟨rfl, rfl, rfl⟩
    ⟨.storage, .value, .fixed .struct⟩ (List.Mem.head _) rfl
    flag2Expr rfl (by native_decide)
    flagState "flag2" [] (SVal.bool true) resolveS_flag2 rfl
  exact Bool.noConfusion hclaim

def resultPlace : PlaceExpr :=
  PlaceExpr.var Kind.stack Ty.bool (Field.primitive "result" Ty.bool)

/-- `result = flag2;` — the pre-fix varcond-less `storageRootReadSelect`
(`find<[int]>`) mis-sorts the bool read the same way. -/
theorem preFix_readSelect_not_sortFaithful :
    ¬ SortFaithful preFixStorageRootReadSelect := by
  intro h
  have hclaim := h flagLayout flagState
    (Stmt.assign resultPlace flag2Expr)
    .storageRootReadSelect rfl
    (by native_decide) (by native_decide)
    ⟨rfl, rfl, rfl⟩
    ⟨.storage, .value, .fixed .int⟩ (List.Mem.head _) rfl
    flag2Expr rfl (by native_decide)
    flagState "flag2" [] (SVal.bool true) resolveS_flag2 rfl
  exact Bool.noConfusion hclaim

/-- Sanity: the CURRENT (post-fix, sort-free) annotation of the same
rule is faithful — indeed vacuously, which is the correct formal
content of the fix: `find<[StValue]>` claims nothing, so nothing can
drift. -/
theorem current_rootCopy_sortFaithful :
    SortFaithful
      { keyName := "storageRootWriteCopySource"
        leanRule := some .storageRootWriteCopySource
        reads := [⟨.storage, .value, .fixed .stValue⟩] } :=
  sortFaithful_of_annOkB _ (by native_decide)

/-! ## Former open findings: the `find<[Struct]>` reads `29c44e225b` removed

Witness layout: `alice : Person` (struct), `total : uint`,
`values : uint[]` — all contract-level storage roots. -/

def findingLayout : Layout :=
  ⟨[("alice", Ty.ref (RefTy.struct "Person")), ("total", Ty.uint),
    ("values", Ty.ref (RefTy.array Ty.uint))]⟩

def findingState : State :=
  { storage :=
      [("alice", SVal.struct []), ("total", SVal.int 42),
        ("values", SVal.array [] [])] }

def aliceExpr : WrappedExpr :=
  WrappedExpr.var Kind.storage (Ty.ref (RefTy.struct "Person"))
    (Field.identity "alice" (RefTy.struct "Person")
      (some StorageOrigin.global))

def agePlace : PlaceExpr :=
  PlaceExpr.field Kind.storage Ty.uint aliceExpr
    (Field.primitive "age" Ty.uint)

def totalExpr : WrappedExpr :=
  WrappedExpr.var Kind.storage Ty.uint
    (Field.primitive "total" Ty.uint (some StorageOrigin.global))

theorem resolveS_total :
    resolveS findingState totalExpr =
      Except.ok (findingState, "total", ([] : List Seg)) := by
  show resolveS findingState
    (WrappedExpr.var Kind.storage Ty.uint
      (Field.primitive "total" Ty.uint (some StorageOrigin.global))) = _
  rw [resolveS]
  rfl

/-- **Former open finding** (fixed upstream by `29c44e225b`).
`storageFieldWriteCopySource` read its `Path[storage,simple]` source
with `find<[Struct]>` — but on `alice.age = total` (a legal Solidity
statement matching the taclet's schema) the source is a `uint` root and
the interpreter finds `SVal.int 42`, not a tree node. The same bug
family `12e72a1b4b` fixed for the root-copy rules survived here. -/
theorem fieldWriteCopySource_not_sortFaithful :
    ¬ SortFaithful
        { keyName := "storageFieldWriteCopySource"
          leanRule := some .storageFieldWriteCopySource
          reads := [⟨.storage, .value, .fixed .struct⟩] } := by
  intro h
  have hclaim := h findingLayout findingState
    (Stmt.assign agePlace totalExpr)
    .storageFieldWriteCopySource rfl
    (by native_decide) (by native_decide)
    ⟨rfl, rfl, rfl⟩
    ⟨.storage, .value, .fixed .struct⟩ (List.Mem.head _) rfl
    totalExpr rfl (by native_decide)
    findingState "total" [] (SVal.int 42) resolveS_total rfl
  exact Bool.noConfusion hclaim

def valuesPlace : PlaceExpr :=
  PlaceExpr.var Kind.storage (Ty.ref (RefTy.array Ty.uint))
    (Field.identity "values" (RefTy.array Ty.uint)
      (some StorageOrigin.global))

/-- **Former open finding** (fixed upstream by `29c44e225b`).
`storagePushValueCopySource` read the pushed `Path[storage,simple]`
source with `find<[Struct]>` — but on `values.push(total)` with
`values : uint[]` the source is a `uint` root. Same failure shape. -/
theorem pushValueCopySource_not_sortFaithful :
    ¬ SortFaithful
        { keyName := "storagePushValueCopySource"
          leanRule := some .storagePushValueCopySource
          reads := [⟨.storage, .length, .fixed .int⟩,
            ⟨.storage, .value, .fixed .struct⟩,
            ⟨.storage, .length, .fixed .int⟩] } := by
  intro h
  have hclaim := h findingLayout findingState
    (Stmt.push valuesPlace (some totalExpr))
    .storagePushValueCopySource rfl
    (by native_decide) (by native_decide)
    ⟨rfl, rfl, rfl, rfl⟩
    ⟨.storage, .value, .fixed .struct⟩
    (List.Mem.tail _ (List.Mem.head _)) rfl
    totalExpr rfl (by native_decide)
    findingState "total" [] (SVal.int 42) resolveS_total rfl
  exact Bool.noConfusion hclaim

-- The two counterexample rows above were literally the table's rows for
-- these taclets until `29c44e225b`; the table's current rows (what
-- `solkeycheck` pins) differ from them exactly in the value read, now
-- the sort-free `find<[StValue]>` — and nothing is left open.
example :
    tacletReadAnns.filter
        (fun ann => ann.keyName == "storageFieldWriteCopySource" ||
          ann.keyName == "storagePushValueCopySource") =
      [ { keyName := "storageFieldWriteCopySource"
          leanRule := some .storageFieldWriteCopySource
          reads := [⟨.storage, .value, .fixed .stValue⟩] },
        { keyName := "storagePushValueCopySource"
          leanRule := some .storagePushValueCopySource
          reads := [⟨.storage, .length, .fixed .int⟩,
            ⟨.storage, .value, .fixed .stValue⟩,
            ⟨.storage, .length, .fixed .int⟩] } ] ∧
    SortFaithfulness.openFindings = [] := by
  constructor <;> native_decide

end PreFixSortAnnotations
end Counterexamples
end Solidity
