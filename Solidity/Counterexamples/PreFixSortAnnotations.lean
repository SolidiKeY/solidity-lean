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

And the **open findings**: the same failure shape reproduced against
two `find<[Struct]>` reads still in the current taclet file
(`storageFieldWriteCopySource`, `storagePushValueCopySource`), whose
`Path[storage,simple]` sources can be primitive-typed. These are
Lean-model results — confirm against KeY's schema-sort dispatch before
filing upstream.
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

/-! ## Open findings: the surviving `find<[Struct]>` reads

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

/-- **Open finding.** `storageFieldWriteCopySource` reads its
`Path[storage,simple]` source with `find<[Struct]>` — but on
`alice.age = total` (a legal Solidity statement matching the taclet's
schema) the source is a `uint` root and the interpreter finds
`SVal.int 42`, not a tree node. The same bug family `12e72a1b4b`
fixed for the root-copy rules survives here. -/
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

/-- **Open finding.** `storagePushValueCopySource` reads the pushed
`Path[storage,simple]` source with `find<[Struct]>` — but on
`values.push(total)` with `values : uint[]` the source is a `uint`
root. Same failure shape. -/
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

-- The two counterexample rows above are literally the table's rows for
-- these taclets (the refutations target what `solkeycheck` pins, not a
-- strawman).
example :
    tacletReadAnns.filter
        (fun ann => SortFaithfulness.openFindings.contains ann.keyName) =
      [ { keyName := "storageFieldWriteCopySource"
          leanRule := some .storageFieldWriteCopySource
          reads := [⟨.storage, .value, .fixed .struct⟩] },
        { keyName := "storagePushValueCopySource"
          leanRule := some .storagePushValueCopySource
          reads := [⟨.storage, .length, .fixed .int⟩,
            ⟨.storage, .value, .fixed .struct⟩,
            ⟨.storage, .length, .fixed .int⟩] } ] := by
  native_decide

end PreFixSortAnnotations
end Counterexamples
end Solidity
