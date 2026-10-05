import Solidity.Typing.Constructibility
import Solidity.Semantics.WellFormed

/-!
# The test `wt(storage)` makes decides `canon ∧ tight`

`storageWtB` (`Semantics/WellFormed.lean`) is a test the interpreter runs;
`SVal.canon` (`Typing/Reachability.lean`) and `SVal.tight`
(`Typing/Constructibility.lean`) are the propositions the reachability
proofs are about.  The tests are written clause for clause like the
propositions, so each equivalence is one case per clause.  The closer reads
a default as canonical through them (`defaultForTy_canonB`), and the
obligations' premise through them (`Calculus/Problem.lean`).
-/

namespace Solidity

open Semantics
open Semantics.SVal.canon (canonFields canonElems canonEntries)
open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB)
open Semantics.SVal.tight (tightFields tightElems tightEntries)
open Semantics.SVal.tightB (tightFieldsB tightElemsB tightEntriesB)
open SemanticsProperties (lookupBy_eq_some_mem)

/-! ## The test decides `canon ∧ tight` -/

mutual

theorem SVal.canonB_iff : ∀ {v : SVal} {T : Ty}, v.canonB T = true ↔ v.canon T
  | SVal.prim (.int _), Ty.int | SVal.prim (.int _), Ty.uint | SVal.prim (.bool _), Ty.bool =>
    ⟨fun _ => trivial, fun _ => rfl⟩
  | SVal.struct fields, Ty.ref (RefTy.struct s) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true, decide_eq_true_eq,
      SVal.canonFieldsB_iff]
  | SVal.array elems shadow fx, Ty.ref (RefTy.array E) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true, Bool.not_eq_true',
      SVal.canonElemsB_iff, and_assoc]
  | SVal.array elems shadow fx, Ty.ref (RefTy.fixed E n) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true, decide_eq_true_eq,
      SVal.canonElemsB_iff, and_assoc]
  | SVal.map entries dflt, Ty.ref (RefTy.mapping _ V) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true,
      SVal.canonEntriesB_iff, SVal.isDfltB_iff, SVal.canonB_iff (v := dflt), and_assoc]
  | SVal.prim (.int _), Ty.bool | SVal.prim (.bool _), Ty.uint | SVal.prim (.bool _), Ty.int
  | SVal.prim _, Ty.ref _
  | SVal.struct _, Ty.prim _ | SVal.struct _, Ty.ref (.array _)
  | SVal.struct _, Ty.ref (.fixed _ _) | SVal.struct _, Ty.ref (.mapping _ _)
  | SVal.array .., Ty.prim _ | SVal.array .., Ty.ref (.struct _)
  | SVal.array .., Ty.ref (.mapping _ _)
  | SVal.map .., Ty.prim _ | SVal.map .., Ty.ref (.struct _)
  | SVal.map .., Ty.ref (.array _) | SVal.map .., Ty.ref (.fixed _ _) =>
    ⟨fun h => by simp only [SVal.canonB, Bool.false_eq_true] at h,
      fun h => by simp only [SVal.canon] at h⟩

theorem SVal.canonFieldsB_iff {s : Name} :
    ∀ {fs : List (Name × SVal)}, canonFieldsB s fs = true ↔ canonFields s fs
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (n, v) :: rest => by
    simp only [canonFieldsB, canonFields, Bool.and_eq_true, SVal.canonFieldsB_iff (fs := rest)]
    cases lookupBy n (structDef s) with
    | none => simp only [Bool.false_eq_true, false_and]
    | some T => simp only [SVal.canonB_iff (v := v) (T := T)]

theorem SVal.canonElemsB_iff {E : Ty} :
    ∀ {es : List SVal}, canonElemsB E es = true ↔ canonElems E es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | v :: rest => by
    simp only [canonElemsB, canonElems, Bool.and_eq_true, SVal.canonB_iff (v := v),
      SVal.canonElemsB_iff (es := rest)]

theorem SVal.canonEntriesB_iff {V : Ty} :
    ∀ {es : List (Int × SVal)}, canonEntriesB V es = true ↔ canonEntries V es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (_, v) :: rest => by
    simp only [canonEntriesB, canonEntries, Bool.and_eq_true, SVal.canonB_iff (v := v),
      SVal.canonEntriesB_iff (es := rest)]

end

mutual

theorem SVal.tightB_iff : ∀ {v : SVal} {T : Ty}, v.tightB T = true ↔ v.tight T
  | SVal.struct fields, Ty.ref (RefTy.struct s) => by
    simp only [SVal.tightB, SVal.tight, SVal.tightFieldsB_iff]
  | SVal.array elems shadow _, Ty.ref (RefTy.array E) => by
    simp only [SVal.tightB, SVal.tight, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff,
      Bool.not_eq_true', List.all_eq_true, SVal.isDfltB_iff, SVal.tightElemsB_iff, and_assoc]
    cases E.defaultOkS <;> cases E.isPrimitive <;>
      simp only [true_or, false_or, Bool.false_eq_true, Bool.true_eq_false, true_and,
        forall_const, false_implies]
  | SVal.array elems shadow _, Ty.ref (RefTy.fixed E _) => by
    simp only [SVal.tightB, SVal.tight, Bool.and_eq_true, List.isEmpty_iff,
      SVal.tightElemsB_iff]
  | SVal.map entries _, Ty.ref (RefTy.mapping K V) => by
    simp only [SVal.tightB, SVal.tight, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff,
      SVal.tightEntriesB_iff]
    cases K.numericKey <;>
      simp only [true_or, false_or, Bool.false_eq_true, true_and, forall_const, reduceCtorEq,
        false_implies]
  | SVal.prim _, _
  | SVal.struct _, Ty.prim _ | SVal.struct _, Ty.ref (.array _)
  | SVal.struct _, Ty.ref (.fixed _ _) | SVal.struct _, Ty.ref (.mapping _ _)
  | SVal.array .., Ty.prim _ | SVal.array .., Ty.ref (.struct _)
  | SVal.array .., Ty.ref (.mapping _ _)
  | SVal.map .., Ty.prim _ | SVal.map .., Ty.ref (.struct _)
  | SVal.map .., Ty.ref (.array _) | SVal.map .., Ty.ref (.fixed _ _) =>
    ⟨fun _ => trivial, fun _ => rfl⟩

theorem SVal.tightFieldsB_iff {s : Name} :
    ∀ {fs : List (Name × SVal)}, tightFieldsB s fs = true ↔ tightFields s fs
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (n, v) :: rest => by
    simp only [tightFieldsB, tightFields, Bool.and_eq_true, SVal.tightFieldsB_iff (fs := rest)]
    cases lookupBy n (structDef s) with
    | none => simp only [true_and]
    | some T => simp only [SVal.tightB_iff (v := v) (T := T)]

theorem SVal.tightElemsB_iff {E : Ty} :
    ∀ {es : List SVal}, tightElemsB E es = true ↔ tightElems E es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | v :: rest => by
    simp only [tightElemsB, tightElems, Bool.and_eq_true, SVal.tightB_iff (v := v),
      SVal.tightElemsB_iff (es := rest)]

theorem SVal.tightEntriesB_iff {V : Ty} :
    ∀ {es : List (Int × SVal)}, tightEntriesB V es = true ↔ tightEntries V es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (_, v) :: rest => by
    simp only [tightEntriesB, tightEntries, Bool.and_eq_true, SVal.tightB_iff (v := v),
      SVal.tightEntriesB_iff (es := rest)]

end

/-- A default of a type whose structs' defaults are well-formed is
canonical: the slot `persons.push()` takes where nothing was popped. -/
theorem defaultForTy_canonB {T : Ty} (h : T.okDeep = true) : (defaultForTy T).canonB T = true :=
  SVal.canonB_iff.2 (defaultForTy_canon (defaultOk_of_defaultOkS (okDeep_defaultOkS h)))

end Solidity
