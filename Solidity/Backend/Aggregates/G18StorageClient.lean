import Solidity.Backend.Aggregates.G18StorageValues
import Solidity.Source.Machine

/-! Inhabited operation-level Source/IR storage correspondence. The source
layout is resolved from actual declarations, not a constant cell-type oracle.
No expression bounds, declaration graph completeness, physical slots, or
whole-program lowering is inferred from these cells. -/
namespace Solidity.Backend.Aggregates.StorageClient
open Lowering.V07

private theorem sevenRange : Source.IntTy.u8.lo ≤ (7 : Int) ∧ (7 : Int) ≤ Source.IntTy.u8.hi := by decide
private theorem eightRange : Source.IntTy.u8.lo ≤ (8 : Int) ∧ (8 : Int) ≤ Source.IntTy.u8.hi := by decide
private theorem elevenRange : Source.IntTy.u8.lo ≤ (11 : Int) ∧ (11 : Int) ≤ Source.IntTy.u8.hi := by decide

/-- A real resolved struct containing a dynamic storage array. -/
def basketDecl : Source.Decl :=
  ⟨.struct, "Basket", none, true,
    .struct "Basket" (.structMember (.array (.elem (.int false 8 Source.IntTy.u8.valid)) .none) "items") .nil⟩
def rootDecl : Source.Decl :=
  ⟨.stateVar, "root", none, true,
    .stateVar (.userType ⟨"Basket", []⟩) none none none false "root" .none⟩
def env : Source.Env := ⟨[basketDecl, rootDecl]⟩
def cell (i : Nat) : Source.SPath := ⟨⟨none,"root"⟩,[.field 0,.index i]⟩
def layout : Source.SPath → Source.STy := fun p => (env.pathTy p).getD .bool

def source : Source.Storage env.layout layout :=
  ((Source.Storage.empty.write (cell 0) (.int 7 sevenRange)).write (cell 1) (.int 11 elevenRange))
def target : SVal (.ref (.struct "Basket")) :=
  .struct (.cons (.array (.cons (.prim (integerValue .u8 7 sevenRange))
    (.cons (.prim (integerValue .u8 11 elevenRange)) .nil)) .nil (by decide)) .nil)
def selected (i : PrimTy.uint.Denote) : Path (.ref (.struct "Basket")) (.prim (integerPrim .u8)) :=
  .field (f := "items") (by decide) (.at i .nil)

theorem initial_first : IntCellAt .u8 source target (cell 0) rfl (selected ⟨0,by decide⟩) := by
  refine ⟨7, sevenRange, rfl, ?_⟩
  simp only [SVal.find_eq_findM, target, selected, SVal.findM, SFields.get_cons,
    ↓reduceDIte, SVec.toList_cons, SVec.toList_nil, SList.toList_nil]
  rfl

theorem initial_other : IntCellAt .u8 source target (cell 1) rfl (selected ⟨1,by decide⟩) := by
  refine ⟨11, elevenRange, rfl, ?_⟩
  simp only [SVal.find_eq_findM, target, selected, SVal.findM, SFields.get_cons,
    ↓reduceDIte, SVec.toList_cons, SVec.toList_nil, SList.toList_nil]
  rfl

theorem selected_apart : Path.Diverges (selected ⟨0,by decide⟩) (selected ⟨1,by decide⟩) := by
  exact .fieldIn (by decide) (.at .nil .nil (by
    intro h
    have e : (0 : Int) = 1 := congrArg Subtype.val h
    omega))

def sourceAfter : Source.Storage env.layout layout := source.write (cell 0) (.int 8 eightRange)
def targetAfter : SVal (.ref (.struct "Basket")) :=
  (target.save (selected ⟨0,by decide⟩) (.prim (integerValue .u8 8 eightRange))).getD target

def observe (s : Source.Storage env.layout layout) (v : SVal (.ref (.struct "Basket"))) :
    List (Option Int) :=
  [(s.read (cell 0)).bind Source.Val.key, (s.read (cell 1)).bind Source.Val.key,
    (v.find (selected ⟨0,by decide⟩)).bind (fun | .prim x => PrimTy.num? x),
    (v.find (selected ⟨1,by decide⟩)).bind (fun | .prim x => PrimTy.num? x)]

/-- The actual target save succeeds; getD's fallback is unreachable. Both
cell relations follow from the NEW operation consumers and inhabited inputs,
not a supplied target run or desired final relation. -/
theorem updated :
    target.save (selected ⟨0,by decide⟩) (.prim (integerValue .u8 8 eightRange)) = some targetAfter ∧
    IntCellAt .u8 sourceAfter targetAfter (cell 0) rfl (selected ⟨0,by decide⟩) ∧
    IntCellAt .u8 sourceAfter targetAfter (cell 1) rfl (selected ⟨1,by decide⟩) := by
  obtain ⟨v,hs,hr⟩ := int_cell_write initial_first 8 eightRange
  have ho := int_cell_write_other (sp := cell 0) (pt := rfl) initial_other
    (by decide) selected_apart 8 eightRange hs
  simpa only [targetAfter, sourceAfter, hs, Option.getD_some] using
    (And.intro hs (And.intro hr ho))

/-- Complete ordered observer for THIS two-cell client: both source cells,
then both target cells, before and after the real writes. -/
theorem ordered_observations :
    observe source target = [some 7,some 11,some 7,some 11] ∧
    observe sourceAfter targetAfter = [some 8,some 11,some 8,some 11] := by
  decide +kernel

/-- info: 'Solidity.Backend.Aggregates.StorageClient.initial_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms initial_first
/-- info: 'Solidity.Backend.Aggregates.StorageClient.initial_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms initial_other
/-- info: 'Solidity.Backend.Aggregates.StorageClient.selected_apart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms selected_apart
/-- info: 'Solidity.Backend.Aggregates.StorageClient.updated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updated
/-- info: 'Solidity.Backend.Aggregates.StorageClient.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_observations
end Solidity.Backend.Aggregates.StorageClient
