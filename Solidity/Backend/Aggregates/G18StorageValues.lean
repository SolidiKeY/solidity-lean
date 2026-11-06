import Solidity.Source.State
import Solidity.Semantics.Storage.Ops
import Solidity.Lowering.V07.Scalar

/-! Actual independent Source.Storage cells and intrinsic typed aggregate paths.
These are store-operation consumers; expression bounds, declaration/graph
admission and whole-program lowering remain separate obligations. -/
namespace Solidity.Backend.Aggregates
open Solidity.Lowering.V07

private theorem bind_some_isSome {α β : Type} (o : Option α) (f : α → β) :
    (o.bind (fun x => some (f x))).isSome=o.isSome := by
  cases o <;> rfl

/-- Actual save availability follows from actual find availability, including
struct fields, fixed/dynamic allocated slots and mapping defaults. This does
not assert live-array bounds, which the source evaluator checks separately. -/
theorem save_isSome_eq_find {T U : Ty} (p : Path T U) (v : SVal T) (new : SVal U) :
    (v.save p new).isSome=(v.find p).isSome := by
  rw [SVal.save_eq_saveM,SVal.find_eq_findM]
  induction p with
  | nil => cases v <;> rfl
  | field hf p ih =>
    cases v with
    | struct fs =>
      simp only [SVal.saveM,SVal.findM,Option.bind_eq_bind,bind_some_isSome,ih]
  | «at» i p ih =>
    cases v with
    | array elems shadow bound =>
      simp only [SVal.saveM,SVal.findM]
      split
      · rename_i child hchild
        simp only [Option.bind_eq_bind,bind_some_isSome,ih]
      · rfl
  | atF i p ih =>
    cases v with
    | fixed elems =>
      simp only [SVal.saveM,SVal.findM]
      split
      · rename_i child hchild
        simp only [Option.bind_eq_bind,bind_some_isSome,ih]
      · rfl
  | key k p ih =>
    cases v with
    | map entries default =>
      simp only [SVal.saveM,SVal.findM]
      split
      · rename_i child hchild
        simp only [Option.bind_eq_bind,bind_some_isSome,ih]
      · rename_i hnone
        simp only [Option.bind_eq_bind,bind_some_isSome,ih]

/-- Pointwise value agreement at EXISTING independent Source and intrinsic
storage carriers; no execution or simulation is a field of this relation. -/
def IntCellAt {D : Source.Layout} {L : Source.SPath → Source.STy} {T : Ty}
    (t : Source.IntTy) (source : Source.Storage D L) (target : SVal T)
    (sp : Source.SPath) (typed : L sp=.int t) (tp : Path T (.prim (integerPrim t))) : Prop :=
  ∃ n, ∃ range : t.lo≤n ∧ n≤t.hi,
    source.read sp=some (typed.symm ▸ (Source.Val.int n range)) ∧
    target.find tp=some (.prim (integerValue t n range))

/-- Derive the target save from the actual initial read, then pair it with
actual Source.Storage.write and readback. No desired save/run is assumed. -/
theorem int_cell_write {D : Source.Layout} {L : Source.SPath → Source.STy} {T : Ty}
    {t : Source.IntTy} {source : Source.Storage D L} {target : SVal T}
    {sp : Source.SPath} {typed : L sp=.int t} {tp : Path T (.prim (integerPrim t))}
    (related : IntCellAt t source target sp typed tp) (n : Int)
    (range : t.lo≤n ∧ n≤t.hi) :
    ∃ target', target.save tp (.prim (integerValue t n range))=some target' ∧
      IntCellAt t (source.write sp (typed.symm ▸ Source.Val.int n range)) target' sp typed tp := by
  obtain ⟨old,oldRange,hs,ht⟩ := related
  have available : (target.save tp (.prim (integerValue t n range))).isSome=true := by
    rw [save_isSome_eq_find,ht]
    rfl
  let target' := (target.save tp (.prim (integerValue t n range))).get available
  have saved : target.save tp (.prim (integerValue t n range))=some target' :=
    (Option.some_get available).symm
  exact ⟨target',saved,n,range,Source.Storage.write_read _ _ _,SVal.find_save_same _ _ _ saved⟩

/-- Disjoint source cells AND actual diverging intrinsic paths retain the
old pointwise relation. Equality of one side alone is insufficient. -/
theorem int_cell_write_other {D : Source.Layout} {L : Source.SPath → Source.STy} {T : Ty}
    {t u : Source.IntTy} {source : Source.Storage D L} {target target' : SVal T}
    {sp sq : Source.SPath} {pt : L sp=.int t} {qt : L sq=.int u}
    {tp : Path T (.prim (integerPrim t))} {tq : Path T (.prim (integerPrim u))}
    (related : IntCellAt u source target sq qt tq) (different : sq≠sp)
    (diverges : Path.Diverges tp tq) (n : Int) (range : t.lo≤n ∧ n≤t.hi)
    (saved : target.save tp (.prim (integerValue t n range))=some target') :
    IntCellAt u (source.write sp (pt.symm ▸ Source.Val.int n range)) target' sq qt tq := by
  obtain ⟨old,oldRange,hs,ht⟩ := related
  refine ⟨old,oldRange,?_,?_⟩
  · rw [Source.Storage.write_other _ different]
    exact hs
  · rw [SVal.find_eq_findM]
    rw [SVal.save_eq_saveM] at saved
    rw [SVal.findM_saveM_diverges diverges target _ saved,← SVal.find_eq_findM]
    exact ht
/-- info: 'Solidity.Backend.Aggregates.save_isSome_eq_find' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms save_isSome_eq_find

/-- info: 'Solidity.Backend.Aggregates.int_cell_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_cell_write

/-- info: 'Solidity.Backend.Aggregates.int_cell_write_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms int_cell_write_other
end Solidity.Backend.Aggregates
