import Solidity.Backend.MemoryOps.MixedChildFootprint
import Solidity.Backend.MemoryOps.CalldataSequenceChildren

/-! Existing nested observer transported through ACTUAL mixed recapture runs.
Only actually selected aliases need the INITIAL Boolean footprint. There is no
new graph semantics, pairwise/global injectivity or Uint-restoration premise. -/
namespace Solidity.Backend.MemoryOps
section
variable {D : Source.Layout} {H : HTy} {R Q : RefTy}
variable (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
variable (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
variable (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
variable (bs us : List SnapshotArgs) (out : Heap H)
variable (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out)

include ho in
theorem checkedMixedCaptures_ref_root_frame (root : HRef H RefChildRef) : out.get root=hp.get root :=
  checkedMixedCaptures_frame c off cu uo hp r a s t d q b u v f bs us out ho root
    (primitiveTransfer_ref_root_ne r a root) (primitiveTransfer_ref_root_ne q b root)
end

theorem RefChildRepr.mixed_schedule_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    {old : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D RefChildTy} {root : HRef H RefChildRef}
    (hi : RefChildRepr old address hp sv root)
    (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out) :
    RefChildRepr old address out sv root ↔
      ∀ leaf ∈ MObj.elems .dyn (hp.get root), r.id=leaf.id →
        ∃ pb, calldataBools c off=some pb ∧ ∀ k,
          (replaceSlice (MObj.elems a (hp.get r)) d ((pb.drop s).take (t-s)))[captureOrigin bs k]?=(MObj.elems a (hp.get r))[k]? := by
  have hf := checkedMixedCaptures_ref_root_frame c off cu uo hp r a s t d q b u v f bs us out ho root
  constructor
  · intro hpost leaf hmem he
    have hmem' : leaf ∈ MObj.elems .dyn (out.get root) := by rw [hf]; exact hmem
    have hleaf : out.get leaf=hp.get leaf := ((hi.2.2 leaf hmem).at_heap_iff out).mp (hpost.2.2 leaf hmem')
    obtain ⟨rfl,hEq⟩ := HRef.heq_of_id r leaf he
    cases hEq
    exact (checkedMixedCaptures_bool_restore c off cu uo hp _ a s t d q b u v f bs us out ho).mp hleaf
  · intro ha
    refine ⟨hi.1,?_,?_⟩
    · rw [hf]; exact hi.2.1
    · intro leaf hmem
      rw [hf] at hmem
      apply ((hi.2.2 leaf hmem).at_heap_iff out).mpr
      by_cases he : r.id=leaf.id
      · have hr := (checkedMixedCaptures_bool_restore c off cu uo hp r a s t d q b u v f bs us out ho).mpr (ha leaf hmem he)
        obtain ⟨rfl,hEq⟩ := HRef.heq_of_id r leaf he
        cases hEq
        exact hr
      · exact checkedMixedCaptures_frame c off cu uo hp r a s t d q b u v f bs us out ho leaf he
          (bool_uint_transfer_ne leaf .dyn q b).symm

/-- Existing typed two-level indexing observes the transported OLD table.
Outer bounds are on the ORIGINAL heap and derived unchanged at actual output. -/
theorem RefChildRepr.mixed_schedule_index_bool {D : Source.Layout} {H : HTy} {R Q : RefTy}
    {old : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D RefChildTy} {root : HRef H RefChildRef}
    (hi : RefChildRepr old address hp sv root)
    (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out)
    (ha : ∀ leaf ∈ MObj.elems .dyn (hp.get root), r.id=leaf.id →
      ∃ pb, calldataBools c off=some pb ∧ ∀ k,
        (replaceSlice (MObj.elems a (hp.get r)) d ((pb.drop s).take (t-s)))[captureOrigin bs k]?=(MObj.elems a (hp.get r))[k]?)
    (i : PrimTy.uint.Denote) (hidx : i.1.toNat < hp.len root .dyn) (j : PrimTy.uint.Denote) (value : Bool) :
    ∃ leaf, out.index root .dyn i=some leaf ∧
      DecodedArrayRead old (address root.id) BoolChildTy none i.1.toNat (.val (.cdRef rfl (address leaf.id))) ∧
      (DecodedBoolRead old (address leaf.id) j.1.toNat value ↔ out.index leaf .dyn j=some value) := by
  have hpost := (hi.mixed_schedule_iff c off cu uo r a s t d q b u v f bs us out ho).mpr ha
  exact hpost.index_bool i (by rw [checkedMixedCaptures_all_len c off cu uo hp r a s t d q b u v f bs us out ho root .dyn]; exact hidx) j value
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_ref_root_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_ref_root_frame
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.mixed_schedule_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.mixed_schedule_iff
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.mixed_schedule_index_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.mixed_schedule_index_bool
end Solidity.Backend.MemoryOps
