import Solidity.Backend.MemoryOps.MixedNestedFootprint
import Solidity.Backend.MemoryOps.CalldataChildExtension
import Solidity.Backend.MemoryOps.MixedCalldataScheduleTransport

/-! Reflection of the existing finite OLD-table observer through preserving
extensions, and application to allocation at the actual decoded intermediate.
Fresh own fields are framed; referenced descendants need not be unchanged. -/
namespace Solidity.Backend.MemoryOps

theorem BoolChildRepr.grow_iff {D : Source.Layout} {H H' : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H} {hp' : Heap H'}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') :
    BoolChildRepr c address hp' s (r.wk e) ↔ BoolChildRepr c address hp s r := by
  constructor
  · intro hr
    refine ⟨hr.1, ?_⟩
    have he := hr.2
    rw [hk r, MObj.elems_wk,
      List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)] at he
    exact he
  · intro hr
    exact hr.grow e hk

theorem RefChildRepr.grow_iff {D : Source.Layout} {H H' : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H} {hp' : Heap H'}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') :
    RefChildRepr c address hp' s (r.wk e) ↔ RefChildRepr c address hp s r := by
  constructor
  · intro hr
    have he : MObj.elems .dyn (hp'.get (r.wk e)) =
        (MObj.elems .dyn (hp.get r)).map (HRef.wk e) := by
      rw [hk r, MObj.elems_wk]
      rfl
    refine ⟨hr.1, ?_, ?_⟩
    · have ht := hr.2.1
      rw [he, decodedChildRefs_wk] at ht
      exact ht
    · intro leaf hl
      apply (BoolChildRepr.grow_iff e hk).mp
      exact hr.2.2 (leaf.wk e) (he ▸ List.mem_map.mpr ⟨leaf,hl,rfl⟩)
  · intro hr
    exact hr.grow e hk

/-- No final relation, uint restoration or stagewise correspondence is assumed.
The allocator and both recapture schedules are the actual existing operations. -/
theorem RefChildRepr.mixed_alloc_iff {D : Source.Layout} {H : HTy} {R Q T : RefTy}
    {old : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D RefChildTy} {root : HRef H RefChildRef}
    (hi : RefChildRepr old address hp sv root)
    (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out)
    (obj : MObj H T) :
    let e := List.prefix_append H [T]
    ∃ ini mid' out', checkedBoolUintSequence c off cu uo hp r a s t d q b u v f=some ini ∧
      runCaptures (ini.alloc obj).1 (r.wk e) a bs=some mid' ∧
      runCaptures mid' (q.wk e) b us=some out' ∧ Heap.Keeps e out out' ∧
      out'.get (ini.alloc obj).2=(ini.alloc obj).1.get (ini.alloc obj).2 ∧
      (RefChildRepr old address out' sv (root.wk e) ↔
        ∀ leaf ∈ MObj.elems .dyn (hp.get root), r.id=leaf.id →
          ∃ pb, calldataBools c off=some pb ∧ ∀ k,
            (replaceSlice (MObj.elems a (hp.get r)) d ((pb.drop s).take (t-s)))[captureOrigin bs k]?=(MObj.elems a (hp.get r))[k]?) := by
  dsimp only
  obtain ⟨ini,mid',out',hinit,hb,hu,hk,hfresh⟩ :=
    checkedMixedCaptures_alloc c off cu uo hp r a s t d q b u v f bs us out ho obj
  exact ⟨ini,mid',out',hinit,hb,hu,hk,hfresh,
    (RefChildRepr.grow_iff _ hk).trans
      (hi.mixed_schedule_iff c off cu uo r a s t d q b u v f bs us out ho)⟩

/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.grow_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.grow_iff
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.grow_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.grow_iff
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.mixed_alloc_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.mixed_alloc_iff
end Solidity.Backend.MemoryOps
