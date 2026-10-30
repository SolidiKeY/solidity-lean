import Solidity.Backend.MemoryOps.CalldataSequenceControls

/-! Actual mixed typed transfers, maximum-value checks, fixed overlap and real
allocator composition. All observations are intrinsic; no ABI/target encoding. -/
namespace Solidity.Backend.MemoryOps.MixedSequenceControls
open SequenceFixtures
private abbrev B : RefTy := .array (.prim .bool)
private abbrev N : RefTy := .array (.prim .uint)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B,N,P]
private def br : HRef H B := ⟨0,rfl⟩
private def nr : HRef H N := ⟨1,rfl⟩
private def parent : HRef H P := ⟨2,rfl⟩
private def hp : Heap H := (⟨List.replicate 4 false,by decide⟩,
  ⟨List.replicate 4 zero,by decide⟩,⟨[br,br],rfl⟩,())
private def bv : List Bool := [true,false,true]
private def nv : List U := [maximum,seven,one]
private theorem hb : 0+bv.length ≤ hp.len br .dyn := by simp only [Heap.len,MObj.elems_dyn]; decide
private theorem hn : 1+nv.length ≤ hp.len nr .dyn := by simp only [Heap.len,MObj.elems_dyn]; decide
private def mid := overwriteSlice hp br .dyn 0 bv hb
private def out := overwriteTwo hp br .dyn 0 bv hb nr .dyn 1 nv hn (by decide)
private theorem first : checkedCalldataBools (bools bv) 7 hp br .dyn 0 3 0 = some mid := by
  have h := checkedCalldataBools_some (bool_repr bv) hp br .dyn 0 3 0 ⟨by decide,by decide⟩
    (by simp only [Heap.len,MObj.elems_dyn]; decide)
  simpa only [bool_values] using h
private theorem run : checkedBoolUintSequence (bools bv) 7 (uints nv) 9 hp br .dyn 0 3 0 nr .dyn 0 3 1 = some out := by
  have h := checkedBoolUintSequence_checked (bool_repr bv) (uint_repr nv) hp br .dyn 0 3 0 nr .dyn 0 3 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
  simpa only [bool_values,calldataUint_values] using h

theorem ordered : checkedBoolUintSequence (bools bv) 7 (uints nv) 9 hp br .dyn 0 3 0 nr .dyn 0 3 1 = some out ∧
    MObj.elems .dyn (out.get br) = [true,false,true,false] ∧
    (MObj.elems .dyn (out.get nr)).map (fun v : U => v.val) = [0,((2^256-1 : Nat) : Int),7,1] := by
  have h := checkedBoolUintSequence_elems (bool_repr bv) (uint_repr nv) hp br .dyn 0 3 0 nr .dyn 0 3 1 out run
  refine ⟨run,?_,?_⟩
  · simpa only [bool_values,MObj.elems_dyn] using h.1
  · have hv := congrArg (List.map (fun v : U => v.val)) h.2
    simpa only [calldataUint_values,MObj.elems_dyn] using hv

theorem distinct_comm : br.id ≠ nr.id ∧
    checkedUintBoolSequence (uints nv) 9 (bools bv) 7 hp nr .dyn 0 3 1 br .dyn 0 3 0 = some out := by
  refine ⟨bool_uint_transfer_ne br .dyn nr .dyn,?_⟩
  have h := checkedBoolUintSequence_comm (bool_repr bv) (uint_repr nv) hp br .dyn 0 3 0 nr .dyn 0 3 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
  exact h.symm.trans run

theorem framed_parent_changed_child : out.get parent = hp.get parent ∧
    (MObj.elems .fixed (out.get parent)).map HRef.id = [0,0] ∧ out.get br ≠ hp.get br := by
  have hf := checkedBoolUintSequence_frame (bool_repr bv) (uint_repr nv) hp br .dyn 0 3 0 nr .dyn 0 3 1 out run parent (by decide) (by decide)
  refine ⟨hf,?_,?_⟩
  · rw [hf]; simp only [MObj.elems_fixed]; rfl
  · intro he
    have h := congrArg (MObj.elems .dyn) he
    rw [ordered.2.1] at h
    simp only [MObj.elems_dyn] at h
    cases h

theorem no_truncation_or_substitution :
    (MObj.elems .dyn (out.get nr)).map (fun v : U => v.val) ≠ [0,255,7,1] ∧
    (MObj.elems .dyn (out.get nr)).map (fun v : U => v.val) ≠ [0,7,((2^256-1 : Nat) : Int),1] := by
  rw [ordered.2.2]
  constructor <;> decide

theorem allocator_composition :
    let obj : MObj H P := ⟨[br,br],rfl⟩
    let g := hp.alloc obj
    let e := List.prefix_append H [P]
    ∃ result, checkedBoolUintSequence (bools bv) 7 (uints nv) 9 g.1 (br.wk e) .dyn 0 3 0 (nr.wk e) .dyn 0 3 1 = some result ∧
      Heap.Keeps e out result ∧ result.get g.2 = g.1.get g.2 ∧
      (MObj.elems .dyn (result.get (nr.wk e))).map (fun v : U => v.val) = [0,((2^256-1 : Nat) : Int),7,1] ∧
      MObj.elems .dyn (result.get (br.wk e)) = [true,false,true,false] := by
  dsimp only
  let obj : MObj H P := ⟨[br,br],rfl⟩
  let e := List.prefix_append H [P]
  obtain ⟨result,ho,hk⟩ := checkedBoolUintSequence_keeps (bool_repr bv) (uint_repr nv) e (Heap.keeps_alloc hp obj) br .dyn 0 3 0 nr .dyn 0 3 1 out run
  refine ⟨result,ho,hk,checkedBoolUintSequence_frame (bool_repr bv) (uint_repr nv) _ (br.wk e) .dyn 0 3 0 (nr.wk e) .dyn 0 3 1 result ho (hp.alloc obj).2 (by decide) (by decide),?_,?_⟩
  · rw [hk nr,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
    exact ordered.2.2
  · rw [hk br,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    exact ordered.2.1

theorem second_failures : checkedCalldataBools (bools bv) 7 hp br .dyn 0 3 0 = some mid ∧
    checkedCalldataUints (uints nv) 9 mid nr .dyn 3 1 0 = none ∧
    checkedCalldataUints (uints nv) 9 mid nr .dyn 0 4 0 = none ∧
    checkedBoolUintSequence (bools bv) 7 (uints nv) 9 hp br .dyn 0 3 0 nr .dyn 0 3 2 = none := by
  refine ⟨first,?_,?_,?_⟩
  · exact (checkedCalldataUints_none_iff (uint_repr nv) mid nr .dyn 3 1 0).mpr (Or.inl (by decide))
  · exact (checkedCalldataUints_none_iff (uint_repr nv) mid nr .dyn 0 4 0).mpr (Or.inr (Or.inl (by decide)))
  · unfold checkedBoolUintSequence
    rw [first]
    apply (checkedCalldataUints_none_iff (uint_repr nv) mid nr .dyn 0 3 2).mpr
    right; right
    rw [boolTransfer_all_len (bools bv) 7 hp br .dyn 0 3 0 mid first nr .dyn]
    simp only [Heap.len,MObj.elems_dyn]; decide

theorem rejection_growth :
    let obj : MObj H P := ⟨[br,br],rfl⟩
    let g := hp.alloc obj
    let e := List.prefix_append H [P]
    checkedBoolUintSequence (bools bv) 7 (uints nv) 9 g.1 (br.wk e) .dyn 0 3 0 (nr.wk e) .dyn 0 3 2 = none := by
  dsimp only
  exact (checkedBoolUintSequence_none_keeps (bools bv) 7 (uints nv) 9
    (List.prefix_append H [P]) (Heap.keeps_alloc (R := P) hp (⟨[br,br],rfl⟩ : MObj H P)) br .dyn 0 3 0 nr .dyn 0 3 2).mpr second_failures.2.2.2

private abbrev F : RefTy := .fixed (.prim .uint) 6
private def fixedR : HRef [F] F := ⟨0,rfl⟩
private def fixedHp : Heap [F] := (⟨[zero,zero,zero,zero,zero,zero],rfl⟩,())
private def ua : List U := [maximum,seven]
private def ub : List U := [one,zero]
theorem fixed_overlap : ∃ result,
    checkedUintSequence (uints ua) 9 (uints ub) 9 fixedHp fixedR .fixed 0 2 1 fixedR .fixed 0 2 2 = some result ∧
    (MObj.elems .fixed (result.get fixedR)).map (fun v : U => v.val) = [0,((2^256-1 : Nat) : Int),1,0,0,0] := by
  have h := checkedUintSequence_same_checked (uint_repr ua) (uint_repr ub) fixedHp fixedR .fixed 0 2 1 0 2 2
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_fixed]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_fixed]; decide)
  refine ⟨_,h,?_⟩
  rw [overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems,calldataUint_values,calldataUint_values]
  simp only [MObj.elems_fixed]; rfl

/-- Arbitrary runtime source lengths; only actual existing destination capacity
is required. These are real table-derived operations, not supplied payloads. -/
theorem runtime (aValues bValues : List U) {K : HTy} {R : RefTy}
    (heap : Heap K) (r : HRef K R) (a : ArrTy R (.prim .uint)) (d f : Nat)
    (ha : d+aValues.length ≤ heap.len r a) (hb : f+bValues.length ≤ heap.len r a) :
    ∃ result, checkedUintSequence (uints aValues) 9 (uints bValues) 9 heap r a 0 aValues.length d r a 0 bValues.length f = some result := by
  exact ⟨_,checkedUintSequence_same_checked (uint_repr aValues) (uint_repr bValues) heap r a 0 aValues.length d 0 bValues.length f
    ⟨Nat.zero_le _,Nat.le_refl _⟩ (by simpa only [Nat.sub_zero] using ha)
    ⟨Nat.zero_le _,Nat.le_refl _⟩ (by simpa only [Nat.sub_zero] using hb)⟩

/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.distinct_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms distinct_comm
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.framed_parent_changed_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms framed_parent_changed_child
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.no_truncation_or_substitution' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms no_truncation_or_substitution
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.allocator_composition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocator_composition
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.second_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_failures
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.rejection_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rejection_growth
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.fixed_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixed_overlap
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runtime
theorem immutable_sources :
    (∃ z, (MObj.elems .dyn (out.get br))[0]? = some z ∧
      DecodedArrayRead (bools bv) 7 .bool none 0 (.val (.bool z))) ∧
    (∃ z, (MObj.elems .dyn (out.get nr))[1]? = some z ∧
      DecodedArrayRead (uints nv) 9 (.int .u256) none 0 (.val (sourceUint z))) := by
  obtain ⟨reached,hf,hs⟩ := (checkedBoolUintSequence_some_iff (bools bv) 7 (uints nv) 9 hp br .dyn 0 3 0 nr .dyn 0 3 1 out).mp run
  constructor
  · obtain ⟨z,hm,hz⟩ := checkedCalldataBools_read (bool_repr bv) hp br .dyn 0 3 0 reached hf 0 (by decide)
    refine ⟨z,?_,hz⟩
    rw [checkedCalldataUints_frame (uint_repr nv) reached nr .dyn 0 3 1 out hs br (by decide)]
    exact hm
  · exact checkedCalldataUints_read (uint_repr nv) reached nr .dyn 0 3 1 out hs 0 (by decide)
/-- info: 'Solidity.Backend.MemoryOps.MixedSequenceControls.immutable_sources' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms immutable_sources
end Solidity.Backend.MemoryOps.MixedSequenceControls
