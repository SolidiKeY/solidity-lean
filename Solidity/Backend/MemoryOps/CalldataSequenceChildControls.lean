import Solidity.Backend.MemoryOps.CalldataSequenceChildren
import Solidity.Backend.MemoryOps.CalldataSequenceFixtures

/-! Existing initial Source child tables, runtime-sized repeated aliases and
actual mixed writes. No Source entries are invented for fresh memory objects. -/
namespace Solidity.Backend.MemoryOps.SequenceChildControls
open SequenceFixtures
private abbrev B := BoolChildRef
private abbrev C := RefChildRef
private abbrev N : RefTy := .array (.prim .uint)
private abbrev H : HTy := [B,B,N,C]
private def dst : HRef H B := ⟨0,rfl⟩
private def held : HRef H B := ⟨1,rfl⟩
private def nr : HRef H N := ⟨2,rfl⟩
private def root : HRef H C := ⟨3,rfl⟩
private def address (i : Nat) := 100+i
private def sv : Source.Data D RefChildTy := .val (.cdRef rfl (address root.id))
private def tables (n : Nat) : Source.Calldata D := ⟨[],fun off =>
  if off = 101 then some ⟨BoolChildTy,decodedBools [false,true]⟩ else
  if off = 103 then some ⟨RefChildTy,decodedChildRefs address (List.replicate n held)⟩ else none⟩
private def heap (n : Nat) (hn : n < 2^256) : Heap H :=
  (⟨[false,false],by decide⟩,⟨[false,true],by decide⟩,
   ⟨[zero,zero,zero],by decide⟩,⟨List.replicate n held,by simpa only [List.length_replicate] using hn⟩,())
private theorem leaf_eq (n : Nat) (hn : n < 2^256) (leaf : HRef H B)
    (hl : leaf ∈ MObj.elems .dyn ((heap n hn).get root)) : leaf = held := by
  have hm : leaf ∈ List.replicate n held := by simpa only [MObj.elems_dyn] using hl
  exact (List.mem_replicate.mp hm).2
private theorem initial (n : Nat) (hn : n < 2^256) : RefChildRepr (tables n) address (heap n hn) sv root := by
  refine ⟨rfl,?_,?_⟩
  · simp only [MObj.elems_dyn]; rfl
  · intro leaf hl
    have he := leaf_eq n hn leaf hl
    subst leaf
    refine ⟨rfl,?_⟩
    simp only [MObj.elems_dyn]; rfl
private def bv : List Bool := [true,false]
private def nv : List U := [maximum,one]
private theorem hb (n : Nat) (hn : n < 2^256) : 0+bv.length ≤ (heap n hn).len dst .dyn := by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,dst,held]; decide
private theorem hu (n : Nat) (hn : n < 2^256) : 1+nv.length ≤ (heap n hn).len nr .dyn := by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide
private def out (n : Nat) (hn : n < 2^256) := overwriteTwo (heap n hn) dst .dyn 0 bv (hb n hn) nr .dyn 1 nv (hu n hn) (by decide)
private theorem run (n : Nat) (hn : n < 2^256) : checkedBoolUintSequence (bools bv) 7 (uints nv) 9 (heap n hn) dst .dyn 0 2 0 nr .dyn 0 2 1 = some (out n hn) := by
  have h := checkedBoolUintSequence_checked (bool_repr bv) (uint_repr nv) (heap n hn) dst .dyn 0 2 0 nr .dyn 0 2 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,dst,held]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide)
  simpa only [bool_values,calldataUint_values] using h

theorem runtime_correspondence (n : Nat) (hn : n < 2^256) :
    checkedBoolUintSequence (bools bv) 7 (uints nv) 9 (heap n hn) dst .dyn 0 2 0 nr .dyn 0 2 1 = some (out n hn) ∧
    RefChildRepr (tables n) address (out n hn) sv root := by
  refine ⟨run n hn,(initial n hn).mixedSequence (bools bv) 7 (uints nv) 9 dst .dyn 0 2 0 nr .dyn 0 2 1 (out n hn) (run n hn) ?_⟩
  intro leaf hl
  have he := leaf_eq n hn leaf hl
  subst leaf
  left; decide

private theorem root_frame (n : Nat) (hn : n < 2^256) : (out n hn).get root = (heap n hn).get root :=
  mixedTransfer_frame_or_empty (bools bv) 7 (uints nv) 9 (heap n hn) dst .dyn 0 2 0 nr .dyn 0 2 1 (out n hn) (run n hn) root (Or.inl (by decide)) (Or.inl (by decide))
private theorem leaf_frame (n : Nat) (hn : n < 2^256) : (out n hn).get held = (heap n hn).get held :=
  mixedTransfer_frame_or_empty (bools bv) 7 (uints nv) 9 (heap n hn) dst .dyn 0 2 0 nr .dyn 0 2 1 (out n hn) (run n hn) held (Or.inl (by decide)) (Or.inl (by decide))

/-- Every selected repeated alias has the old identity and final child contents. -/
theorem typed_index (n : Nat) (hn : n < 2^256) (i : U) (hi : i.val.toNat < n) :
    (out n hn).index root .dyn i = some held ∧
    (out n hn).index held .dyn one = some true := by
  constructor
  · change (MObj.elems .dyn ((out n hn).get root))[i.val.toNat]? = some held
    rw [root_frame]
    simp only [MObj.elems_dyn]
    exact List.getElem?_replicate_of_lt hi
  · change (MObj.elems .dyn ((out n hn).get held))[1]? = some true
    rw [leaf_frame]
    simp only [MObj.elems_dyn]; rfl

theorem changed_other_objects (n : Nat) (hn : n < 2^256) :
    MObj.elems .dyn ((out n hn).get dst) = [true,false] ∧
    (MObj.elems .dyn ((out n hn).get nr)).map (fun v : U => v.val) = [0,((2^256-1 : Nat) : Int),1] := by
  constructor
  · rw [out,overwriteTwo_first,overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · rw [out,overwriteTwo,overwriteSlice_elems,overwriteSlice_frame _ dst nr .dyn _ _ _ (by decide)]
    simp only [MObj.elems_dyn]; rfl

private def emptyOut (n : Nat) (hn : n < 2^256) := overwriteSlice (heap n hn) nr .dyn 1 nv (hu n hn)
private theorem emptyRun (n : Nat) (hn : n < 2^256) :
    checkedBoolUintSequence (bools bv) 7 (uints nv) 9 (heap n hn) held .dyn 2 2 2 nr .dyn 0 2 1 = some (emptyOut n hn) := by
  have h := checkedBoolUintSequence_checked (bool_repr bv) (uint_repr nv) (heap n hn) held .dyn 2 2 2 nr .dyn 0 2 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide)
  simpa only [Nat.sub_self,List.take_zero,overwriteTwo,overwriteSlice_empty,calldataUint_values] using h

/-- The aliased Boolean destination is allowed when the captured interval is
empty, including exact end. This is not an alias admission restriction. -/
theorem empty_alias (n : Nat) (hn : n < 2^256) :
    checkedBoolUintSequence (bools bv) 7 (uints nv) 9 (heap n hn) held .dyn 2 2 2 nr .dyn 0 2 1 = some (emptyOut n hn) ∧
    RefChildRepr (tables n) address (emptyOut n hn) sv root := by
  refine ⟨emptyRun n hn,(initial n hn).mixedSequence (bools bv) 7 (uints nv) 9 held .dyn 2 2 2 nr .dyn 0 2 1 (emptyOut n hn) (emptyRun n hn) ?_⟩
  intro leaf _
  right; rfl

private theorem hbad (n : Nat) (hn : n < 2^256) : 0+bv.length ≤ (heap n hn).len held .dyn := by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide
private def bad (n : Nat) (hn : n < 2^256) := overwriteTwo (heap n hn) held .dyn 0 bv (hbad n hn) nr .dyn 1 nv (hu n hn) (by decide)
private theorem badRun (n : Nat) (hn : n < 2^256) :
    checkedBoolUintSequence (bools bv) 7 (uints nv) 9 (heap n hn) held .dyn 0 2 0 nr .dyn 0 2 1 = some (bad n hn) := by
  have h := checkedBoolUintSequence_checked (bool_repr bv) (uint_repr nv) (heap n hn) held .dyn 0 2 0 nr .dyn 0 2 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,heap,held,nr]; decide)
  simpa only [bool_values,calldataUint_values] using h
private theorem bad_root_frame (n : Nat) (hn : n < 2^256) : (bad n hn).get root = (heap n hn).get root :=
  mixedTransfer_frame_or_empty (bools bv) 7 (uints nv) 9 (heap n hn) held .dyn 0 2 0 nr .dyn 0 2 1 (bad n hn) (badRun n hn) root (Or.inl (by decide)) (Or.inl (by decide))
private theorem bad_child (n : Nat) (hn : n < 2^256) : MObj.elems .dyn ((bad n hn).get held) = [true,false] := by
  rw [bad,overwriteTwo_first,overwriteSlice_elems]
  simp only [MObj.elems_dyn]; rfl

/-- Nonempty supported alias mutation can invalidate the initial immutable
child correspondence. No Source shape is excluded to avoid this counterexample. -/
theorem alias_mutation_negative (n : Nat) (hn : n < 2^256) (hpos : 0 < n) :
    checkedBoolUintSequence (bools bv) 7 (uints nv) 9 (heap n hn) held .dyn 0 2 0 nr .dyn 0 2 1 = some (bad n hn) ∧
    ¬ RefChildRepr (tables n) address (bad n hn) sv root := by
  refine ⟨badRun n hn,?_⟩
  intro hr
  have hm : held ∈ MObj.elems .dyn ((bad n hn).get root) := by
    rw [bad_root_frame]
    simp only [MObj.elems_dyn]
    exact List.mem_replicate.mpr ⟨by omega,rfl⟩
  have leaf := hr.2.2 held hm
  have hs : DecodedBoolRead (tables n) (address held.id) 0 true :=
    (leaf.read_iff 0 true).mpr (by rw [bad_child]; rfl)
  have hc : DecodedBoolArray (tables n) (address held.id) [false,true] := rfl
  have h := (decodedBoolRead_iff hc).mp hs
  change (some false : Option Bool) = some true at h
  cases h

/-- With no selected descendants, changing an unobserved child does not refute
this root relation: the footprint premise is vacuous only in this empty case. -/
theorem empty_root_alias : RefChildRepr (tables 0) address (bad 0 (by decide)) sv root := by
  apply (initial 0 (by decide)).mixedSequence (bools bv) 7 (uints nv) 9 held .dyn 0 2 0 nr .dyn 0 2 1 _ (badRun 0 (by decide))
  intro leaf hl
  simp only [MObj.elems_dyn] at hl
  change leaf ∈ ([] : List (HRef H B)) at hl
  cases hl

theorem repeated_and_boundary :
    (out 33 (by decide)).index root .dyn zero = some held ∧
    (out 33 (by decide)).index root .dyn (⟨32,by decide⟩ : U) = some held ∧
    (out 33 (by decide)).index held .dyn one = some true := by
  exact ⟨(typed_index 33 (by decide) zero (by decide)).1,
    (typed_index 33 (by decide) (⟨32,by decide⟩ : U) (by decide)).1,
    (typed_index 33 (by decide) zero (by decide)).2⟩

/-- info: 'Solidity.Backend.MemoryOps.SequenceChildControls.runtime_correspondence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runtime_correspondence
/-- info: 'Solidity.Backend.MemoryOps.SequenceChildControls.typed_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms typed_index
/-- info: 'Solidity.Backend.MemoryOps.SequenceChildControls.changed_other_objects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_other_objects
/-- info: 'Solidity.Backend.MemoryOps.SequenceChildControls.empty_alias' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_alias
/-- info: 'Solidity.Backend.MemoryOps.SequenceChildControls.alias_mutation_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms alias_mutation_negative
/-- info: 'Solidity.Backend.MemoryOps.SequenceChildControls.empty_root_alias' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_root_alias
/-- info: 'Solidity.Backend.MemoryOps.SequenceChildControls.repeated_and_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms repeated_and_boundary
end Solidity.Backend.MemoryOps.SequenceChildControls
