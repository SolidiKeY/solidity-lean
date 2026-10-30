import Solidity.Backend.MemoryOps.CalldataSequenceFixtures

/-! Inhabited actual decoded sequence controls. Overlap is supported and produces
second-write precedence; failures are Option results, not rollback/Source halts. -/
namespace Solidity.Backend.MemoryOps.SequenceControls
open SequenceFixtures
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B,P]
private def r : HRef H B := ⟨0,rfl⟩
private def parent : HRef H P := ⟨1,rfl⟩
private def hp : Heap H := (⟨List.replicate 6 false,by decide⟩,⟨[r,r],rfl⟩,())
private def A : List Bool := [true,false,true]
private def Bv : List Bool := [true,true,false]
private theorem ha : 1+A.length ≤ hp.len r .dyn := by simp only [Heap.len,MObj.elems_dyn]; decide
private theorem hb : 2+Bv.length ≤ hp.len r .dyn := by simp only [Heap.len,MObj.elems_dyn]; decide
private def mid := overwriteSlice hp r .dyn 1 A ha
private def out := overwriteIntervals hp r .dyn 1 A ha 2 Bv hb
private theorem first : checkedCalldataBools (bools A) 7 hp r .dyn 0 3 1 = some mid := by
  have h := checkedCalldataBools_some (bool_repr A) hp r .dyn 0 3 1
    (show SliceBounds A.length 0 3 from ⟨by decide,by decide⟩)
    (by simp only [Heap.len,MObj.elems_dyn]; decide)
  simpa only [bool_values] using h
private theorem run : checkedBoolSequence (bools A) 7 (bools Bv) 7 hp r .dyn 0 3 1 r .dyn 0 3 2 = some out := by
  have h := checkedBoolSequence_same_checked (bool_repr A) (bool_repr Bv) hp r .dyn 0 3 1 0 3 2
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
  simpa only [bool_values] using h

theorem ordered : checkedCalldataBools (bools A) 7 hp r .dyn 0 3 1 = some mid ∧
    checkedBoolSequence (bools A) 7 (bools Bv) 7 hp r .dyn 0 3 1 r .dyn 0 3 2 = some out ∧
    MObj.elems .dyn (out.get r) = [false,true,true,true,false,false] := by
  refine ⟨first,run,?_⟩
  rw [out,overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems]
  simp only [MObj.elems_dyn]
  rfl

theorem source_observations :
    (∃ z, (MObj.elems .dyn (out.get r))[2]? = some z ∧
      DecodedArrayRead (bools Bv) 7 .bool none 0 (.val (.bool z))) ∧
    (∃ z, (MObj.elems .dyn (out.get r))[1]? = some z ∧
      DecodedArrayRead (bools A) 7 .bool none 0 (.val (.bool z))) :=
  ⟨checkedBoolSequence_second_read (bool_repr Bv) hp r .dyn 0 3 1 r .dyn 0 3 2 out run 0 (by decide),
    checkedBoolSequence_first_exterior (bool_repr A) (bool_repr Bv) hp r .dyn 0 3 1 0 3 2 out run 0 (by decide) (by decide)⟩

private theorem reverseCap : 1+A.length ≤ hp.len r .dyn := ha
private def reverseOut := overwriteIntervals hp r .dyn 2 Bv hb 1 A reverseCap
private theorem reverseRun : checkedBoolSequence (bools Bv) 7 (bools A) 7 hp r .dyn 0 3 2 r .dyn 0 3 1 = some reverseOut := by
  have h := checkedBoolSequence_same_checked (bool_repr Bv) (bool_repr A) hp r .dyn 0 3 2 0 3 1
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
  simpa only [bool_values] using h

theorem precedence_negative :
    checkedBoolSequence (bools Bv) 7 (bools A) 7 hp r .dyn 0 3 2 r .dyn 0 3 1 = some reverseOut ∧
    MObj.elems .dyn (reverseOut.get r) = [false,true,false,true,false,false] ∧ out ≠ reverseOut := by
  refine ⟨reverseRun,?_,?_⟩
  · rw [reverseOut,overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · intro he
    have h := congrArg (fun h : Heap H => MObj.elems .dyn (h.get r)) he
    dsimp only at h
    rw [ordered.2.2] at h
    rw [reverseOut,overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems] at h
    simp only [MObj.elems_dyn] at h
    cases h

theorem ignored_or_stale_negative :
    MObj.elems .dyn (out.get r) ≠ [false,false,true,true,false,false] ∧
    MObj.elems .dyn (out.get r) ≠ [false,true,true,false,true,false] := by
  rw [ordered.2.2]
  constructor <;> intro h <;> cases h

theorem parent_frame : out.get parent = hp.get parent :=
  checkedBoolSequence_frame (bool_repr A) (bool_repr Bv) hp r .dyn 0 3 1 r .dyn 0 3 2 out run parent (by decide) (by decide)

/-- Touching destinations commute, with complete nonuniform outputs. -/
theorem touching_comm : ∃ result,
    checkedBoolSequence (bools A) 7 (bools Bv) 7 hp r .dyn 0 3 0 r .dyn 0 3 3 = some result ∧
    checkedBoolSequence (bools Bv) 7 (bools A) 7 hp r .dyn 0 3 3 r .dyn 0 3 0 = some result ∧
    MObj.elems .dyn (result.get r) = [true,false,true,true,true,false] := by
  have hf := checkedBoolSequence_same_checked (bool_repr A) (bool_repr Bv) hp r .dyn 0 3 0 0 3 3
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
  have hc := checkedBoolSequence_same_comm (bool_repr A) (bool_repr Bv) hp r .dyn 0 3 0 0 3 3
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    (Or.inr (Or.inr (Or.inl (by decide))))
  refine ⟨_,hf,hc.symm.trans hf,?_⟩
  rw [overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems,bool_values,bool_values]
  simp only [MObj.elems_dyn]; rfl

private theorem empty_run (values : List Bool) (k : Nat) (hk : k ≤ values.length) :
    checkedCalldataBools (bools values) 7 hp r .dyn k k 6 = some hp := by
  have h := checkedCalldataBools_some (bool_repr values) hp r .dyn k k 6 ⟨Nat.le_refl _,hk⟩
    (by simp only [Nat.sub_self,Nat.add_zero,Heap.len,MObj.elems_dyn]; decide)
  simpa only [Nat.sub_self,List.take_zero,overwriteSlice_empty] using h

theorem empty_end : checkedBoolSequence (bools []) 7 (bools A) 7 hp r .dyn 0 0 6 r .dyn 3 3 6 = some hp := by
  unfold checkedBoolSequence
  rw [empty_run [] 0 (by decide)]
  exact empty_run A 3 (by decide)

/-- A valid first write reaches mid, then each independent second guard fails. -/
theorem second_failures : checkedCalldataBools (bools A) 7 hp r .dyn 0 3 1 = some mid ∧
    checkedCalldataBools (bools Bv) 7 mid r .dyn 3 1 0 = none ∧
    checkedCalldataBools (bools Bv) 7 mid r .dyn 0 4 0 = none ∧
    checkedBoolSequence (bools A) 7 (bools Bv) 7 hp r .dyn 0 3 1 r .dyn 0 3 5 = none := by
  refine ⟨first,?_,?_,?_⟩
  · exact (checkedCalldataBools_none_iff (bool_repr Bv) mid r .dyn 3 1 0).mpr (Or.inl (by decide))
  · exact (checkedCalldataBools_none_iff (bool_repr Bv) mid r .dyn 0 4 0).mpr (Or.inr (Or.inl (by decide)))
  · unfold checkedBoolSequence
    rw [first]
    apply (checkedCalldataBools_none_iff (bool_repr Bv) mid r .dyn 0 3 5).mpr
    right; right
    rw [boolTransfer_all_len (bools A) 7 hp r .dyn 0 3 1 mid first r .dyn]
    simp only [Heap.len,MObj.elems_dyn]; decide

private def unsupported : Source.Calldata D := ⟨[],fun _ => some ⟨.bytes .calldata,.bytes [1]⟩⟩
theorem missing_order :
    checkedBoolSequence (bools A) 8 unsupported 7 hp r .dyn 0 3 1 r .dyn 0 3 2 = none ∧
    checkedCalldataBools (bools A) 7 hp r .dyn 0 3 1 = some mid ∧
    checkedBoolSequence (bools A) 7 unsupported 7 hp r .dyn 0 3 1 r .dyn 0 3 2 = none ∧
    checkedBoolSequence (bools A) 7 (bools Bv) 8 hp r .dyn 0 3 1 r .dyn 0 3 2 = none := by
  refine ⟨rfl,first,?_,?_⟩
  all_goals unfold checkedBoolSequence; rw [first]; rfl

private def boundaryHp : Heap [B] := (⟨List.replicate 36 false,by decide⟩,())
private def boundaryR : HRef [B] B := ⟨0,rfl⟩
theorem element_boundary : ∃ result,
    checkedBoolSequence (bools A) 7 (bools Bv) 7 boundaryHp boundaryR .dyn 0 3 31 boundaryR .dyn 0 3 32 = some result ∧
    MObj.elems .dyn (result.get boundaryR) = List.replicate 31 false ++ [true,true,true,false,false] := by
  have h := checkedBoolSequence_same_checked (bool_repr A) (bool_repr Bv) boundaryHp boundaryR .dyn 0 3 31 0 3 32
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
  refine ⟨_,h,?_⟩
  rw [overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems,bool_values,bool_values]
  simp only [MObj.elems_dyn]; rfl

/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.source_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms source_observations
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.precedence_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms precedence_negative
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.ignored_or_stale_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ignored_or_stale_negative
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.parent_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms parent_frame
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.touching_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms touching_comm
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.second_failures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms second_failures
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.missing_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms missing_order
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.element_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms element_boundary
/-- Passing the first decoded table again really differs from consuming the
second table. This is an executed stale-source substitution negative. -/
theorem stale_source_call : ∃ bad,
    checkedBoolSequence (bools A) 7 (bools A) 7 hp r .dyn 0 3 1 r .dyn 0 3 2 = some bad ∧
    MObj.elems .dyn (bad.get r) = [false,true,true,false,true,false] ∧ out ≠ bad := by
  have hs := checkedBoolSequence_same_checked (bool_repr A) (bool_repr A) hp r .dyn 0 3 1 0 3 2
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
  refine ⟨_,hs,?_,?_⟩
  · rw [overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems,bool_values]
    simp only [MObj.elems_dyn]; rfl
  · intro he
    have h := congrArg (fun h : Heap H => MObj.elems .dyn (h.get r)) he
    dsimp only at h
    rw [ordered.2.2,overwriteIntervals,overwriteSlice_elems,overwriteSlice_elems,bool_values] at h
    simp only [MObj.elems_dyn] at h
    cases h

theorem first_failures :
    checkedBoolSequence (bools A) 7 (bools Bv) 7 hp r .dyn 3 1 0 r .dyn 0 3 2 = none ∧
    checkedBoolSequence (bools A) 7 (bools Bv) 7 hp r .dyn 0 4 0 r .dyn 0 3 2 = none ∧
    checkedBoolSequence (bools A) 7 (bools Bv) 7 hp r .dyn 0 3 5 r .dyn 0 3 2 = none ∧
    checkedBoolSequence unsupported 7 (bools Bv) 7 hp r .dyn 0 3 1 r .dyn 0 3 2 = none := by
  refine ⟨?_,?_,?_,rfl⟩
  · apply (checkedBoolSequence_none_iff (bools A) 7 (bools Bv) 7 hp r .dyn 3 1 0 r .dyn 0 3 2).mpr
    left
    exact (checkedCalldataBools_none_iff (bool_repr A) hp r .dyn 3 1 0).mpr (Or.inl (by decide))
  · apply (checkedBoolSequence_none_iff (bools A) 7 (bools Bv) 7 hp r .dyn 0 4 0 r .dyn 0 3 2).mpr
    left
    exact (checkedCalldataBools_none_iff (bool_repr A) hp r .dyn 0 4 0).mpr (Or.inr (Or.inl (by decide)))
  · apply (checkedBoolSequence_none_iff (bools A) 7 (bools Bv) 7 hp r .dyn 0 3 5 r .dyn 0 3 2).mpr
    left
    apply (checkedCalldataBools_none_iff (bool_repr A) hp r .dyn 0 3 5).mpr
    right; right
    simp only [Heap.len,MObj.elems_dyn]; decide

/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.stale_source_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stale_source_call
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.first_failures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms first_failures
private def twoHp : Heap [B,B] := (⟨List.replicate 3 false,by decide⟩,⟨List.replicate 3 false,by decide⟩,())
private def ra : HRef [B,B] B := ⟨0,rfl⟩
private def rb : HRef [B,B] B := ⟨1,rfl⟩
theorem different_objects : ∃ result,
    checkedBoolSequence (bools A) 7 (bools Bv) 7 twoHp ra .dyn 0 3 0 rb .dyn 0 3 0 = some result ∧
    checkedBoolSequence (bools Bv) 7 (bools A) 7 twoHp rb .dyn 0 3 0 ra .dyn 0 3 0 = some result ∧
    MObj.elems .dyn (result.get ra) = A ∧ MObj.elems .dyn (result.get rb) = Bv := by
  have hf := checkedBoolSequence_other_checked (bool_repr A) (bool_repr Bv) twoHp ra .dyn 0 3 0 rb .dyn 0 3 0
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide) (by decide)
  have hc := checkedBoolSequence_other_comm (bool_repr A) (bool_repr Bv) twoHp ra .dyn 0 3 0 rb .dyn 0 3 0
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide)
    ⟨by decide,by decide⟩ (by simp only [Heap.len,MObj.elems_dyn]; decide) (by decide)
  refine ⟨_,hf,hc.symm.trans hf,?_,?_⟩
  · rw [overwriteTwo_first,overwriteSlice_elems,bool_values]
    simp only [MObj.elems_dyn]; rfl
  · rw [overwriteTwo,overwriteSlice_elems,overwriteSlice_frame _ ra rb .dyn _ _ _ (by decide),bool_values]
    simp only [MObj.elems_dyn]; rfl
/-- info: 'Solidity.Backend.MemoryOps.SequenceControls.different_objects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms different_objects
end Solidity.Backend.MemoryOps.SequenceControls
