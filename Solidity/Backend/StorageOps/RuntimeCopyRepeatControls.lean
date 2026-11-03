import Solidity.Backend.StorageOps.RuntimeCopyRepeat

/-! Actual current-header runtime copies, including a GOOD-region numeric
source-header interference counterexample. Numeric locations in that control
are not claimed to be a well-typed Source term. No emitted loop or rollback. -/
namespace Solidity.Backend.StorageOps.RuntimeCopyRepeatControls
open Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph NumericCopyCommutation
private def w (n : Fin 256) : Semantics.Word := lengthWord n.val (by have h:=n.isLt; omega)
private def dst : Solidity.Storage.Loc := .root 0
private def src : Solidity.Storage.Loc := .root 1
private def d (i : Nat) : Solidity.Storage.Loc := .data dst i
private def s (i : Nat) : Solidity.Storage.Loc := .data src i
private def hash (p : Pre) : Nat := if p=.data 0 then 16 else 48
private def locations : List Solidity.Storage.Loc := [dst,src,d 0,d 1,d 2,d 3,d 4,d 5,d 6,s 0,s 1,s 2,s 3,s 4,s 5,s 6]
private def initial (old live : Fin 8) : WordStore := fun a =>
 if a=0 then w ⟨old.val,by have h:=old.isLt; omega⟩ else
 if a=1 then w ⟨live.val,by have h:=live.isLt; omega⟩ else
 if a=16 then w 31 else if a=17 then w 37 else if a=18 then w 41 else if a=19 then w 43 else
 if a=20 then w 99 else if a=21 then w 151 else if a=22 then w 157 else
 if a=48 then w 7 else if a=49 then w 17 else if a=50 then w 23 else if a=51 then w 53 else
 if a=52 then w 71 else if a=53 then w 113 else if a=54 then w 127 else w 0
private def copy := NumericTraversal.copy 128 hash dst src
private def view (m : WordStore) : List Nat :=
 [0,1,16,17,18,19,20,21,22,48,49,50,51,52,53,54].map (fun a => (m a).val.toNat)
private theorem run : FiniteRun 128 16 2 hash [.data 0,.data 1] locations := by
 constructor
 · intro p; simp only [hash]; split <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [dst,src,d,s,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem covered : ∀ l ∈ writeSet 128 hash dst src (initial 4 2) ++ (readSet 128 hash dst src (initial 4 2)).tail,l∈locations := by
 intro l member
 change l∈[dst,d 0,d 1,d 2,d 3]++[src,s 0,s 1] at member
 simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl) <;> decide
private theorem separate : ∀ w∈writeSet 128 hash dst src (initial 4 2),∀ r∈(readSet 128 hash dst src (initial 4 2)).tail,w≠r := by decide

/-- Whole-store equality, not just the finite observation vector. -/
theorem shrinking_repeat : copy (copy (initial 4 2))=copy (initial 4 2) :=
 RuntimeCopyRepeat.copy_repeat run dst src (initial 4 2) covered (Or.inr separate)
/-- COMPLETE ordered fixture observations, before/once/twice. -/
theorem shrinking_ordered : (view (initial 4 2),view (copy (initial 4 2)),view (copy (copy (initial 4 2)))) =
 ([4,2,31,37,41,43,99,151,157,7,17,23,53,71,113,127],
  [2,2,7,17,0,0,99,151,157,7,17,23,53,71,113,127],
  [2,2,7,17,0,0,99,151,157,7,17,23,53,71,113,127]) := by decide
/-- Shrinkage is strict; destination header READ VALUE intentionally changes. -/
theorem shrinking_accesses :
 (writeSet 128 hash dst src (initial 4 2),writeSet 128 hash dst src (copy (initial 4 2)),
  (readSet 128 hash dst src (initial 4 2)).tail,(readSet 128 hash dst src (copy (initial 4 2))).tail,
  (initial 4 2 0).val.toNat,(copy (initial 4 2) 0).val.toNat)=
 ([dst,d 0,d 1,d 2,d 3],[dst,d 0,d 1],[src,s 0,s 1],[src,s 0,s 1],4,2) := by decide
/-- Independent actual runtime lengths: growth, empty source and exact alias. -/
theorem other_lengths_ordered :
 (view (initial 1 4),view (copy (initial 1 4)),view (copy (copy (initial 1 4))),
  view (initial 3 0),view (copy (initial 3 0)),view (copy (copy (initial 3 0))),
  view (NumericTraversal.copy 128 hash dst dst (initial 4 2))) =
 ([1,4,31,37,41,43,99,151,157,7,17,23,53,71,113,127],
  [4,4,7,17,23,53,99,151,157,7,17,23,53,71,113,127],
  [4,4,7,17,23,53,99,151,157,7,17,23,53,71,113,127],
  [3,0,31,37,41,43,99,151,157,7,17,23,53,71,113,127],
  [0,0,0,0,0,43,99,151,157,7,17,23,53,71,113,127],
  [0,0,0,0,0,43,99,151,157,7,17,23,53,71,113,127],
  [4,2,31,37,41,43,99,151,157,7,17,23,53,71,113,127]) := by rfl

private def nestedSrc := d 0
private def nestedHash (p : Pre) : Nat := if p=.data 0 then 16 else 48
private def badInitial : WordStore := fun a => if a=0 then w 1 else if a=16 then w 2 else
 if a=17 then w 31 else if a=18 then w 99 else if a=48 then w 7 else if a=49 then w 17 else w 0
private def badCopy := NumericTraversal.copy 128 nestedHash dst nestedSrc
private def badLocations : List Solidity.Storage.Loc := [dst,nestedSrc,d 1,d 2,.data nestedSrc 0,.data nestedSrc 1]
/-- The interference has VALID per-run hash regions, not a collision. -/
theorem interference_regions : FiniteRun 128 16 2 nestedHash [.data 0,.data 16] badLocations := by
 constructor
 · intro p; simp only [nestedHash]; split <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [badLocations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [dst,d,nestedSrc,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [badLocations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
/-- COMPLETE ordered numeric observations: first write clobbers the source
header, the second loop grows and overwrites an older destination shadow. -/
theorem interference_ordered :
 (view badInitial,view (badCopy badInitial),view (badCopy (badCopy badInitial))) =
 ([1,0,2,31,99,0,0,0,0,7,17,0,0,0,0,0],
  [2,0,7,17,99,0,0,0,0,7,17,0,0,0,0,0],
  [7,0,7,17,0,0,0,0,0,7,17,0,0,0,0,0]) := by decide
/-- Refutes unrestricted repetition and second-footprint containment. -/
theorem interference_rejected :
 ¬ (∀ w∈writeSet 128 nestedHash dst nestedSrc badInitial,∀ r∈(readSet 128 nestedHash dst nestedSrc badInitial).tail,w≠r) ∧
 d 2 ∉ writeSet 128 nestedHash dst nestedSrc badInitial ∧
 d 2 ∈ writeSet 128 nestedHash dst nestedSrc (badCopy badInitial) ∧
 badCopy (badCopy badInitial)≠badCopy badInitial := by
 refine ⟨by decide,by decide,by decide,?_⟩
 intro equal
 have headers := congrFun equal 0
 have impossible : w 7=w 2 := headers
 exact (by decide : w 7≠w 2) impossible

/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeatControls.shrinking_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_repeat
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeatControls.shrinking_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_ordered
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeatControls.shrinking_accesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_accesses
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeatControls.other_lengths_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms other_lengths_ordered
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeatControls.interference_regions' depends on axioms: [propext] -/
#guard_msgs in #print axioms interference_regions
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeatControls.interference_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms interference_ordered
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeatControls.interference_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms interference_rejected
end Solidity.Backend.StorageOps.RuntimeCopyRepeatControls
