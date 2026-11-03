import Solidity.Lowering.StorageOps.SourceBoolStorageCopy
import Solidity.Lowering.StorageOps.SourceCopyReadbacks

/-! Canonical Source boolean payload and false-default copy readbacks.
Header words retain existing uint implementation. Boolean cells/payloads stay
intrinsic booleans, never arbitrary uint words or a changed source profile. -/
namespace Solidity.Backend.StorageOps.SourceBoolCopyReadbacks
open SourceBoolStorageCopy SourceCopyReadbacks SourceArrayDeleteTarget

theorem bool_word {D : Source.Layout} (b : Bool) :
 (Source.Val.bool (D:=D) b).word.map Fin.val=some (if b then 1 else 0) := by cases b <;> rfl

/-- Actual clear reads the environment's boolean default FALSE. -/
theorem clear_word_false {E : Source.Env} (frame : Source.Fr)
 (state : Source.ExecState E.layout E.lay E.lay) (query : Source.SPath)
 (ordinary : E.transientRoot query=false) (typed : E.cellTy query=.bool) :
 wordAt frame (state.apply (SourceScalarDeleteLog.clearOp E frame query)) query=some 0 := by
 unfold wordAt SourceScalarDeleteLog.clearOp
 simp only [ordinary,Bool.false_eq_true,if_false,Source.ExecState.apply,Source.World.set_get,Source.Storage.read,Source.Storage.set,dif_pos]
 change ((Source.Val.default E.layout (E.cellTy query)).bind Source.Val.word).map Fin.val=some 0
 rw [typed]
 rfl

theorem clear_words_index {E : Source.Env} (frame : Source.Fr)
 (state : Source.ExecState E.layout E.lay E.lay) (path : Source.SPath) (indices : List Nat) (j : Nat)
 (ordinary : E.transientRoot (path.go (.index j))=false) (typed : E.cellTy (path.go (.index j))=.bool) :
 wordAt frame (state.run (indices.map (fun i => SourceScalarDeleteLog.clearOp E frame (path.go (.index i))))) (path.go (.index j))=
 if j ∈ indices then some 0 else wordAt frame state (path.go (.index j)) := by
 induction indices generalizing state with
 | nil => rfl
 | cons i indices ih =>
  simp only [List.map_cons,Source.ExecState.run]
  rw [ih]
  by_cases same : j=i
  · subst i
    rw [clear_word_false frame state _ ordinary typed]
    simp only [List.mem_cons,true_or,if_true,ite_self]
  · rw [SourceArrayDeleteTarget.clear_word_other frame state _ _ (index_ne_index path same)]
    simp only [List.mem_cons,same,false_or]

/-- Actual runtime write-list readback, including exact unvisited words. -/
theorem writes_word {E : Source.Env} (frame : Source.Fr) (path : Source.SPath)
 (payload : Nat → Source.Val E.layout .bool)
 (typed : ∀ j, (.bool : Source.STy)=E.cellTy (path.go (.index j)))
 (start count j : Nat) (state : Source.ExecState E.layout E.lay E.lay)
 (ordinary : E.transientRoot (path.go (.index j))=false) :
 wordAt frame (state.run (writes frame path payload typed start count)) (path.go (.index j))=
 if start≤j ∧ j<start+count then (payload j).word.map Fin.val else wordAt frame state (path.go (.index j)) := by
 induction count generalizing start state with
 | zero => simp only [writes,Source.ExecState.run,if_neg (by omega : ¬ (start≤j ∧ j<start+0))]
 | succ count ih =>
  simp only [writes,Source.ExecState.run]
  rw [ih]
  by_cases later : start+1≤j ∧ j<start+1+count
  · rw [if_pos later,if_pos (by omega : start≤j ∧ j<start+(count+1))]
  · rw [if_neg later]
    by_cases head : j=start
    · subst j
      rw [cell_word frame state _ _ ordinary,word_cast,if_pos (by omega : start≤start ∧ start<start+(count+1))]
    · rw [cell_word_other frame state _ _ _ (index_ne_index path head),if_neg (by omega : ¬ (start≤j ∧ j<start+(count+1)))]

/-- Exact copied/stale-live/older-shadow Source outcomes. The default scalar
clear remains the published Source default, with ordinary storage explicit. -/
theorem copy_data {E : Source.Env} (frame : Source.Fr) (dst : Source.SPath)
 (count oldLength j : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool none))
 (state : Source.ExecState E.layout E.lay E.lay) (ordinary : E.transientRoot dst=false) :
 wordAt frame (state.run (copyLog frame dst count oldLength payload typed)) (dst.go (.index j))=
 if j<count then (payload j).word.map Fin.val else if j<oldLength then some 0 else wordAt frame state (dst.go (.index j)) := by
 have childOrdinary : E.transientRoot (dst.go (.index j))=false := ordinary
 unfold copyLog
 rw [Source.run_append,Source.run_append]
 change wordAt frame ((state.run _).run _ |>.apply _) (dst.go (.index j))=_
 rw [cell_word_other frame _ dst _ _ (index_ne_header dst j)]
 rw [clear_words_index frame _ dst _ j childOrdinary (element_type dst typed j)]
 rw [writes_word frame dst payload _ 0 count j state childOrdinary]
 have membership : j ∈ List.range' count (oldLength-count) ↔ count≤j ∧ j<oldLength := by
  rw [List.mem_range']
  constructor
  · rintro ⟨i,inside,same⟩
    simp only [Nat.one_mul] at same
    omega
  · rintro ⟨lower,upper⟩
    refine ⟨j-count,by omega,?_⟩
    simp only [Nat.one_mul]
    omega
 by_cases copied : j<count
 · rw [if_pos copied,if_neg (by intro yes; have bound:count≤j := (membership.mp yes).1; omega),if_pos (by omega : 0≤j ∧ j<0+count)]
 · rw [if_neg copied,if_neg (by omega : ¬ (0≤j ∧ j<0+count))]
   by_cases stale : j<oldLength
   · rw [if_pos stale,if_pos (membership.mpr ⟨by omega,stale⟩)]
   · rw [if_neg stale,if_neg (by intro yes; exact stale (membership.mp yes).2)]

/-- The ACTUAL header write is the existing intWrap result; no new default
or integer implementation and no input length bound is hidden. -/
theorem copy_header {E : Source.Env} (frame : Source.Fr) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool none))
 (state : Source.ExecState E.layout E.lay E.lay) (ordinary : E.transientRoot dst=false) :
 wordAt frame (state.run (copyLog frame dst count oldLength payload typed)) dst=
 (Source.intWrap (D:=E.layout) Source.IntTy.u256 count).word.map Fin.val := by
 unfold copyLog
 rw [Source.run_append,Source.run_append]
 change wordAt frame ((state.run _).run _ |>.apply _) dst=_
 rw [cell_word frame _ dst _ ordinary,word_cast]


/-- info: 'Solidity.Backend.StorageOps.SourceBoolCopyReadbacks.bool_word' does not depend on any axioms -/
#guard_msgs in #print axioms bool_word
/-- info: 'Solidity.Backend.StorageOps.SourceBoolCopyReadbacks.clear_word_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_word_false
/-- info: 'Solidity.Backend.StorageOps.SourceBoolCopyReadbacks.clear_words_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_words_index
/-- info: 'Solidity.Backend.StorageOps.SourceBoolCopyReadbacks.writes_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms writes_word
/-- info: 'Solidity.Backend.StorageOps.SourceBoolCopyReadbacks.copy_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_data
/-- info: 'Solidity.Backend.StorageOps.SourceBoolCopyReadbacks.copy_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_header
end Solidity.Backend.StorageOps.SourceBoolCopyReadbacks
