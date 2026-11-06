import Solidity.Lowering.StorageOps.SourceCopyFrames

/-! Readbacks of actual Source storage-copy payload/header operations, for
composition with existing numeric/target operations. Independent Source
semantics remains the specification; no compiler relation is defined here. -/
namespace Solidity.Backend.StorageOps.SourceCopyReadbacks
open SourceStorageCopy SourceCopyFrames SourceArrayDeleteTarget

theorem word_cast {D : Source.Layout} {τ σ : Source.STy} (same : τ=σ) (value : Source.Val D τ) :
 (same ▸ value).word=value.word := by cases same; rfl

theorem index_ne_header (path : Source.SPath) (j : Nat) : path.go (.index j)≠path := by
 intro same
 have lengths := congrArg (fun p : Source.SPath => p.steps.length) same
 simp only [Source.SPath.go,List.length_append,List.length_singleton] at lengths
 omega

theorem index_ne_index (path : Source.SPath) {i j : Nat} (different : i≠j) : path.go (.index i)≠path.go (.index j) := by
 intro same
 have steps := congrArg Source.SPath.steps same
 change path.steps ++ [Source.Step.index i]=path.steps ++ [Source.Step.index j] at steps
 have suffix := List.append_cancel_left steps
 exact different (Source.Step.index.inj (List.cons.inj suffix).1)

theorem cell_word {E : Source.Env} (frame : Source.Fr)
 (state : Source.ExecState E.layout E.lay E.lay) (path : Source.SPath)
 (value : Source.Val E.layout (E.cellTy path)) (ordinary : E.transientRoot path=false) :
 wordAt frame (state.apply (cellOp E frame path (some value))) path=value.word.map Fin.val := by
 simp only [wordAt,cellOp,ordinary,Bool.false_eq_true,if_false,Source.ExecState.apply,Source.World.set_get,
  Source.Storage.read,Source.Storage.set,dif_pos,Option.bind_some]

theorem cell_word_other {E : Source.Env} (frame : Source.Fr)
 (state : Source.ExecState E.layout E.lay E.lay) (path query : Source.SPath)
 (value : Option (Source.Val E.layout (E.cellTy path))) (different : query≠path) :
 wordAt frame (state.apply (cellOp E frame path value)) query=wordAt frame state query := by
 unfold wordAt
 rw [(cell_other frame state path query value different).1]

/-- Actual runtime write-list readback, including exact unvisited words. -/
theorem writes_word {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (payload : Nat → Source.Val E.layout (.int t))
 (typed : ∀ j, (.int t : Source.STy)=E.cellTy (path.go (.index j)))
 (start count j : Nat) (state : Source.ExecState E.layout E.lay E.lay)
 (ordinary : E.transientRoot (path.go (.index j))=false) :
 wordAt frame (state.run (writes frame t path payload typed start count)) (path.go (.index j))=
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
 (count oldLength j : Nat) (payload : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (typed : E.pathTy dst=some (.array .storage (.int Source.IntTy.u256) none))
 (state : Source.ExecState E.layout E.lay E.lay) (ordinary : E.transientRoot dst=false) :
 wordAt frame (state.run (copyLog frame Source.IntTy.u256 dst count oldLength payload typed)) (dst.go (.index j))=
 if j<count then (payload j).word.map Fin.val else if j<oldLength then some 0 else wordAt frame state (dst.go (.index j)) := by
 have childOrdinary : E.transientRoot (dst.go (.index j))=false := ordinary
 unfold copyLog
 rw [Source.run_append,Source.run_append]
 change wordAt frame ((state.run _).run _ |>.apply _) (dst.go (.index j))=_
 rw [cell_word_other frame _ dst _ _ (index_ne_header dst j)]
 rw [clear_words_index frame _ dst _ j childOrdinary (element_type Source.IntTy.u256 dst typed j)]
 rw [writes_word frame Source.IntTy.u256 dst payload _ 0 count j state childOrdinary]
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
theorem copy_header {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (state : Source.ExecState E.layout E.lay E.lay) (ordinary : E.transientRoot dst=false) :
 wordAt frame (state.run (copyLog frame t dst count oldLength payload typed)) dst=
 (Source.intWrap (D:=E.layout) Source.IntTy.u256 count).word.map Fin.val := by
 unfold copyLog
 rw [Source.run_append,Source.run_append]
 change wordAt frame ((state.run _).run _ |>.apply _) dst=_
 rw [cell_word frame _ dst _ ordinary,word_cast]

/-- Normalize the PUBLISHED Source uint header at its existing word bound.
This is an operation adapter, not a new arithmetic/default implementation. -/
theorem header_word {D : Source.Layout} (count : Nat) (fits : count<2^256) :
 (Source.intWrap (D:=D) Source.IntTy.u256 count).word.map Fin.val=some count := by
 have wrapped : Source.IntTy.u256.wrap (count : Int)=(count : Int) := by
  simp only [Source.IntTy.wrap,Source.wrapBits,Source.IntTy.u256,Bool.false_eq_true,false_and,if_false]
  exact Int.emod_eq_of_lt (by omega) (by omega)
 simp only [Source.intWrap,Source.Val.word,wrapped,Source.intWord,Source.toWord,Option.map_some]
 rw [Int.emod_eq_of_lt (by omega : (0:Int)≤count) (by omega : (count:Int)<((2^256:Nat):Int))]
 simp only [Int.toNat_natCast,Nat.mod_eq_of_lt fits]

/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.word_cast' does not depend on any axioms -/
#guard_msgs in #print axioms word_cast
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.index_ne_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms index_ne_header
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.index_ne_index' does not depend on any axioms -/
#guard_msgs in #print axioms index_ne_index
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.cell_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cell_word
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.cell_word_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cell_word_other
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.writes_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms writes_word
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.copy_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_data
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.copy_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_header
/-- info: 'Solidity.Backend.StorageOps.SourceCopyReadbacks.header_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms header_word
end Solidity.Backend.StorageOps.SourceCopyReadbacks
