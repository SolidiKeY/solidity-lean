import Solidity.Lowering.StorageOps.SourceCopyReadbacks

/-! Actual independent Source copy sequencing. Readbacks may repeat while the
journal grows. Core/Source semantics, original fuel and refusals are unchanged.
This above-core consumer supplies no general compiler/hash/world simulation. -/
namespace Solidity.Backend.StorageOps.SourceCopyRepeat
open SourceStorageCopy SourceCopyFrames SourceCopyReadbacks SourceArrayDeleteTarget

/-- The actual header write derives the NEXT input length at the existing
uint256 bound, retaining the entire post-copy state and journal. -/
theorem header_readback {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (dst : Source.SPath) (count oldLength : Nat)
 (payload : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (typed : E.pathTy dst=some (.array .storage (.int Source.IntTy.u256) none))
 (ordinary : E.transientRoot dst=false) (fits : count<2^256)
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 let after := {state with ex:=state.ex.run (copyLog frame Source.IntTy.u256 dst count oldLength payload typed)}
 (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,after)=(.ok count,(locals,after)) := by
 have headerType : E.cellTy dst=.int Source.IntTy.u256 := by
  simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some]
 have wrapped : Source.IntTy.u256.wrap (count : Int)=(count : Int) := by
  simp only [Source.IntTy.wrap,Source.wrapBits,Source.IntTy.u256,Bool.false_eq_true,false_and,if_false]
  exact Int.emod_eq_of_lt (by omega) (by omega)
 dsimp only
 simp only [copyLog,Source.run_append,Source.ExecState.run]
 simp only [Source.readLen,Source.readAt,dif_pos headerType,bind_assoc,pure_bind]
 simp only [Source.readCell,Source.EM.st,bind,pure,get,getThe,liftM,MonadLiftT.monadLift,MonadLift.monadLift,
  Functor.map,StateT.map,MonadStateOf.get,ExceptT.mk,ExceptT.run,ExceptT.bind,ExceptT.bindCont,ExceptT.pure,ExceptT.lift,
  StateT.bind,StateT.pure,StateT.get,cellOp,ordinary,Bool.false_eq_true,if_false,Source.ExecState.apply,
  Source.World.set_get,Source.Storage.read,Source.Storage.set,dif_pos,Source.Env.lay]
 have undo : headerType ▸ (headerType.symm ▸ Source.intWrap (D:=E.layout) Source.IntTy.u256 count)=
   Source.intWrap (D:=E.layout) Source.IntTy.u256 count :=
  eq_of_heq ((eqRec_heq (φ := fun τ => Source.Val E.layout τ) headerType _).trans
   (eqRec_heq (φ := fun τ => Source.Val E.layout τ) headerType.symm _))
 rw [undo]
 simp only [Source.intWrap,wrapped,Int.toNat_natCast]
 rfl

/-- ALL ordinary-storage word observations repeat under the actual generated
Source logs. This equality deliberately does not identify journal/state values. -/
theorem word_repeat {E : Source.Env} (frame : Source.Fr) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (typed : E.pathTy dst=some (.array .storage (.int Source.IntTy.u256) none))
 (ordinary : E.transientRoot dst=false) (state : Source.ExecState E.layout E.lay E.lay) :
 let first := state.run (copyLog frame Source.IntTy.u256 dst count oldLength payload typed)
 ∀ query,wordAt frame (first.run (copyLog frame Source.IntTy.u256 dst count count payload typed)) query=wordAt frame first query := by
 dsimp only
 intro query
 by_cases header : query=dst
 · subst query
   exact (copy_header frame Source.IntTy.u256 dst count count payload typed
    (state.run (copyLog frame Source.IntTy.u256 dst count oldLength payload typed)) ordinary).trans
    (copy_header frame Source.IntTy.u256 dst count oldLength payload typed state ordinary).symm
 · by_cases child : ∃ i,query=dst.go (.index i)
   · obtain ⟨i,rfl⟩:=child
     rw [copy_data frame dst count count i payload typed
      (state.run (copyLog frame Source.IntTy.u256 dst count oldLength payload typed)) ordinary]
     by_cases live : i<count
     · rw [if_pos live,copy_data frame dst count oldLength i payload typed state ordinary,if_pos live]
     · rw [if_neg live,if_neg live]
   · have frameResult := copy_other frame Source.IntTy.u256 dst query count count payload typed
      (state.run (copyLog frame Source.IntTy.u256 dst count oldLength payload typed)) header
      (fun i _ same => child ⟨i,same⟩) (fun i _ same => child ⟨i,same⟩)
     unfold wordAt
     rw [frameResult.1]

/-- TWO independent CURRENT Source.storeVal executions, their exact composed
Source.Op effect and all word readbacks. OLD reads and path separation derive
second reads/length; journals strictly grow even when every word stabilizes.
Each operation uses its unchanged sufficient ORIGINAL runtime fuel formula. -/
theorem complete {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (src dst : Source.SPath) (different : src≠dst)
 (count oldLength : Nat) (fits : count<2^256)
 (payload : Nat → Source.Val E.layout (.int Source.IntTy.u256))
 (typed : E.pathTy dst=some (.array .storage (.int Source.IntTy.u256) none))
 (ordinary : E.transientRoot dst=false)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int Source.IntTy.u256)).run (locals,state)=(.ok (payload j),(locals,state)))
 (dstHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state)))
 (outside : ∀ query,query=src ∨ (∃ j<count,query=src.go (.index j)) →
  query≠dst ∧ (∀ j<count,query≠dst.go (.index j)) ∧
  (∀ j∈List.range' count (oldLength-count),query≠dst.go (.index j))) :
 let firstLog := copyLog frame Source.IntTy.u256 dst count oldLength payload typed
 let secondLog := copyLog frame Source.IntTy.u256 dst count count payload typed
 let first := {state with ex:=state.ex.run firstLog}
 let final := {state with ex:=(state.ex.run firstLog).run secondLog}
 let op1 := Source.storeVal (E:=E) (Γ:=Γ) frame (count+(oldLength-count)+4)
  (.array .storage (.int Source.IntTy.u256) none) dst (Source.Val.storRef (τ:=.array .storage (.int Source.IntTy.u256) none) rfl src)
 let op2 := Source.storeVal (E:=E) (Γ:=Γ) frame (count+4)
  (.array .storage (.int Source.IntTy.u256) none) dst (Source.Val.storRef (τ:=.array .storage (.int Source.IntTy.u256) none) rfl src)
 op1.run (locals,state)=(.ok (),(locals,first)) ∧
 op2.run (locals,first)=(.ok (),(locals,final)) ∧
 (op1 >>= fun _ => op2).run (locals,state)=(.ok (),(locals,final)) ∧
 (∀ query,wordAt frame final.ex query=wordAt frame first.ex query) ∧
 final.ex.journal.length=state.ex.journal.length+(count+(oldLength-count)+1)+(count+1) ∧
 first.ex.journal.length<final.ex.journal.length := by
 dsimp only
 let first : Source.St E := {state with ex:=state.ex.run (copyLog frame Source.IntTy.u256 dst count oldLength payload typed)}
 have firstRun := SourceStorageCopy.complete frame writable Source.IntTy.u256 src dst different count oldLength payload typed locals state sourceHeader reads dstHeader
 have headerOutside := outside src (Or.inl rfl)
 have sourceNext : (Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,first)=(.ok count,(locals,first)) := by
  have transport := SourceCopyFrames.readLen frame Source.IntTy.u256 dst src count oldLength payload typed locals state
   headerOutside.1 headerOutside.2.1 headerOutside.2.2
  rw [sourceHeader] at transport
  exact transport
 have readsNext : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int Source.IntTy.u256)).run (locals,first)=(.ok (payload j),(locals,first)) := by
  intro j inside
  have apart := outside (src.go (.index j)) (Or.inr ⟨j,inside,rfl⟩)
  have transport := SourceCopyFrames.readAt frame Source.IntTy.u256 dst (src.go (.index j)) count oldLength payload typed locals state
   (.int Source.IntTy.u256) apart.1 apart.2.1 apart.2.2
  rw [reads j inside] at transport
  exact transport
 have headerNext := header_readback frame dst count oldLength payload typed ordinary fits locals state
 have secondRun := SourceStorageCopy.complete frame writable Source.IntTy.u256 src dst different count count payload typed locals first sourceNext readsNext headerNext
 simp only [Nat.sub_self,Nat.add_zero] at secondRun
 refine ⟨firstRun,secondRun,?_,word_repeat frame dst count oldLength payload typed ordinary state.ex,?_,?_⟩
 · rw [Source.Hoare.run_bind,firstRun]
   dsimp only
   exact secondRun
 · have journal1 := SourceCopyFrames.journal frame Source.IntTy.u256 dst count oldLength payload typed state.ex
   have journal2 := SourceCopyFrames.journal frame Source.IntTy.u256 dst count count payload typed first.ex
   simp only [Nat.sub_self,Nat.add_zero] at journal2
   rw [journal2,journal1]
 · have journal2 := SourceCopyFrames.journal frame Source.IntTy.u256 dst count count payload typed first.ex
   simp only [Nat.sub_self,Nat.add_zero] at journal2
   change first.ex.journal.length < (first.ex.run (copyLog frame Source.IntTy.u256 dst count count payload typed)).journal.length
   rw [journal2]
   omega

/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.header_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_readback
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.word_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms word_repeat
/-- info: 'Solidity.Backend.StorageOps.SourceCopyRepeat.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.SourceCopyRepeat
