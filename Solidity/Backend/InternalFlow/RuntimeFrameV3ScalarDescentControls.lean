import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarAllocatingDescent
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingPrefixes

/-! Actual zero/one/two allocating descent prefixes and their full three-cell
history. The initial bottom word is installed by real instructions; original
fixtures and vectors are unchanged. No general callRec compiler is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev σ := AllocatingScalarTarget.initial
abbrev F := ScalarAllocatingDescent.F
def input := writeMachine AllocatingScalarTarget.input 7 w[10]
def setupCode : List Instr := [.push w[0],.mstore 4] ++ [.push w[10],.mstore 7]
def loopCode : List Instr := [.loop guardCompiled.code (AllocatingScalarTurn.code 8)]

theorem available (steps : Nat) (small : steps≤2) :
 ∃ (τ : State C (Frame A)) (e : σ.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 run setupCode AllocatorReturn.Checks.input=.ok input 0 ∧
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code 8)) steps input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧
 τ.env=(PrimTy.dflt .uint,(countValue (2-steps) (by have h : 2<W := (by decide);omega),(some (P.r0.wk e),()))) ∧
 τ.H.length=σ.H.length+steps ∧ Heap.Keeps e σ.heap τ.heap ∧
 StructAllocatorRepr τ.heap addresses 16 (⟨22+4*steps,by have h : 30<W := (by decide);omega⟩ : Fin W) after ∧
 BaseExtends σ.H P.base addresses ∧
 (∀ j,j<steps → after.mem (10+3*j)=w[16] ∧ after.mem (10+3*j+1)=.val (wmod (2-j)) ∧ after.mem (10+3*j+2)=w[0]) ∧
 (after.stack,[after.mem 0,after.mem 2,after.mem 3,after.mem 4,after.mem 7,after.mem 8,after.mem 9,
 after.mem 16,after.mem 17,after.mem 18,after.mem 20,after.mem 21])=
 ([w[77]],[.val (wmod (22+4*steps)),w[16],.val (wmod (2-steps)),w[0],w[10],.val (wmod (10+3*steps)),w[99],w[2],w[7],w[9],w[1],w[4]]) := by
 have initialized : run setupCode AllocatorReturn.Checks.input=.ok input 0 :=
   (run_append_ok AllocatingScalarTarget.default_entry).trans (show run [.push w[10],.mstore 7] AllocatingScalarTarget.input=.ok input 0 from rfl)
 have initialRepr : StateRepr 1 2 16 F σ P.base input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have initialOwner : StructAllocatorRepr σ.heap P.base 16 (⟨22,by decide⟩ : Fin W) input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 have count : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=
     countValue ((2-steps)+steps) (by have h : 2<W := (by decide);omega) := by
   apply Subtype.ext
   change (2:Int)=(((2-steps)+steps:Nat):Int)
   omega
 obtain ⟨τ,e,after,addresses,actual,repr,env,size,kept,owner,extended,growth,stack,pointer,history,words⟩ :=
   running steps (2-steps) σ (by have h : 2<W := (by decide);omega) P.r0 rfl count rfl P.base input initialRepr
     (⟨22,by decide⟩ : Fin W) initialOwner (by have h : 30<W := (by decide);change 22+4*steps<W;omega)
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by omega) (by decide)
     (by have h : 16<W := (by decide);omega) rfl
 have resultValue : TEnv.get (.here : Idx (Frame A) (.val .uint)) τ.env=PrimTy.dflt .uint := by rw [env];rfl
 have counterValue : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) τ.env=
     countValue (2-steps) (by have h : 2<W := (by decide);omega) := by rw [env];rfl
 have resultRepr := repr.core.vals (.here : Idx (Frame A) (.val .uint))
 change ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) τ.env) (after.mem 4) at resultRepr
 rw [resultValue] at resultRepr
 have resultWord : after.mem 4=w[0] := Restore.uint_unique resultRepr (ReprV.dflt_zero .uint)
 have counterRepr := repr.core.vals (.there .here : Idx (Frame A) (.val .uint))
 change ReprV .uint (TEnv.get (.there .here : Idx (Frame A) (.val .uint)) τ.env) (after.mem 3) at counterRepr
 rw [counterValue] at counterRepr
 have counterCanonical : wmod (2-steps)=(⟨2-steps,by have h : 2<W := (by decide);omega⟩ : Fin W) :=
   Fin.ext (Nat.mod_eq_of_lt (by have h : 2<W := (by decide);omega))
 have encoded : ReprV .uint (countValue (2-steps) (by have h : 2<W := (by decide);omega)) (.val (wmod (2-steps))) := by
   rw [counterCanonical]
   exact ReprV.uint_of rfl
 have counterWord : after.mem 3=.val (wmod (2-steps)) := Restore.uint_unique counterRepr encoded
 obtain ⟨reference,binding,referenceWord⟩ := repr.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
 have expected : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) τ.env=some (P.r0.wk e) := by rw [env];rfl
 have same : reference=P.r0.wk e := Option.some.inj (binding.symm.trans expected)
 subst reference
 change after.mem 2=.val (addresses P.r0.id) at referenceWord
 rw [extended P.r0] at referenceWord
 have cursorWord : after.mem 0=.val (wmod (22+4*steps)) := by
   rw [owner.arrays.free.cell]
   congr 1
   exact Fin.ext (Nat.mod_eq_of_lt (by have h : 30<W := (by decide);omega)).symm
 have bottomWord : after.mem 7=w[10] := words 7 (by decide) (by decide) (by decide) (.inl (by decide))
 have sentinel : after.mem 9=w[99] := words 9 (by decide) (by decide) (by decide) (.inl (by decide))
 have first := AllocatingPrefixes.old_array e kept extended repr.heap P.r0
 have other := AllocatingPrefixes.old_array e kept extended repr.heap CompileExamples.r1
 have firstLength := first.length
 have otherLength := other.length
 have sourceLength0 : σ.heap.len P.r0 .dyn=2 := HeapDomain.Checks.length_zero
 have sourceLength1 : σ.heap.len CompileExamples.r1 .dyn=1 := HeapDomain.Checks.length_one
 rw [sourceLength0] at firstLength
 rw [sourceLength1] at otherLength
 change after.mem 16=w[2] at firstLength
 change after.mem 20=w[1] at otherLength
 have first0 := first.elements 0 (P.uint 7 (by decide)) (by with_unfolding_all rfl)
 have first1 := first.elements 1 (P.uint 9 (by decide)) (by with_unfolding_all rfl)
 have other0 := other.elements 0 (P.uint 4 (by decide)) (by with_unfolding_all rfl)
 have word7 : after.mem 17=w[7] := Restore.uint_unique first0 (ReprV.uint_of rfl)
 have word9 : after.mem 18=w[9] := Restore.uint_unique first1 (ReprV.uint_of rfl)
 have word4 : after.mem 21=w[4] := Restore.uint_unique other0 (ReprV.uint_of rfl)
 refine ⟨τ,e,after,addresses,initialized,actual,repr,env,size,kept,owner,extended,?_,?_⟩
 · intro j lower
   simpa only [show (2-steps)+steps-j=2-j from by omega] using history j lower
 · rw [stack,cursorWord,referenceWord,counterWord,resultWord,bottomWord,pointer,sentinel,
     firstLength,word7,word9,otherLength,word4]
   rfl

theorem complete : ∃ (τ : State C (Frame A)) (e : σ.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 run (setupCode ++ loopCode) AllocatorReturn.Checks.input=.ok after 0 ∧
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code 8)) 3 input=.inr (.ok after 0) ∧
 StateRepr 1 2 16 F τ addresses after ∧ Heap.Keeps e σ.heap τ.heap ∧
 StructAllocatorRepr τ.heap addresses 16 (⟨30,by decide⟩ : Fin W) after ∧
 τ.H.length=4 ∧ after.mem 0=w[30] ∧ after.mem 8=w[16] ∧
 after.mem 10=w[16] ∧ after.mem 11=w[2] ∧ after.mem 12=w[0] ∧
 after.mem 13=w[16] ∧ after.mem 14=w[1] ∧ after.mem 15=w[0] ∧
 after.mem 0≠w[34] ∧ after.mem 11≠after.mem 14 := by
 obtain ⟨τ,e,after,addresses,setup,running,repr,environment,size,kept,owner,extended,history,obs⟩ := available 2 (by decide)
 have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [environment];rfl
 have done := zero_turn τ counter addresses after repr 8
 have stopped := GuardedPrefixes.finish_prefix _ _ 2 input after (.ok after 0) running done
 have loopRun : run loopCode input=.ok after 0 :=
   GuardedRecursion.successful_loop guardCompiled.code (AllocatingScalarTurn.code 8) input after 3 stopped
 have first := history 0 (by decide)
 have next := history 1 (by decide)
 have cursor : after.mem 0=w[30] := congrArg (fun t : List Word × List Word => t.2[0]!) obs
 have pointer : after.mem 8=w[16] := congrArg (fun t : List Word × List Word => t.2[5]!) obs
 refine ⟨τ,e,after,addresses,(run_append_ok setup).trans loopRun,stopped,repr,kept,owner,?_,cursor,pointer,
   first.1,first.2.1,first.2.2,next.1,next.2.1,next.2.2,?_,?_⟩
 · simpa using size
 · rw [cursor]
   decide
 · rw [first.2.1,next.2.1]
   decide

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.Controls.available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.Controls.available

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.Controls.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocatingDescent.Controls.complete
