import Solidity.Lowering.StorageOps.SourceReadFrames

/-! Operation-side footprints of actual nested Source capture allocations.
These are existing Source.St/Heap operations, not another heap/evaluator.
Storage observation preservation is distinct from full-state preservation. -/
namespace Solidity.Lowering.StorageOps.SourceNestedByteCapture
open Solidity Solidity.Backend.StorageOps

/-- Exactly one existing allocation of an empty memory-byte object. -/
def captureStep {E : Source.Env} (state : Source.St E) : Source.St E :=
 {state with heap:=(state.heap.alloc ⟨.bytes .memory,Source.Data.bytes []⟩).1}

/-- Actual nested capture allocates even an empty byte object. -/
theorem empty_capture {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (path : Source.SPath) (padding : Nat)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame path).run (locals,state)=(.ok 0,(locals,state))) :
 (Source.loadElem (E:=E) (Γ:=Γ) frame (padding+3) (.bytes .memory) path).run (locals,state)=
 (.ok (Source.Val.memRef (τ:=.bytes .memory) rfl state.heap.next),(locals,captureStep state)) := by
 simp only [Source.loadElem,Source.STy.byRef,Source.STy.loc?,Option.isSome_some,
   if_true,Source.loadMem,Source.Hoare.run_bind,header]
 rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCapture.empty_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_capture

/-- A capture of count+1 empty reference elements at original fuel count+3
fails after exactly count actual heap allocations. Storage/journal effects
are not substituted for the resulting full Source state. -/
theorem timeout_prefix : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (start count : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (path.go (.index (start+j)))).run (locals,state)=(.ok 0,(locals,state))),
 (Solidity.Source.loadElems (E:=E) (Γ:=Γ) frame (count+3) (.bytes .memory) path start (count+1)).run (locals,state)=
 (.error .timeout,(locals,Nat.repeatTR Solidity.Lowering.StorageOps.SourceNestedByteCapture.captureStep count state)) := by
 intro E Γ frame path start count locals state headers
 induction count generalizing start state with
 | zero =>
   have first := headers 0 (by omega)
   simp only [Nat.add_zero] at first
   simp only [Source.loadElems,Source.loadElem,Source.STy.byRef,Source.STy.loc?,
     Option.isSome_some,if_true,Source.loadMem,Source.Hoare.run_bind,first]
   rfl
 | succ count ih =>
   change ((Source.loadElem frame (count+3) (.bytes .memory) (path.go (.index start)) >>= fun x =>
     Source.loadElems frame (count+3) (.bytes .memory) path (start+1) (count+1) >>= fun xs =>
     pure (Source.finCons (.val x) xs)).run (locals,state))=_
   have first := headers 0 (by omega)
   simp only [Nat.add_zero] at first
   rw [Source.Hoare.run_bind,empty_capture frame (path.go (.index start)) count locals state first]
   dsimp only
   rw [Source.Hoare.run_bind,ih (start+1) (captureStep state) (by
     intro j member
     rw [SourceReadFrames.readLen_transport frame (path.go (.index ((start+1)+j)))
       locals state (captureStep state) rfl rfl]
     have found := headers (j+1) (by omega)
     have index : start+(j+1)=(start+1)+j := by omega
     rw [index] at found
     rw [found])]
   rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCapture.timeout_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_prefix
end Solidity.Lowering.StorageOps.SourceNestedByteCapture
