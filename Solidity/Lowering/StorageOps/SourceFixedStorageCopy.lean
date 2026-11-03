import Solidity.Lowering.StorageOps.SourceCopyReadbacks

/-! Actual independent Source fixed-length storage-reference copying.
Existing loadElems/storeElems/writes are reused. The fixed branch captures all
payloads first, writes only declared elements and never reads/writes a runtime
length header or clears a dynamic stale tail. No new lowering/evaluator/state. -/
namespace Solidity.Backend.StorageOps.SourceFixedStorageCopy
open SourceStorageCopy SourceCopyReadbacks
open SourceArrayDeleteTarget (wordAt)

theorem load_fixed {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index j)) (.int t)).run initial=(.ok (payload j),initial)) :
 (Source.loadMem (E:=E) (Γ:=Γ) frame (count+padding+2) (.array .memory (.int t) (some count)) path).run initial=
 (.ok (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) (fun j : Fin count => .val (payload j.val))),initial) := by
 have budget : count+padding+2=(count+padding+1)+1 := by omega
 rw [budget]
 change ((Source.loadElems frame (count+padding+1) (.int t) path 0 count >>= fun xs =>
   pure (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) xs)).run initial)=_
 rw [Source.Hoare.run_bind,SourceStorageCopy.load_elems frame t path 0 count padding payload initial (by simpa only [Nat.zero_add] using reads)]
 simp only [Nat.zero_add]
 rfl

theorem captured_copy {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run initial=(.ok (payload j),initial)) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+3) (.array .storage (.int t) (some count)) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) (some count)) rfl src)).run initial=
 (Source.storeData (E:=E) (Γ:=Γ) frame (count+padding+2) (.array .storage (.int t) (some count)) dst
  (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) (fun j : Fin count => .val (payload j.val)))).run initial := by
 have budget : count+padding+3=(count+padding+2)+1 := by omega
 rw [budget]
 simp only [Source.storeVal,if_neg different,Source.STy.withLoc]
 rw [Source.Hoare.run_bind,load_fixed frame t src count padding payload initial reads]

theorem element_type {E : Source.Env} (t : Source.IntTy) (path : Source.SPath) (count : Nat)
 (typed : E.pathTy path=some (.array .storage (.int t) (some count))) (i : Nat) :
 E.cellTy (path.go (.index i))=.int t := by
 simp only [Source.Env.cellTy,Source.Env.pathTy_go,typed,Option.bind_some,Source.Env.stepTy,Option.map_some,Option.getD_some,Source.STy.cell,Source.STy.isValue,if_true]

theorem store_fixed {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (dst : Source.SPath)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.storeData (E:=E) (Γ:=Γ) frame (count+padding+3) (.array .storage (.int t) (some count)) dst
  (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) (fun j : Fin count => .val (payload j.val)))).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (writes frame t dst payload (fun j => (element_type t dst count typed j).symm) 0 count)})) := by
 have budget : count+padding+3=(count+padding+2)+1 := by omega
 rw [budget]
 change (Source.storeElems frame (count+padding+2) (.int t) dst 0 count (fun j : Fin count => .val (payload j.val))).run (locals,state)=_
 have result := SourceStorageCopy.store_elems frame writable t dst 0 count padding payload (fun j => (element_type t dst count typed j).symm) locals state
 simpa only [Nat.zero_add] using result

/-- Arbitrary declared fixed count, no runtime header input or dynamic-tail
premise. OLD payload reads capture the snapshot before ALL actual writes. -/
theorem complete {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state))) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage (.int t) (some count)) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) (some count)) rfl src)).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (writes frame t dst payload (fun j => (element_type t dst count typed j).symm) 0 count)})) := by
 have capture := captured_copy frame t src dst different count (padding+1) payload (locals,state) reads
 have outer : count+(padding+1)+3=count+padding+4 := by omega
 have inner : count+(padding+1)+2=count+padding+3 := by omega
 rw [outer,inner] at capture
 rw [capture]
 exact store_fixed frame writable t dst count padding payload typed locals state

theorem data_word {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (src dst : Source.SPath) (different : src≠dst)
 (count padding j : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) (some count))) (ordinary : E.transientRoot dst=false)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) (.int t)).run (locals,state)=(.ok (payload i),(locals,state))) :
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage (.int t) (some count)) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) (some count)) rfl src)).run (locals,state)
 wordAt frame result.2.2.ex (dst.go (.index j))=if j<count then (payload j).word.map Fin.val else wordAt frame state.ex (dst.go (.index j)) := by
 dsimp only
 rw [complete frame writable t src dst different count padding payload typed locals state reads]
 rw [SourceCopyReadbacks.writes_word frame t dst payload _ 0 count j state.ex ordinary]
 simp only [Nat.zero_add,Nat.zero_le,true_and]

theorem frame_other {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (src dst query : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) (.int t)).run (locals,state)=(.ok (payload i),(locals,state)))
 (untouched : ∀ j<count,query≠dst.go (.index j)) :
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage (.int t) (some count)) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) (some count)) rfl src)).run (locals,state)
 (result.2.2.ex.world.accounts frame.this).storage.read query=(state.ex.world.accounts frame.this).storage.read query ∧
 (result.2.2.ex.transient.cells frame.this).read query=(state.ex.transient.cells frame.this).read query := by
 dsimp only
 rw [complete frame writable t src dst different count padding payload typed locals state reads]
 exact SourceCopyFrames.writes_other frame t dst query payload _ 0 count state.ex (by simpa only [Nat.zero_add] using untouched)

theorem journal {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) (.int t)).run (locals,state)=(.ok (payload i),(locals,state))) :
 ((Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage (.int t) (some count)) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) (some count)) rfl src)).run (locals,state)).2.2.ex.journal.length=state.ex.journal.length+count := by
 rw [complete frame writable t src dst different count padding payload typed locals state reads]
 rw [Source.ExecState.journal_run,SourceCopyFrames.writes_length]

theorem rollback {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) (input : Roadmap.Bytes)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) (.int t)).run (locals,state)=(.ok (payload i),(locals,state))) :
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage (.int t) (some count)) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) (some count)) rfl src)).run (locals,state)
 (result.2.1,{result.2.2 with ex:=(state.ex.enter frame.this frame.sender frame.value input frame.static).rollback result.2.2.ex})=(locals,state) := by
 dsimp only
 rw [complete frame writable t src dst different count padding payload typed locals state reads,Source.rollback_run]

/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.load_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms load_fixed
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.captured_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms captured_copy
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.element_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms element_type
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.store_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms store_fixed
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.data_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms data_word
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.frame_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frame_other
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.journal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms journal
/-- info: 'Solidity.Backend.StorageOps.SourceFixedStorageCopy.rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rollback
end Solidity.Backend.StorageOps.SourceFixedStorageCopy
