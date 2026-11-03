import Solidity.Lowering.StorageOps.SourceBoolCopyReadbacks

/-! Actual independent BOOLEAN Source fixed-length storage-reference copying.
Existing loadElems/storeElems/writes are reused. The fixed branch captures all
payloads first, writes only declared elements and never reads/writes a runtime
length header or clears a dynamic stale tail. No new lowering/evaluator/state. -/
namespace Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy
open SourceStorageCopy SourceCopyReadbacks
open SourceArrayDeleteTarget (wordAt)

theorem load_fixed {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (path : Source.SPath)
 (count padding : Nat) (payload : Nat → Source.Val E.layout .bool)
 (initial : Source.Locals E.layout Γ × Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index j)) .bool).run initial=(.ok (payload j),initial)) :
 (Source.loadMem (E:=E) (Γ:=Γ) frame (count+padding+2) (.array .memory .bool (some count)) path).run initial=
 (.ok (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) (fun j : Fin count => .val (payload j.val))),initial) := by
 have budget : count+padding+2=(count+padding+1)+1 := by omega
 rw [budget]
 change ((Source.loadElems frame (count+padding+1) .bool path 0 count >>= fun xs =>
   pure (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) xs)).run initial)=_
 rw [Source.Hoare.run_bind,SourceBoolStorageCopy.load_elems frame path 0 count padding payload initial (by simpa only [Nat.zero_add] using reads)]
 simp only [Nat.zero_add]
 rfl

theorem captured_copy {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout .bool)
 (initial : Source.Locals E.layout Γ × Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) .bool).run initial=(.ok (payload j),initial)) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+3) (.array .storage .bool (some count)) dst
  (Source.Val.storRef (τ:=.array .storage .bool (some count)) rfl src)).run initial=
 (Source.storeData (E:=E) (Γ:=Γ) frame (count+padding+2) (.array .storage .bool (some count)) dst
  (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) (fun j : Fin count => .val (payload j.val)))).run initial := by
 have budget : count+padding+3=(count+padding+2)+1 := by omega
 rw [budget]
 simp only [Source.storeVal,if_neg different,Source.STy.withLoc]
 rw [Source.Hoare.run_bind,load_fixed frame src count padding payload initial reads]

theorem element_type {E : Source.Env} (path : Source.SPath) (count : Nat)
 (typed : E.pathTy path=some (.array .storage .bool (some count))) (i : Nat) :
 E.cellTy (path.go (.index i))=.bool := by
 simp only [Source.Env.cellTy,Source.Env.pathTy_go,typed,Option.bind_some,Source.Env.stepTy,Option.map_some,Option.getD_some,Source.STy.cell,Source.STy.isValue,if_true]

theorem store_fixed {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (dst : Source.SPath)
 (count padding : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.storeData (E:=E) (Γ:=Γ) frame (count+padding+3) (.array .storage .bool (some count)) dst
  (Source.Data.array (l:=.memory) (n:=some count) count (fun _ h => by cases h; rfl) (fun j : Fin count => .val (payload j.val)))).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (SourceBoolStorageCopy.writes frame dst payload (fun j => (element_type dst count typed j).symm) 0 count)})) := by
 have budget : count+padding+3=(count+padding+2)+1 := by omega
 rw [budget]
 change (Source.storeElems frame (count+padding+2) .bool dst 0 count (fun j : Fin count => .val (payload j.val))).run (locals,state)=_
 have result := SourceBoolStorageCopy.store_elems frame writable dst 0 count padding payload (fun j => (element_type dst count typed j).symm) locals state
 simpa only [Nat.zero_add] using result

/-- Arbitrary declared fixed count, no runtime header input or dynamic-tail
premise. OLD payload reads capture the snapshot before ALL actual writes. -/
theorem complete {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) .bool).run (locals,state)=(.ok (payload j),(locals,state))) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage .bool (some count)) dst
  (Source.Val.storRef (τ:=.array .storage .bool (some count)) rfl src)).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (SourceBoolStorageCopy.writes frame dst payload (fun j => (element_type dst count typed j).symm) 0 count)})) := by
 have capture := captured_copy frame src dst different count (padding+1) payload (locals,state) reads
 have outer : count+(padding+1)+3=count+padding+4 := by omega
 have inner : count+(padding+1)+2=count+padding+3 := by omega
 rw [outer,inner] at capture
 rw [capture]
 exact store_fixed frame writable dst count padding payload typed locals state

theorem data_word {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (src dst : Source.SPath) (different : src≠dst)
 (count padding j : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool (some count))) (ordinary : E.transientRoot dst=false)
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) .bool).run (locals,state)=(.ok (payload i),(locals,state))) :
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage .bool (some count)) dst
  (Source.Val.storRef (τ:=.array .storage .bool (some count)) rfl src)).run (locals,state)
 wordAt frame result.2.2.ex (dst.go (.index j))=if j<count then (payload j).word.map Fin.val else wordAt frame state.ex (dst.go (.index j)) := by
 dsimp only
 rw [complete frame writable src dst different count padding payload typed locals state reads]
 rw [SourceBoolCopyReadbacks.writes_word frame dst payload _ 0 count j state.ex ordinary]
 simp only [Nat.zero_add,Nat.zero_le,true_and]

private theorem bool_writes_other {E : Source.Env} (frame : Source.Fr) (path query : Source.SPath)
 (payload : Nat → Source.Val E.layout .bool)
 (typed : ∀ j, (.bool : Source.STy)=E.cellTy (path.go (.index j)))
 (start count : Nat) (state : Source.ExecState E.layout E.lay E.lay)
 (untouched : ∀ j<count,query≠path.go (.index (start+j))) :
 ((state.run (SourceBoolStorageCopy.writes frame path payload typed start count)).world.accounts frame.this).storage.read query=(state.world.accounts frame.this).storage.read query ∧
 ((state.run (SourceBoolStorageCopy.writes frame path payload typed start count)).transient.cells frame.this).read query=(state.transient.cells frame.this).read query := by
 induction count generalizing start state with
 | zero => exact ⟨rfl,rfl⟩
 | succ count ih =>
  have first := SourceCopyFrames.cell_other frame state (path.go (.index start)) query (some ((typed start) ▸ payload start)) (by simpa only [Nat.add_zero] using untouched 0 (by omega))
  have rest := ih (start+1) (state.apply (cellOp E frame (path.go (.index start)) (some ((typed start) ▸ payload start)))) (by
   intro j member
   have apart := untouched (j+1) (by omega)
   simpa only [Nat.add_assoc,Nat.add_comm j 1] using apart)
  exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩


theorem frame_other {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (src dst query : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) .bool).run (locals,state)=(.ok (payload i),(locals,state)))
 (untouched : ∀ j<count,query≠dst.go (.index j)) :
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage .bool (some count)) dst
  (Source.Val.storRef (τ:=.array .storage .bool (some count)) rfl src)).run (locals,state)
 (result.2.2.ex.world.accounts frame.this).storage.read query=(state.ex.world.accounts frame.this).storage.read query ∧
 (result.2.2.ex.transient.cells frame.this).read query=(state.ex.transient.cells frame.this).read query := by
 dsimp only
 rw [complete frame writable src dst different count padding payload typed locals state reads]
 exact bool_writes_other frame dst query payload _ 0 count state.ex (by simpa only [Nat.zero_add] using untouched)

private theorem bool_writes_length {E : Source.Env} (frame : Source.Fr) (path : Source.SPath)
 (payload : Nat → Source.Val E.layout .bool)
 (typed : ∀ j, (.bool : Source.STy)=E.cellTy (path.go (.index j))) (start count : Nat) :
 (SourceBoolStorageCopy.writes frame path payload typed start count).length=count := by
 induction count generalizing start with
 | zero => rfl
 | succ count ih => simp only [SourceBoolStorageCopy.writes,List.length_cons,ih]

theorem journal {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) .bool).run (locals,state)=(.ok (payload i),(locals,state))) :
 ((Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage .bool (some count)) dst
  (Source.Val.storRef (τ:=.array .storage .bool (some count)) rfl src)).run (locals,state)).2.2.ex.journal.length=state.ex.journal.length+count := by
 rw [complete frame writable src dst different count padding payload typed locals state reads]
 rw [Source.ExecState.journal_run,bool_writes_length]

theorem rollback {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout .bool)
 (typed : E.pathTy dst=some (.array .storage .bool (some count)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) (input : Roadmap.Bytes)
 (reads : ∀ i<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index i)) .bool).run (locals,state)=(.ok (payload i),(locals,state))) :
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4) (.array .storage .bool (some count)) dst
  (Source.Val.storRef (τ:=.array .storage .bool (some count)) rfl src)).run (locals,state)
 (result.2.1,{result.2.2 with ex:=(state.ex.enter frame.this frame.sender frame.value input frame.static).rollback result.2.2.ex})=(locals,state) := by
 dsimp only
 rw [complete frame writable src dst different count padding payload typed locals state reads,Source.rollback_run]

/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.load_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms load_fixed
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.captured_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms captured_copy
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.element_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms element_type
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.store_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms store_fixed
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.data_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms data_word
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.frame_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frame_other
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms journal
/-- info: 'Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy.rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rollback
end Solidity.Backend.StorageOps.SourceBoolFixedStorageCopy
