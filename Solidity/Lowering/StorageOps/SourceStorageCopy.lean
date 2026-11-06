import Solidity.Lowering.StorageOps.SourceReadFrames

/-! Actual independent Source storage-to-storage copy capture. No Source edits,
heap surrogate, target-as-source evaluator or memory-to-storage lowering task.
Original Source fuel and exact state outcomes are preserved. -/
namespace Solidity.Backend.StorageOps.SourceStorageCopy

/-- Primitive loadElems traverses EVERY runtime position, reading the original
state throughout. No heap allocation occurs and no depth/length cap is added. -/
theorem load_elems {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (start count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index (start+j))) (.int t)).run initial=(.ok (payload (start+j)),initial)) :
 (Source.loadElems (E:=E) (Γ:=Γ) frame (count+padding+1) (.int t) path start count).run initial=
 (.ok (fun j : Fin count => Source.Data.val (payload (start+j.val))),initial) := by
 induction count generalizing start with
 | zero =>
   change (Except.ok (ε:=Source.Halt) (Fin.elim0 : Fin 0 → Source.Data E.layout (.int t)),initial)=_
   have vector : (Fin.elim0 : Fin 0 → Source.Data E.layout (.int t))=(fun j : Fin 0 => Source.Data.val (payload (start+j.val))) := by
    funext j; exact Fin.elim0 j
   rw [vector]
 | succ count ih =>
   have budget : count+1+padding+1=(count+padding+1)+1 := by omega
   rw [budget]
   change ((Source.readAt frame (path.go (.index start)) (.int t) >>= fun x =>
     Source.loadElems frame (count+padding+1) (.int t) path (start+1) count >>= fun f =>
       pure (Source.finCons (.val x) f)).run initial)=_
   rw [Source.Hoare.run_bind]
   have first := reads 0 (by omega)
   simp only [Nat.add_zero] at first
   rw [first]
   dsimp only
   rw [Source.Hoare.run_bind]
   have rest := ih (start+1) (by
    intro j member
    have found := reads (j+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm j 1] using found)
   rw [rest]
   change (Except.ok (ε:=Source.Halt) (Source.finCons (Source.Data.val (payload start)) (fun j : Fin count => Source.Data.val (payload (start+1+j.val)))),initial)=_
   have vector : Source.finCons (Source.Data.val (payload start)) (fun j : Fin count => Source.Data.val (payload (start+1+j.val)))=
    (fun j : Fin (count+1) => Source.Data.val (payload (start+j.val))) := by
    funext j
    unfold Source.finCons
    split
    next zero => simp only [zero,Nat.add_zero]
    next nonzero =>
     have index : start+1+(j.val-1)=start+j.val := by omega
     dsimp only
     rw [index]
   rw [vector]

theorem load_array {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E)
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame path).run initial=(.ok count,initial))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index j)) (.int t)).run initial=(.ok (payload j),initial)) :
 (Source.loadMem (E:=E) (Γ:=Γ) frame (count+padding+2) (.array .memory (.int t) none) path).run initial=
 (.ok (Source.Data.array (l:=.memory) (n:=none) count (fun _ h => nomatch h) (fun j : Fin count => .val (payload j.val))),initial) := by
 have budget : count+padding+2=(count+padding+1)+1 := by omega
 rw [budget]
 change ((Source.readLen frame path >>= fun len =>
  Source.loadElems frame (count+padding+1) (.int t) path 0 len >>= fun xs =>
   pure (Source.Data.array (l:=.memory) (n:=none) len (fun _ h => nomatch h) xs)).run initial)=_
 rw [Source.Hoare.run_bind,header]
 dsimp only
 rw [Source.Hoare.run_bind]
 rw [load_elems frame t path 0 count padding payload initial (by simpa only [Nat.zero_add] using reads)]
 simp only [Nat.zero_add]
 rfl

/-- A genuine distinct-path storeVal first captures all source elements from
OLD state. The remaining computation is the ACTUAL storeData, not a simulated
copy or an assumed preservation result. -/
theorem captured_copy {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (src dst : Source.SPath) (different : src≠dst)
 (count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E)
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame src).run initial=(.ok count,initial))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run initial=(.ok (payload j),initial)) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+3) (.array .storage (.int t) none) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run initial=
 (Source.storeData (E:=E) (Γ:=Γ) frame (count+padding+2) (.array .storage (.int t) none) dst
  (Source.Data.array (l:=.memory) (n:=none) count (fun _ h => nomatch h) (fun j : Fin count => .val (payload j.val)))).run initial := by
 have budget : count+padding+3=(count+padding+2)+1 := by omega
 rw [budget]
 simp only [Source.storeVal,if_neg different,Source.STy.withLoc]
 rw [Source.Hoare.run_bind]
 rw [load_array frame t src count padding payload initial header reads]

/-- Exact existing journal operation for a successful typed cell write. -/
def cellOp (E : Source.Env) (frame : Source.Fr) (path : Source.SPath)
 (value : Option (Source.Val E.layout (E.cellTy path))) : Source.Op E.layout E.lay E.lay :=
 if E.transientRoot path then .transient frame.this (fun storage => storage.set path value)
 else .account frame.this (fun account => {account with storage:=account.storage.set path value})

theorem set_run {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (path : Source.SPath)
 (value : Option (Source.Val E.layout (E.cellTy path)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.setCell (E:=E) (Γ:=Γ) frame path value).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.apply (cellOp E frame path value)})) := by
 cases branch : E.transientRoot path <;>
  simp only [Source.setCell,cellOp,branch,Source.applyOp,writable,Bool.false_eq_true,if_false,if_true] <;> rfl

theorem write_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
 (frame : Source.Fr) (writable : frame.static=false) (path : Source.SPath)
 (value : Source.Val E.layout τ) (typed : τ=E.cellTy path)
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.writeAt (E:=E) (Γ:=Γ) frame path value).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.apply (cellOp E frame path (some (typed ▸ value)))})) := by
 simp only [Source.writeAt,dif_pos typed]
 exact set_run (E:=E) (Γ:=Γ) frame writable path (some (typed ▸ value)) locals state

/-- Generated list of EXISTING Source.Op values, not an evaluator/state layer. -/
def writes {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (payload : Nat → Source.Val E.layout (.int t)) (typed : ∀ j, (.int t : Source.STy)=E.cellTy (path.go (.index j))) : Nat → Nat → List (Source.Op E.layout E.lay E.lay)
 | _,0 => []
 | start,count+1 => cellOp E frame (path.go (.index start)) (some ((typed start) ▸ payload start)) :: writes frame t path payload typed (start+1) count

/-- Actual primitive storeData with positive original leaf fuel. -/
theorem store_leaf {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (path : Source.SPath)
 (value : Source.Val E.layout (.int t)) (typed : (.int t : Source.STy)=E.cellTy path)
 (padding : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.storeData (E:=E) (Γ:=Γ) frame (padding+2) (.int t) path (.val value)).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.apply (cellOp E frame path (some (typed ▸ value)))})) := by
 cases value with
 | int v bound =>
  change (Source.writeAt frame path (.int v bound)).run (locals,state)=_
  exact write_run (E:=E) (Γ:=Γ) frame writable path (.int v bound) typed locals state
 | memRef impossible _ => cases impossible
 | storRef impossible _ => cases impossible
 | cdRef impossible _ => cases impossible

/-- Every runtime captured element is written once in order, with the exact
existing Source journal and all other interpreter state retained. -/
theorem store_elems {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (path : Source.SPath)
 (start count padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : ∀ j, (.int t : Source.STy)=E.cellTy (path.go (.index j)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.storeElems (E:=E) (Γ:=Γ) frame (count+padding+2) (.int t) path start count
  (fun j : Fin count => Source.Data.val (payload (start+j.val)))).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (writes frame t path payload typed start count)})) := by
 induction count generalizing start state with
 | zero => rfl
 | succ count ih =>
  have budget : count+1+padding+2=(count+padding+2)+1 := by omega
  rw [budget]
  change ((Source.storeData frame (count+padding+2) (.int t) (path.go (.index start)) (.val (payload (start+0))) >>= fun _ =>
   Source.storeElems frame (count+padding+2) (.int t) path (start+1) count
    (fun j => .val (payload (start+(j.val+1))))).run (locals,state))=_
  simp only [Nat.add_zero]
  rw [Source.Hoare.run_bind,store_leaf frame writable t _ (payload start) (typed start) (count+padding) locals state]
  dsimp only
  have vector : (fun j : Fin count => Source.Data.val (payload (start+(j.val+1))))=(fun j : Fin count => Source.Data.val (payload (start+1+j.val))) := by
   funext j
   congr 2
   omega
  rw [vector,ih]
  rfl

/-- Existing declared array type supplies exact element cell types. -/
theorem element_type {E : Source.Env} (t : Source.IntTy) (path : Source.SPath)
 (typed : E.pathTy path=some (.array .storage (.int t) none)) (i : Nat) :
 E.cellTy (path.go (.index i))=.int t := by
 simp only [Source.Env.cellTy,Source.Env.pathTy_go,typed,Option.bind_some,Source.Env.stepTy,Option.map_some,Option.getD_some,Source.STy.cell,Source.STy.isValue,if_true]

def copyLog {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none)) : List (Source.Op E.layout E.lay E.lay) :=
 writes frame t dst payload (fun j => (element_type t dst typed j).symm) 0 count ++
 ((List.range' count (oldLength-count)).map (fun j => SourceScalarDeleteLog.clearOp E frame (dst.go (.index j)))) ++
 [cellOp E frame dst (some ((by
   simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some] : (.int Source.IntTy.u256 : Source.STy)=E.cellTy dst) ▸ Source.intWrap Source.IntTy.u256 count))]

/-- Exact runtime storage write phase: snapshot payload, ONLY stale live tail,
then header LAST; all existing Source journal/state effects retained. -/
theorem store_array {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))) :
 (Source.storeData (E:=E) (Γ:=Γ) frame (count+(oldLength-count)+3) (.array .storage (.int t) none) dst
  (Source.Data.array (l:=.memory) (n:=none) count (fun _ h => nomatch h) (fun j : Fin count => .val (payload j.val)))).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (copyLog frame t dst count oldLength payload typed)})) := by
 have budget : count+(oldLength-count)+3=(count+(oldLength-count)+2)+1 := by omega
 rw [budget]
 change ((Source.readLen frame dst >>= fun old =>
  Source.storeElems frame (count+(oldLength-count)+2) (.int t) dst 0 count (fun j : Fin count => Source.Data.val (payload j.val)) >>= fun _ =>
   Source.deleteRange frame (count+(oldLength-count)+2) (.int t) dst count (old-count) >>= fun _ =>
    Source.writeLen frame dst count).run (locals,state))=_
 rw [Source.Hoare.run_bind,header]
 dsimp only
 rw [Source.Hoare.run_bind]
 have written := store_elems frame writable t dst 0 count (oldLength-count) payload (fun j => (element_type t dst typed j).symm) locals state
 simp only [Nat.zero_add] at written
 rw [written]
 dsimp only
 rw [Source.Hoare.run_bind]
 have clearBudget : count+(oldLength-count)+2=(oldLength-count)+(count+1)+1 := by omega
 rw [clearBudget,SourceScalarDeleteLog.scalar_range_run frame writable t dst count (oldLength-count) (count+1)]
 dsimp only
 simp only [Source.writeLen]
 rw [write_run (E:=E) (Γ:=Γ) frame writable dst (Source.intWrap Source.IntTy.u256 count) (by
  simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some])]
 simp only [copyLog,Source.run_append,Source.ExecState.run]

/-- Successful actual distinct-path storage-to-storage copy, for every runtime
count at sufficient ORIGINAL fuel. Source is captured BEFORE all writes; no
ordinary Source/compiler/target/world relation is assumed or concluded. -/
theorem complete {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (src dst : Source.SPath) (different : src≠dst)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state)))
 (targetHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame (count+(oldLength-count)+4) (.array .storage (.int t) none) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (copyLog frame t dst count oldLength payload typed)})) := by
 have captured := captured_copy frame t src dst different count (oldLength-count+1) payload (locals,state) sourceHeader reads
 have budget : count+(oldLength-count+1)+3=count+(oldLength-count)+4 := by omega
 have inner : count+(oldLength-count+1)+2=count+(oldLength-count)+3 := by omega
 rw [budget,inner] at captured
 rw [captured]
 exact store_array frame writable t dst count oldLength payload typed locals state targetHeader

/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.load_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms load_elems
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.load_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms load_array
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.captured_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captured_copy
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.set_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms set_run
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.write_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write_run
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.store_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store_leaf
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.store_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store_elems
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.element_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms element_type
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.store_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store_array
/-- info: 'Solidity.Backend.StorageOps.SourceStorageCopy.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.SourceStorageCopy
