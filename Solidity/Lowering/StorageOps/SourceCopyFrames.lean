import Solidity.Lowering.StorageOps.SourceStorageCopy

/-! Frames of the ACTUAL generated Source storage-copy operation log.
Typed paths, reads, Source.Op, journal and explicit rollback are unchanged.
No automatic rollback, journal commutation or Source/target relation follows. -/
namespace Solidity.Backend.StorageOps.SourceCopyFrames
open SourceStorageCopy

theorem cell_other {E : Source.Env} (frame : Source.Fr)
 (state : Source.ExecState E.layout E.lay E.lay) (path query : Source.SPath)
 (value : Option (Source.Val E.layout (E.cellTy path))) (different : query≠path) :
 ((state.apply (cellOp E frame path value)).world.accounts frame.this).storage.read query=(state.world.accounts frame.this).storage.read query ∧
 ((state.apply (cellOp E frame path value)).transient.cells frame.this).read query=(state.transient.cells frame.this).read query := by
 cases branch : E.transientRoot path <;>
  simp only [cellOp,branch,Bool.false_eq_true,if_false,if_true,Source.ExecState.apply,
   Source.World.set,Source.Transient.set,dif_pos,and_true,true_and] <;>
  simp only [Source.Storage.set,Source.Storage.read,different,dif_neg,not_false_eq_true]

theorem writes_other {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (path query : Source.SPath)
 (payload : Nat → Source.Val E.layout (.int t))
 (typed : ∀ j, (.int t : Source.STy)=E.cellTy (path.go (.index j)))
 (start count : Nat) (state : Source.ExecState E.layout E.lay E.lay)
 (untouched : ∀ j<count,query≠path.go (.index (start+j))) :
 ((state.run (writes frame t path payload typed start count)).world.accounts frame.this).storage.read query=(state.world.accounts frame.this).storage.read query ∧
 ((state.run (writes frame t path payload typed start count)).transient.cells frame.this).read query=(state.transient.cells frame.this).read query := by
 induction count generalizing start state with
 | zero => exact ⟨rfl,rfl⟩
 | succ count ih =>
  have first := cell_other frame state (path.go (.index start)) query (some ((typed start) ▸ payload start)) (by simpa only [Nat.add_zero] using untouched 0 (by omega))
  have rest := ih (start+1) (state.apply (cellOp E frame (path.go (.index start)) (some ((typed start) ▸ payload start)))) (by
   intro j member
   have apart := untouched (j+1) (by omega)
   simpa only [Nat.add_assoc,Nat.add_comm j 1] using apart)
  exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩

theorem copy_other {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (dst query : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (state : Source.ExecState E.layout E.lay E.lay)
 (header : query≠dst) (written : ∀ j<count,query≠dst.go (.index j))
 (cleared : ∀ j ∈ List.range' count (oldLength-count),query≠dst.go (.index j)) :
 ((state.run (copyLog frame t dst count oldLength payload typed)).world.accounts frame.this).storage.read query=(state.world.accounts frame.this).storage.read query ∧
 ((state.run (copyLog frame t dst count oldLength payload typed)).transient.cells frame.this).read query=(state.transient.cells frame.this).read query := by
 have first := writes_other frame t dst query payload (fun j => (element_type t dst typed j).symm) 0 count state (by simpa only [Nat.zero_add] using written)
 have tail := SourceScalarDeleteLog.clear_log_other frame
  (state.run (writes frame t dst payload (fun j => (element_type t dst typed j).symm) 0 count)) dst query (List.range' count (oldLength-count)) cleared
 unfold copyLog
 rw [Source.run_append,Source.run_append]
 have last := cell_other frame
  ((state.run (writes frame t dst payload (fun j => (element_type t dst typed j).symm) 0 count)).run
   ((List.range' count (oldLength-count)).map (fun j => SourceScalarDeleteLog.clearOp E frame (dst.go (.index j)))))
  dst query (some ((by simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some] : (.int Source.IntTy.u256 : Source.STy)=E.cellTy dst) ▸ Source.intWrap Source.IntTy.u256 count)) header
 exact ⟨last.1.trans (tail.1.trans first.1),last.2.trans (tail.2.trans first.2)⟩

theorem writes_length {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (payload : Nat → Source.Val E.layout (.int t))
 (typed : ∀ j, (.int t : Source.STy)=E.cellTy (path.go (.index j))) (start count : Nat) :
 (writes frame t path payload typed start count).length=count := by
 induction count generalizing start with
 | zero => rfl
 | succ count ih => simp only [writes,List.length_cons,ih]

theorem log_length {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none)) :
 (copyLog frame t dst count oldLength payload typed).length=count+(oldLength-count)+1 := by
 simp only [copyLog,List.length_append,writes_length,List.length_map,List.length_range',List.length_singleton]

theorem journal {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (state : Source.ExecState E.layout E.lay E.lay) :
 (state.run (copyLog frame t dst count oldLength payload typed)).journal.length=
 state.journal.length+(count+(oldLength-count)+1) := by
 rw [Source.ExecState.journal_run,log_length]

/-- Restore requires explicitly applying the actual entered-frame rollback. -/
theorem rollback {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (dst : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (state : Source.ExecState E.layout E.lay E.lay) (input : Roadmap.Bytes) :
 (state.enter frame.this frame.sender frame.value input frame.static).rollback
  (state.run (copyLog frame t dst count oldLength payload typed))=state :=
 Source.rollback_run state _ frame.this frame.sender frame.value input frame.static

/-- Exact typed outcomes include success, missing and type mismatch, with the
AFTER state retained; the operation is not identified with its OLD state. -/
theorem readAt {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr) (t : Source.IntTy) (dst query : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) (τ : Source.STy)
 (header : query≠dst) (written : ∀ j<count,query≠dst.go (.index j))
 (cleared : ∀ j ∈ List.range' count (oldLength-count),query≠dst.go (.index j)) :
 let after := {state with ex:=state.ex.run (copyLog frame t dst count oldLength payload typed)}
 (Source.readAt (E:=E) (Γ:=Γ) frame query τ).run (locals,after)=
 (((Source.readAt (E:=E) (Γ:=Γ) frame query τ).run (locals,state)).1,(locals,after)) := by
 have same := copy_other frame t dst query count oldLength payload typed state.ex header written cleared
 exact SourceReadFrames.readAt_transport frame query τ locals state _ same.1 same.2

theorem readLen {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr) (t : Source.IntTy) (dst query : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (header : query≠dst) (written : ∀ j<count,query≠dst.go (.index j))
 (cleared : ∀ j ∈ List.range' count (oldLength-count),query≠dst.go (.index j)) :
 let after := {state with ex:=state.ex.run (copyLog frame t dst count oldLength payload typed)}
 (Source.readLen (E:=E) (Γ:=Γ) frame query).run (locals,after)=
 (((Source.readLen (E:=E) (Γ:=Γ) frame query).run (locals,state)).1,(locals,after)) := by
 have same := copy_other frame t dst query count oldLength payload typed state.ex header written cleared
 exact SourceReadFrames.readLen_transport frame query locals state _ same.1 same.2

theorem readCell {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr) (t : Source.IntTy) (dst query : Source.SPath)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (header : query≠dst) (written : ∀ j<count,query≠dst.go (.index j))
 (cleared : ∀ j ∈ List.range' count (oldLength-count),query≠dst.go (.index j)) :
 let after := {state with ex:=state.ex.run (copyLog frame t dst count oldLength payload typed)}
 (Source.readCell (E:=E) (Γ:=Γ) frame query).run (locals,after)=
 (((Source.readCell (E:=E) (Γ:=Γ) frame query).run (locals,state)).1,(locals,after)) := by
 have same := copy_other frame t dst query count oldLength payload typed state.ex header written cleared
 exact SourceReadFrames.readCell_transport frame query locals state _ same.1 same.2

/-- A subsequent disjoint runtime primitive snapshot reads exactly the OLD
payload, while retaining the actual AFTER copy state and journal. -/
theorem snapshot {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr) (t qType : Source.IntTy) (dst query : Source.SPath)
 (count oldLength qCount padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (observed : Nat → Source.Val E.layout (.int qType))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (outside : ∀ probe,probe=query ∨ (∃ j<qCount,probe=query.go (.index j)) →
  probe≠dst ∧ (∀ j<count,probe≠dst.go (.index j)) ∧ (∀ j ∈ List.range' count (oldLength-count),probe≠dst.go (.index j)))
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame query).run (locals,state)=(.ok qCount,(locals,state)))
 (reads : ∀ j<qCount,(Source.readAt (E:=E) (Γ:=Γ) frame (query.go (.index j)) (.int qType)).run (locals,state)=(.ok (observed j),(locals,state))) :
 let after := {state with ex:=state.ex.run (copyLog frame t dst count oldLength payload typed)}
 (Source.loadMem (E:=E) (Γ:=Γ) frame (qCount+padding+2) (.array .memory (.int qType) none) query).run (locals,after)=
 (.ok (Source.Data.array (l:=.memory) (n:=none) qCount (fun _ h => nomatch h) (fun j : Fin qCount => .val (observed j.val))),(locals,after)) := by
 have h := outside query (Or.inl rfl)
 have newHeader := readLen frame t dst query count oldLength payload typed locals state h.1 h.2.1 h.2.2
 rw [header] at newHeader
 apply load_array frame qType query qCount padding observed _ newHeader
 intro j member
 have apart := outside (query.go (.index j)) (Or.inr ⟨j,member,rfl⟩)
 have next := readAt frame t dst (query.go (.index j)) count oldLength payload typed locals state (.int qType) apart.1 apart.2.1 apart.2.2
 rw [reads j member] at next
 exact next

/-- The actual Source operation derives frames and the exact journal from
OLD read facts. Rollback here is explicitly applied, never inferred from a halt. -/
theorem actual {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (src dst query : Source.SPath) (different : src≠dst)
 (count oldLength : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) (τ : Source.STy) (input : Roadmap.Bytes)
 (sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state)))
 (targetHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state)))
 (header : query≠dst) (written : ∀ j<count,query≠dst.go (.index j))
 (cleared : ∀ j ∈ List.range' count (oldLength-count),query≠dst.go (.index j)) :
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+(oldLength-count)+4) (.array .storage (.int t) none) dst
  (Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run (locals,state)
 result.1=.ok () ∧
 ((Source.readAt (E:=E) (Γ:=Γ) frame query τ).run result.2).1=((Source.readAt (E:=E) (Γ:=Γ) frame query τ).run (locals,state)).1 ∧
 result.2.2.ex.journal.length=state.ex.journal.length+(count+(oldLength-count)+1) ∧
 (state.ex.enter frame.this frame.sender frame.value input frame.static).rollback result.2.2.ex=state.ex ∧
 result.2.2.heap=state.heap := by
 rw [SourceStorageCopy.complete frame writable t src dst different count oldLength payload typed locals state sourceHeader reads targetHeader]
 refine ⟨rfl,?_,journal frame t dst count oldLength payload typed state.ex,rollback frame t dst count oldLength payload typed state.ex input,rfl⟩
 have same := readAt frame t dst query count oldLength payload typed locals state τ header written cleared
 have outcome := congrArg Prod.fst same
 exact outcome

/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.cell_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cell_other
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.writes_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms writes_other
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.copy_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_other
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.writes_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms writes_length
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.log_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms log_length
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.journal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms journal
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rollback
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.readAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms readAt
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.readLen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms readLen
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.readCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms readCell
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms snapshot
/-- info: 'Solidity.Backend.StorageOps.SourceCopyFrames.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms actual
end Solidity.Backend.StorageOps.SourceCopyFrames
