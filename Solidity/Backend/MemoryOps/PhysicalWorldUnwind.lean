import Solidity.Backend.MemoryOps.PhysicalByteJournal
import Solidity.Backend.Failure.Unwind
import Solidity.Lowering.V08.SourceFailures
import Solidity.Source.World

/-! P6b: actual Source world journal, independent ABI reason execution and the
existing byte emitter/local checkpoint. Projection is record observation only;
Source.run and Source.rollback remain the only world journal operations here.
The evaluator retains its dirty state on revert. Explicit caller rollback is a
SEPARATE conclusion, not transaction/catch/compiler adequacy. No automatic
memory snapshot or global address injection is inferred. -/
namespace Solidity.Backend.MemoryOps.Physical
open Solidity

/-- Observe the actual Source stores in the existing local byte journal.
Source's operation-entry list is deliberately NOT erased by a journal equality:
its exact restoration is separately proved by rollback_run. -/
def worldJournal {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (state : Source.ExecState D L T) (machine : Failure.Slice.Machine) :
    Failure.Local.Journal (Source.World D L) (Source.Transient D T) :=
  ⟨state.world,state.transient,machine⟩

/-- Arbitrary real journal operations, followed by an actual ABI reason emitter.
The local saved world/transient are the INITIAL Source projections; the live
stores are the ACTUAL reached projections. Complete Source journal restoration
is obtained from the published operation journal theorem, not assumed. -/
theorem world_reason_unwind {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy}
    (state : Source.ExecState D L T) (ops : List (Source.Op D L T))
    (this caller : Roadmap.Address) (value : Roadmap.Word) (input : Roadmap.Bytes)
    (static : Bool) (saved live : Failure.Slice.Machine) (a : Nat)
    (reason : Roadmap.Bytes) (hf : Failure.Fits a (Semantics.encodeError reason))
    (hs : live.stack.length+2≤1024) :
    (state.enter this caller value input static).rollback (state.run ops)=state ∧
    Failure.Local.execute (Failure.Local.save (worldJournal state saved)) a (.reason reason)
      (worldJournal (state.run ops) live)=
      some (worldJournal state saved,.revert (Source.errorData reason)) := by
  constructor
  · exact Source.rollback_run state ops this caller value input static
  · rw [Lowering.V08.errorData_transport_total]
    exact Failure.Local.execute_failure _ a (Semantics.encodeError reason) _ hf hs

/-- The emitted terminal reads the complete ABI bytes from the reached memory,
BEFORE restoration, and stops before any supplied suffix. This is real checked
byte-code execution, not a supplied emitter-success premise. -/
theorem reason_live_bytes (a : Nat) (reason : Roadmap.Bytes)
    (live : Failure.Slice.Machine) (suffix : Backend.Program)
    (hf : Failure.Fits a (Semantics.encodeError reason))
    (hs : live.stack.length+2≤1024) :
    Failure.Slice.checkedRun (Failure.emit a (.reason reason) ++ suffix) live=
      some ({live with memory:=Failure.Slice.putBytes live.memory a (Source.errorData reason)},
        some (.revert (Source.errorData reason))) := by
  rw [Lowering.V08.errorData_transport_total]
  exact Failure.checkedRun_emit_suffix a (.reason reason) suffix live hf hs

/-- Actual independent Source syntax at the reached world journal. Revert does
NOT roll back that evaluator state; the explicit caller operation and byte
checkpoint are separately derived alongside it. Other fields of Source.St and
all locals are retained by the actual literal-reason evaluator. -/
theorem source_reason_world_unwind {E : Source.Env} {Γ : Source.RCtx}
    (global : Source.Glob E) (frame : Source.Fr) (horizon : Nat)
    (locals : Source.Locals E.layout Γ) (initial : Source.St E)
    (ops : List (Source.Op E.layout E.lay E.lay))
    (saved live : Failure.Slice.Machine) (a : Nat) (reason : Roadmap.Bytes)
    (hf : Failure.Fits a (Semantics.encodeError reason))
    (hs : live.stack.length+2≤1024) :
    let reached := {initial with ex:=initial.ex.run ops}
    (Source.evalE global frame (horizon+5)
      (Lowering.V08.SourceFailures.reason reason)).run (locals,reached)=
        (.error (.revert (Source.errorData reason)),(locals,reached)) ∧
    (initial.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
      reached.ex=initial.ex ∧
    Failure.Local.execute (Failure.Local.save (worldJournal initial.ex saved)) a (.reason reason)
      (worldJournal reached.ex live)=
      some (worldJournal initial.ex saved,.revert (Source.errorData reason)) := by
  dsimp only
  refine ⟨Lowering.V08.SourceFailures.eval_reason global frame horizon reason locals _,?_⟩
  exact world_reason_unwind initial.ex ops frame.this frame.sender frame.value frame.cd frame.static
    saved live a reason hf hs

/-- Restoration of physical numeric observations comes from the INITIAL caller
frame, even if the emission overlaps it and live Source stores materially differ.
This does not assert a physical encoding for Source accounts/storage. -/
theorem world_reason_restored_frame {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy}
    (state : Source.ExecState D L T) (ops : List (Source.Op D L T))
    (saved live : Failure.Slice.Machine) (m : Evm.Machine) (cells : Nat → Prop)
    (h : WordFrame m saved.memory cells) (a : Nat) (reason : Roadmap.Bytes)
    (hf : Failure.Fits a (Semantics.encodeError reason))
    (hs : live.stack.length+2≤1024) :
    ∃ output, Failure.Local.execute (Failure.Local.save (worldJournal state saved))
      a (.reason reason) (worldJournal (state.run ops) live)=
        some (output,.revert (Source.errorData reason)) ∧
      WordFrame m output.machine.memory cells ∧
      output.machine=saved ∧ output.persistent=state.world ∧ output.transient=state.transient := by
  refine ⟨worldJournal state saved,?_,h,rfl,rfl,rfl⟩
  rw [Lowering.V08.errorData_transport_total]
  exact Failure.Local.execute_failure _ a (Semantics.encodeError reason) _ hf hs

/-- The real evaluator mark, including its actually saved heap field. -/
theorem source_mark {E : Source.Env} {Γ : Source.RCtx}
    (locals : Source.Locals E.layout Γ) (initial : Source.St E) :
    (Source.mark : Source.EM E Γ _).run (locals,initial)=
      (.ok (initial.ex.journal.length,initial.logs.length,initial.heap),(locals,initial)) := rfl

/-- Actual published rollbackTo after arbitrary real world operations and new
logs. Its CURRENT implementation restores the journal and log prefix, but keeps
its reached heap, events and fnLocals. The mark's heap is not silently restored.
Caller byte restoration in the local target checkpoint is a separate interface. -/
theorem source_rollback_to {E : Source.Env} {Γ : Source.RCtx}
    (locals : Source.Locals E.layout Γ) (initial : Source.St E)
    (ops : List (Source.Op E.layout E.lay E.lay))
    (newLogs : List (Roadmap.Address × Roadmap.Bytes)) (liveHeap : Source.Heap E.layout) :
    let reached := {initial with ex:=initial.ex.run ops, logs:=newLogs++initial.logs, heap:=liveHeap}
    (Source.rollbackTo (initial.ex.journal.length,initial.logs.length,initial.heap) :
      Source.EM E Γ Unit).run (locals,reached)=
        (.ok (),(locals,{initial with heap:=liveHeap})) := by
  dsimp only
  change (Except.ok (), (locals,
    {initial with ex:=((initial.ex.run ops).undoN ((initial.ex.run ops).journal.length-initial.ex.journal.length)), logs:=((newLogs++initial.logs).drop ((newLogs++initial.logs).length-initial.logs.length)), heap:=liveHeap})) = _
  rw [Source.ExecState.journal_run]
  have count : initial.ex.journal.length+ops.length-initial.ex.journal.length=ops.length := by omega
  rw [count,Source.ExecState.undoN_run,List.length_append]
  have logCount : newLogs.length+initial.logs.length-initial.logs.length=newLogs.length := by omega
  rw [logCount,List.drop_left]

/-- The caller checkpoint is the actual output of the paired store prefix.
The restored word machine is that prefix's reached machine; no frame on an
arbitrary saved caller is a premise. World/transient changes remain the actual
published journal operations, with no Source heap encoding asserted. -/
theorem world_reason_saved_store {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy}
    (state : Source.ExecState D L T) (ops : List (Source.Op D L T))
    (m : Evm.Machine) (bytes : Environment.Memory) (cells : Nat → Prop)
    (cell w : Fin Evm.W) (tail : List Roadmap.Word)
    (initial : WordFrame m bytes cells) (fits : 32*cell.val+32≤2^256)
    (live : Failure.Slice.Machine) (a : Nat) (reason : Roadmap.Bytes)
    (hf : Failure.Fits a (Semantics.encodeError reason))
    (hs : live.stack.length+2≤1024) :
    let word := Evm.Memory.writeMachine m cell.val (.val w)
    let savedBytes := Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val)
    let saved : Failure.Slice.Machine := ⟨tail,savedBytes⟩
    Evm.run [.mstoreAt] ((m.push (.val w)).push (.val cell))=.ok word 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU (32*cell.val) (by change 32*cell.val<2^256;omega)::
        lenU w.val w.isLt::tail.map (fun (v : Roadmap.Word) => lenU v.val v.isLt),bytes⟩=
        some ⟨tail.map (fun (v : Roadmap.Word) => lenU v.val v.isLt),savedBytes⟩ ∧
    ∃ output, Failure.Local.execute (Failure.Local.save (worldJournal state saved))
      a (.reason reason) (worldJournal (state.run ops) live)=
        some (output,.revert (Source.errorData reason)) ∧
      WordFrame word output.machine.memory (fun c => cells c ∨ c=cell.val) ∧
      output.machine=saved ∧ output.persistent=state.world ∧ output.transient=state.transient := by
  dsimp only
  have store := checkpoint_mstore_frame state.world state.transient
    m bytes cells cell w tail (worldJournal (state.run ops) live) (Source.errorData reason) fits initial
  refine ⟨store.1,store.2.1,worldJournal state _,?_,store.2.2,rfl,rfl,rfl⟩
  rw [Lowering.V08.errorData_transport_total]
  exact Failure.Local.execute_failure _ a (Semantics.encodeError reason) _ hf hs

/-- info: 'Solidity.Backend.MemoryOps.Physical.world_reason_saved_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_reason_saved_store

/-- info: 'Solidity.Backend.MemoryOps.Physical.source_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_mark
/-- info: 'Solidity.Backend.MemoryOps.Physical.source_rollback_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_rollback_to
/-- info: 'Solidity.Backend.MemoryOps.Physical.world_reason_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_reason_unwind
/-- info: 'Solidity.Backend.MemoryOps.Physical.reason_live_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reason_live_bytes
/-- info: 'Solidity.Backend.MemoryOps.Physical.source_reason_world_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_reason_world_unwind
/-- info: 'Solidity.Backend.MemoryOps.Physical.world_reason_restored_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_reason_restored_frame
end Solidity.Backend.MemoryOps.Physical
