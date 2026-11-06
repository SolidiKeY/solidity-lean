import Solidity.Lowering.V08.SourceTransientBytesEmitControls

/-! Source-only component, kernel-checked by the build: G23 / Backfill B repeated source end/re-entry application.
No source transaction interpreter is introduced. Each end is the explicit
published endTx adapter; evalE is the independent published source execution.
A caller must still justify that a real transaction reaches these boundaries.
No SourceSpec, intrinsic-frame, log rollback or bytecode adequacy is claimed. -/
namespace Solidity.Lowering.V08.SourceTransientReentry
open Solidity Source
open SourceEmitControls
open SourceTransientBytesEmitControls (completed encoded eventSelector)

/-- A next invocation starts only after the explicit source end operation. -/
def nextOpening (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (completed pipeline bytes)
def nextWritten (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.transientUpdate (nextOpening pipeline bytes) self scratch (.bool true)
def nextEnded (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Source.St E :=
  SourceTransient.endExecution (nextWritten pipeline bytes)

/-- Generic actual typed write after end; no whole-trace premise. -/
theorem write_after_end {D : Source.Env} {Γ : RCtx} (fr : Fr) (path : Source.SPath)
    (transient : D.transientRoot path = true) (ordinary : fr.static = false)
    (value : Source.Val D.layout (D.cellTy path)) (ls : Source.Locals D.layout Γ)
    (state : Source.St D) :
    (Source.writeAt fr path value : Source.EM D Γ _).run
      (ls,SourceTransient.endExecution state) =
      (.ok (),(ls,SourceTransient.transientUpdate
        (SourceTransient.endExecution state) fr.this path value)) :=
  SourceTransient.transient_write fr path transient ordinary value ls
    (SourceTransient.endExecution state)

/-- Actual resolved assignment executes at the genuinely reached reset machine. -/
theorem reentry_assignment (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 4 SourceTransientEmitControls.setScratch).run
      (locals,nextOpening pipeline bytes) =
      (.ok (.val (.bool true)),(locals,nextWritten pipeline bytes)) := rfl

theorem reentry_read (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,nextWritten pipeline bytes) =
      (.ok (.val (.bool true)),(locals,nextWritten pipeline bytes)) := rfl

theorem second_end_read (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,nextEnded pipeline bytes) =
      (.ok (.val (.bool false)),(locals,nextEnded pipeline bytes)) := rfl

theorem static_reentry (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=true} 4
      SourceTransientEmitControls.setScratch).run (locals,nextOpening pipeline bytes) =
      (.error (.revert []),(locals,nextOpening pipeline bytes)) := rfl

theorem zero_reentry (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 0 SourceTransientEmitControls.setScratch).run
      (locals,nextOpening pipeline bytes) =
      (.error .timeout,(locals,nextOpening pipeline bytes)) := rfl

/-- Explicit undo restores the reached next-opening snapshot, not the old dirty
completed state. Neither undo nor end implicitly erases the retained log/heap. -/
theorem undo_reentry (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    {nextWritten pipeline bytes with ex:=(nextWritten pipeline bytes).ex.undo} =
      nextOpening pipeline bytes :=
  SourceTransient.transient_undo (nextOpening pipeline bytes) self scratch (.bool true)

/-- All old byte-event vector fields are retained, with each changed transient
and journal boundary separately recorded. Complete payload is never projected away. -/
theorem complete_boundary_vector (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((nextEnded pipeline bytes).ex.world.accounts sender).balance.val = 93 ∧
    ((nextEnded pipeline bytes).ex.world.accounts self).balance.val = 7 ∧
    ((nextEnded pipeline bytes).ex.world.accounts self).code = some 0 ∧
    ((nextEnded pipeline bytes).ex.world.accounts self).nonce = 1 ∧
    ((nextEnded pipeline bytes).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    ((nextOpening pipeline bytes).ex.transient.cells self).read scratch = some (.bool false) ∧
    ((nextWritten pipeline bytes).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((nextWritten pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    ((nextEnded pipeline bytes).ex.transient.cells self).read scratch = some (.bool false) ∧
    ((nextEnded pipeline bytes).ex.transient.cells sender).read scratch = some (.bool false) ∧
    (nextOpening pipeline bytes).ex.journal.length = 0 ∧
    (nextWritten pipeline bytes).ex.journal.length = 1 ∧
    (nextEnded pipeline bytes).ex.journal.length = 0 ∧
    (nextEnded pipeline bytes).heap.next = 2 ∧
    (nextEnded pipeline bytes).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (nextEnded pipeline bytes).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (nextEnded pipeline bytes).events = populated.events ∧
    (nextEnded pipeline bytes).logs =
      (self,eventSelector pipeline ++ encoded bytes) :: populated.logs ∧
    (nextEnded pipeline bytes).fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Distinguishes reset from reusing the preceding invocation's dirty snapshot. -/
theorem wrong_dirty_reuse (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    nextOpening pipeline bytes ≠ completed pipeline bytes := by
  intro same
  have counts := congrArg (fun state : Source.St E => state.ex.journal.length) same
  change 0 = 2 at counts
  cases counts

/-- The prior caller's transient cell cannot be smuggled into the new epoch. -/
theorem wrong_caller_transient (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ((nextWritten pipeline bytes).ex.transient.cells sender).read scratch ≠
      some (.bool true) := by
  change some (.bool false : Source.Val E.layout .bool) ≠ some (.bool true)
  intro same
  cases same

/-- Inhabited client: the first invocation is the actual existing resolved
item execution, not an assumed completed-state equation. Explicit end separates
it from actual next-invocation assignment/read, then the second explicit end.
This conjunction records each result and complete reached source machine. -/
theorem reached_client (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (SourceTransientBytesEmitControls.execution pipeline false bytes).run
      (Source.L0 E,SourceTransientEmitControls.opening) =
      (.ok (.normal locals),(Source.L0 E,completed pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 4 SourceTransientEmitControls.setScratch).run
      (locals,nextOpening pipeline bytes) =
      (.ok (.val (.bool true)),(locals,nextWritten pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,nextWritten pipeline bytes) =
      (.ok (.val (.bool true)),(locals,nextWritten pipeline bytes)) ∧
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,nextEnded pipeline bytes) =
      (.ok (.val (.bool false)),(locals,nextEnded pipeline bytes)) :=
  ⟨SourceTransientBytesEmitControls.sequence_complete pipeline bytes 0,
    reentry_assignment pipeline bytes,reentry_read pipeline bytes,second_end_read pipeline bytes⟩

/-- No payload admission bound: arbitrary bytes above, with empty/binary/33-byte
inhabited clients below; the full machine observations remain in reached_client. -/
theorem payload_witnesses (pipeline : Roadmap.Pipeline) :
    ((nextEnded pipeline []).heap.get 1 = some ⟨.bytes .memory,.bytes []⟩) ∧
    ((nextEnded pipeline binary).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩) ∧
    ((nextEnded pipeline SourceTransientBytesEmitControls.boundary33).heap.get 1 =
      some ⟨.bytes .memory,.bytes SourceTransientBytesEmitControls.boundary33⟩) :=
  ⟨rfl,rfl,rfl⟩

#print axioms reached_client
#print axioms payload_witnesses

#print axioms write_after_end
#print axioms reentry_assignment
#print axioms reentry_read
#print axioms second_end_read
#print axioms static_reentry
#print axioms zero_reentry
#print axioms undo_reentry
#print axioms complete_boundary_vector
#print axioms wrong_dirty_reuse
#print axioms wrong_caller_transient
end Solidity.Lowering.V08.SourceTransientReentry
