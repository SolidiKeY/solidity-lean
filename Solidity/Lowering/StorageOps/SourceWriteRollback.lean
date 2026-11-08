import Solidity.Lowering.StorageOps.SourceWordWrite

/-! Captured Source cell operations and an explicitly invoked rollbackTo.
A halt retains the state. This trace leaves heap, events, function locals and
locals unchanged; rollbackTo does not generally restore those fields.
Frame premises do not establish a Source AST call sequence or target/compiler
preservation. No ExtCall is constructed. -/
namespace Solidity.Lowering.StorageOps.SourceWriteRollback
open Solidity

def refusedAfter {E : Source.Env} {Γ : Source.RCtx}
    (writer rejector : Source.Fr) (p : Source.SPath)
    (v : Source.Val E.layout (E.cellTy p)) (q : Source.SPath)
    (w : Source.Val E.layout (E.cellTy q)) : Source.EM E Γ Unit := do
  Source.writeAt writer p v
  Source.writeAt rejector q w

theorem static_write : ∀ {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath)
    (value : Source.Val E.layout (E.cellTy path))
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (_static : frame.static=true),
    (Source.writeAt frame path value : Source.EM E Γ Unit).run (locals,state)=
      (.error (.revert []),(locals,state)) := by
  intro E Γ frame path value locals state static
  cases root : E.transientRoot path <;>
    simp only [Source.writeAt,Source.setCell,root,↓reduceIte,Source.applyOp,static] <;> rfl

/-- Exact restoration for this account-write-only poststate. The original
heap/events/locals survive because the write never changed them. The mark's
heap component is not a heap restoration theorem. No path-distinctness or
empty initial journal/log premise is needed. -/
theorem rollback_once : ∀ {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath)
    (value : Source.Val E.layout (E.cellTy path))
    (locals : Source.Locals E.layout Γ) (state : Source.St E),
    (Source.rollbackTo (state.ex.journal.length,state.logs.length,state.heap) : Source.EM E Γ Unit).run
      (locals,SourceWordWrite.after frame path value state)=
      (.ok (),(locals,state)) := by
  intro E Γ frame path value locals state
  change
    ((Except.ok () : Except Source.Halt Unit), (locals,
      {state with
        ex := Source.ExecState.undoN
          ((state.ex.apply (SourceWordWrite.op frame path value)).journal.length-state.ex.journal.length)
          (state.ex.apply (SourceWordWrite.op frame path value)),
        logs := state.logs.drop (state.logs.length-state.logs.length)})) =
    ((Except.ok () : Except Source.Halt Unit), (locals,state))
  rw [Source.ExecState.journal_apply,Nat.add_sub_cancel_left,Nat.sub_self,List.drop_zero]
  simp only [Source.ExecState.undoN,Source.ExecState.undo_apply]

/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollback.static_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms static_write
/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollback.rollback_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollback_once
/-- Static refusal after a captured ordinary write retains that write without implicit rollback. -/
theorem run_refused {E : Source.Env} {Γ : Source.RCtx}
    (writer rejector : Source.Fr) (p : Source.SPath)
    (v : Source.Val E.layout (E.cellTy p)) (q : Source.SPath)
    (w : Source.Val E.layout (E.cellTy q))
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (writable : writer.static=false) (ordinary : E.transientRoot p=false)
    (static : rejector.static=true) :
    (refusedAfter writer rejector p v q w : Source.EM E Γ Unit).run (locals,state)=
      (.error (.revert []),(locals,SourceWordWrite.after writer p v state)) := by
  unfold refusedAfter
  rw [Source.Hoare.run_bind,
    SourceWordWrite.source_write writer p v locals state writable ordinary]
  exact static_write rejector q w locals (SourceWordWrite.after writer p v state) static

/-- info: 'Solidity.Lowering.StorageOps.SourceWriteRollback.run_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_refused
end Solidity.Lowering.StorageOps.SourceWriteRollback
