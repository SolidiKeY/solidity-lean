import Solidity.Yul.Views.RetainedLoopCheckpoint
import Solidity.Yul.Views.RetainedLoopSequence

/-! Explicit Source checkpoint rollback after two actual primitive writes and
an ordinary halt. This restores Source state only; reencoding an old raw map
still uses its original saved complement. No residual-journal or call adequacy
is inferred, and no halt automatically invokes this adapter. -/
namespace Solidity.Yul.Views.RetainedLoopSequenceCheckpoint

def rollbackSequence {E Γ} (F : Source.Fr) (first second : Source.Op E.layout E.lay E.lay)
    (state : Source.EMState E Γ) (error : Source.Halt) : Except Source.Halt Unit × Source.EMState E Γ :=
  let reached := (RetainedLoopSequence.writeTwiceThenHalt (E:=E) (Γ:=Γ) F first second error).run state
  let checkpoint := state.2.ex.enter F.this F.sender F.value F.cd F.static
  (reached.1,(reached.2.1,{reached.2.2 with ex := checkpoint.rollback reached.2.2.ex}))

/-- The original pre-sequence checkpoint restores the whole Source state;
nonstatic late halt or static early refusal retains its actual error. -/
theorem rollback_result {E Γ} (F : Source.Fr) (first second : Source.Op E.layout E.lay E.lay)
    (state : Source.EMState E Γ) (error : Source.Halt) :
    rollbackSequence F first second state error=
      if F.static then (.error (.revert []),state) else (.error error,state) := by
  unfold rollbackSequence
  cases mode : F.static
  · rw [RetainedLoopSequence.run F first second state error mode]
    simp only [Bool.false_eq_true,if_false]
    have undo := Source.rollback_run state.2.ex [first,second] F.this F.sender F.value F.cd false
    change (state.2.ex.enter F.this F.sender F.value F.cd false).rollback
      ((state.2.ex.apply first).apply second)=state.2.ex at undo
    rw [undo]
  · simp only [RetainedLoopSequence.writeTwiceThenHalt,Source.Hoare.run_bind,actualApplyOp_run,mode,if_true]
    have undo := Source.rollback_run state.2.ex [] F.this F.sender F.value F.cd true
    change (state.2.ex.enter F.this F.sender F.value F.cd true).rollback state.2.ex=state.2.ex at undo
    rw [undo]

end Solidity.Yul.Views.RetainedLoopSequenceCheckpoint
