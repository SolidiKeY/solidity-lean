import Solidity.Yul.Views.RetainedLoopSequenceCheckpoint

/-! Explicit checkpoint rollback for any finite list of actual Source applyOp
runs followed by ordinary halt. Empty batches keep the requested halt even in
static mode; nonempty static batches refuse before their first operation. Only
this explicit adapter invokes rollback. No arbitrary heap/call rollback or
residual-complement recovery is inferred. -/
namespace Solidity.Yul.Views.RetainedLoopBatchCheckpoint

def applyOpsThenHalt {E Γ} (F : Source.Fr) (operations : List (Source.Op E.layout E.lay E.lay))
    (error : Source.Halt) : Source.EM E Γ Unit :=
  match operations with
  | [] => Source.EM.halt error
  | operation::rest => do
    Source.applyOp F operation
    applyOpsThenHalt F rest error

def rollbackBatch {E Γ} (F : Source.Fr) (operations : List (Source.Op E.layout E.lay E.lay))
    (state : Source.EMState E Γ) (error : Source.Halt) : Except Source.Halt Unit × Source.EMState E Γ :=
  let reached := (applyOpsThenHalt (E:=E) (Γ:=Γ) F operations error).run state
  let checkpoint := state.2.ex.enter F.this F.sender F.value F.cd F.static
  (reached.1,(reached.2.1,{reached.2.2 with ex := checkpoint.rollback reached.2.2.ex}))

theorem run_nonstatic {E Γ} (F : Source.Fr) (operations : List (Source.Op E.layout E.lay E.lay))
    (state : Source.EMState E Γ) (error : Source.Halt) (static : F.static=false) :
    (applyOpsThenHalt F operations error).run state=
      (.error error,(state.1,{state.2 with ex := state.2.ex.run operations})) := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
    simp only [applyOpsThenHalt,Source.Hoare.run_bind,actualApplyOp_run,static,Bool.false_eq_true,if_false]
    exact ih (state.1,{state.2 with ex := state.2.ex.apply operation})

theorem run_static_cons {E Γ} (F : Source.Fr) (first : Source.Op E.layout E.lay E.lay)
    (rest : List (Source.Op E.layout E.lay E.lay))
    (state : Source.EMState E Γ) (error : Source.Halt) (static : F.static=true) :
    (applyOpsThenHalt F (first::rest) error).run state=(.error (.revert []),state) := by
  simp only [applyOpsThenHalt,Source.Hoare.run_bind,actualApplyOp_run,static,if_true]

theorem rollback_result {E Γ} (F : Source.Fr) (operations : List (Source.Op E.layout E.lay E.lay))
    (state : Source.EMState E Γ) (error : Source.Halt) :
    rollbackBatch F operations state error=
      (if F.static && !operations.isEmpty then .error (.revert []) else .error error,state) := by
  unfold rollbackBatch
  cases mode : F.static
  · rw [run_nonstatic F operations state error mode]
    simp only [Bool.false_and,Bool.false_eq_true,if_false]
    rw [Source.rollback_run state.2.ex operations F.this F.sender F.value F.cd false]
  · cases operations with
    | nil =>
      have undo := Source.rollback_run state.2.ex [] F.this F.sender F.value F.cd true
      change (state.2.ex.enter F.this F.sender F.value F.cd true).rollback state.2.ex=state.2.ex at undo
      change ((Except.error error : Except Source.Halt Unit),(state.1,{state.2 with ex := (state.2.ex.enter F.this F.sender F.value F.cd true).rollback state.2.ex}))=(.error error,state)
      rw [undo]
    | cons first rest =>
      rw [run_static_cons F first rest state error mode]
      have undo := Source.rollback_run state.2.ex [] F.this F.sender F.value F.cd true
      change (state.2.ex.enter F.this F.sender F.value F.cd true).rollback state.2.ex=state.2.ex at undo
      change ((Except.error (.revert []) : Except Source.Halt Unit),(state.1,{state.2 with ex := (state.2.ex.enter F.this F.sender F.value F.cd true).rollback state.2.ex}))=(.error (.revert []),state)
      rw [undo]

end Solidity.Yul.Views.RetainedLoopBatchCheckpoint
