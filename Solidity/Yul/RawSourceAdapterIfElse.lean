import Solidity.Yul.RawSourceAdapterLoop

/-! Actual Source if/else composition over syntax-indexed executable adapters.
Source agreement retains the real coherent-input premise. -/
namespace Solidity.Yul.RawSourceAdapterIfElse

def run {ctx returns modifier u condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawSourceAdapter.Adapter ctx returns modifier u yes)
    (two : RawSourceAdapter.Adapter ctx returns modifier u no)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := RawCondition.eval test n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok choice => if choice then one.run n first.2 else two.run n first.2

theorem source_selected {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (yes no : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state next : Solidity.Yul.RawFrame.State ctx) (choice : Bool)
    (result : Solidity.Source.R Solidity.Yul.RawLoopBody.Flow × Solidity.Yul.RawFrame.State ctx)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.ok (.val (.bool choice)),(next.clean,next.world)))
    (branch : (Solidity.Source.execS glob frame fuel nps ph
      (if choice then yes else no) next.clean).run (Solidity.Source.L0 ctx.env,next.world) =
        Solidity.Yul.RawLoopBody.represented result) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.ifElse condition yes no) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) = Solidity.Yul.RawLoopBody.represented result := by
  cases choice with
  | false =>
    simp only [Bool.false_eq_true,if_false] at branch
    rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,Solidity.Yul.RawCondition.sub_bool condition glob frame fuel state.clean next.clean state.world next.world false actual]
    change (do
      let out ← Solidity.Source.execS glob frame fuel nps ph no next.clean
      Solidity.Source.EM.lift out.close).run (Solidity.Source.L0 ctx.env,next.world) = _
    rw [Solidity.Source.Hoare.run_bind,branch]
    cases tag : result.1 <;> simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawControlSequence.close_self,Solidity.Source.EM.lift] <;> rfl
  | true =>
    simp only [if_true] at branch
    rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,Solidity.Yul.RawCondition.sub_bool condition glob frame fuel state.clean next.clean state.world next.world true actual]
    change (do
      let out ← Solidity.Source.execS glob frame fuel nps ph yes next.clean
      Solidity.Source.EM.lift out.close).run (Solidity.Source.L0 ctx.env,next.world) = _
    rw [Solidity.Source.Hoare.run_bind,branch]
    cases tag : result.1 <;> simp only [Solidity.Yul.RawLoopBody.represented,tag,Except.map,Solidity.Yul.RawControlSequence.close_self,Solidity.Source.EM.lift] <;> rfl

theorem source_error {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier u : Bool}
    (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
    (yes no : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : Solidity.Yul.RawFrame.State ctx)
    (next : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
      (.error halt,(next,world))) :
    (Solidity.Source.execS glob frame (fuel+1) nps ph
      (Solidity.Source.RStmt.ifElse condition yes no) state.clean).run
      (Solidity.Source.L0 ctx.env,state.world) =
        (.error halt,(Solidity.Source.L0 ctx.env,world)) := by
  first
  | simp only [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,Solidity.Yul.RawCondition.sub_error condition glob frame fuel state.clean next state.world world halt actual]
  | decide
  | omega
  | rfl

theorem correct {ctx returns modifier u condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawSourceAdapter.Adapter ctx returns modifier u yes)
    (two : RawSourceAdapter.Adapter ctx returns modifier u no)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run test one two fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.ifElse condition yes no) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          RawLoopBody.represented (run test one two fuel state) := by
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have conditionRun := RawCondition.source_eval test glob frame fuel state same
    cases actual : (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) with
    | mk tag next =>
      rcases next with ⟨locals,world⟩
      rw [actual] at conditionRun
      let nextFrame : RawFrame.State ctx :=
        RawCoherent.capture state (LocalState.ofClean (locals,world))
      have nextSame : RawCoherent.coherent nextFrame = true :=
        RawCoherent.capture_coherent state locals world
      have nextClean : nextFrame.clean = locals := by
        simp only [nextFrame, RawCoherent.capture, LocalState.ofClean,
          LocalValues.clean_ofClean, Option.getD_some]
      cases tag with
      | error halt =>
        change RawCondition.eval test fuel state = (.error halt,nextFrame) at conditionRun
        simp only [run, conditionRun]
        exact ⟨nextSame, source_error condition yes no glob frame fuel nps ph state locals world halt actual⟩
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool choice =>
            cases choice with
            | false =>
              change RawCondition.eval test fuel state = (.ok false,nextFrame) at conditionRun
              have branch := two.correct glob frame fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool false)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := source_selected condition yes no glob frame fuel nps ph
                state nextFrame false (two.run fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, Bool.false_eq_true, if_false]
              exact ⟨branch.1,selected⟩
            | true =>
              change RawCondition.eval test fuel state = (.ok true,nextFrame) at conditionRun
              have branch := one.correct glob frame fuel nps ph nextFrame nextSame
              have sourceCondition :
                  (Solidity.Source.evalE glob frame fuel condition).run (state.clean,state.world) =
                    (.ok (.val (.bool true)),(nextFrame.clean,nextFrame.world)) := by
                rw [nextClean]
                exact actual
              have selected := source_selected condition yes no glob frame fuel nps ph
                state nextFrame true (one.run fuel nextFrame) sourceCondition branch.2
              simp only [run, conditionRun, if_true]
              exact ⟨branch.1,selected⟩
          | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible


/-- Concrete executable constructor; its correspondence field is proved above. -/
def adapter {ctx returns modifier u condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawSourceAdapter.Adapter ctx returns modifier u yes)
    (two : RawSourceAdapter.Adapter ctx returns modifier u no) :
    RawSourceAdapter.Adapter ctx returns modifier u (.ifElse condition yes no) :=
  ⟨run test one two,correct test one two⟩

/-- Final concrete sequence-branch instantiation, no caller execution law. -/
theorem concrete_sequences {ctx returns modifier u condition yes no}
    (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u yes)
    (two : Solidity.Yul.RawControlSequence.Supported ctx returns modifier u no)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : Solidity.Yul.RawFrame.State ctx)
    (same : Solidity.Yul.RawCoherent.coherent state = true) :
    Solidity.Yul.RawCoherent.coherent
        (Solidity.Yul.RawSourceAdapterIfElse.run test
          (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence one))
          (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence two)) fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.ifElse condition (.block yes) (.block no)) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) =
          Solidity.Yul.RawLoopBody.represented
            (Solidity.Yul.RawSourceAdapterIfElse.run test
              (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence one))
              (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence two)) fuel state) := by
  first
  | simp only [Solidity.Yul.RawSourceAdapterIfElse.correct test
      (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence one))
      (Solidity.Yul.RawSourceAdapter.block (Solidity.Yul.RawSourceAdapter.sequence two))
      glob frame fuel nps ph state same, and_self]
  | decide
  | omega
  | rfl

end Solidity.Yul.RawSourceAdapterIfElse
