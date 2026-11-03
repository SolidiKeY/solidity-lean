import Solidity.Lowering.Readonly.EnvironmentHistory
import Solidity.Lowering.Readonly.SourceHistory

/-! Actual envLoop successor histories. Recursive environment execution and
child entry use the strictly smaller bound. Credits and all halts remain. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open StaticJournal EnvironmentSteps EnvironmentCredit
variable {E : Env}

private def lookupCode (global : Glob E) (target : Address) (state : St E) : Option String :=
  match (state.ex.world.accounts target).code with
  | some code => global.contractAt code
  | none => none

private theorem instance_run (global : Glob E) (target : Address) (state : St E) :
    (instanceAt global target : EM E [] _).run (L0 E, state) =
      (.ok (lookupCode global target state), (L0 E, state)) := by
  simp only [instanceAt, EM.st, lookupCode, bind, pure, ExceptT.bind, ExceptT.pure,
    ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.get,
    get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    Functor.map, StateT.map]
  cases (state.ex.world.accounts target).code <;> rfl

theorem envLoop_succ (global : Glob E) (n : Nat) (history : At global n) (depth : Nat) (mode : Bool) :
    Effect mode (envLoop global (n+1) depth mode) := by
  intro locals state
  cases locals
  have ih (depth : Nat) (state : St E) : History state.ex mode ((envLoop global n depth mode).run (L0 E, state)).2.2.ex := history.envLoop depth mode (L0 E) state
  cases choice : global.callee state.events with
  | answer out =>
    rw [EnvironmentSteps.answer global n depth mode state out choice]
    exact .start _ _
  | credit target value =>
    have lookup := instance_run global target (recorded state target value)
    cases found : lookupCode global target (recorded state target value) with
    | none =>
      rw [found] at lookup
      rw [EnvironmentCredit.unknown global n depth mode state target value choice lookup]
      exact ih depth (recorded state target value)
    | some code =>
      rw [found] at lookup
      have prior := credit_history target value (L0 E) (recorded state target value) mode
      rcases creditRun : (credit target value : EM E [] Unit).run
          (L0 E, recorded state target value) with ⟨result, locals, final⟩
      cases locals
      rw [creditRun] at prior
      cases result with
      | error halt =>
        rw [EnvironmentCredit.failed global n depth mode state final target value code halt choice lookup creditRun]
        exact prior
      | ok done =>
        cases done
        rw [EnvironmentCredit.known global n depth mode state final target value code choice lookup creditRun]
        exact JournalLeaves.chain (ih depth final) _ prior
  | reenter target sender value input requested =>
    cases guard : decide (depth ≥ 1024) || (mode && decide (value.val ≠ 0)) with
    | true =>
      rw [EnvironmentSteps.refused global n depth mode requested state target sender value input choice guard]
      exact ih depth (completed (entered state target sender value input requested) (.revert []))
    | false =>
      have lookup := instance_run global target (entered state target sender value input requested)
      cases found : lookupCode global target (entered state target sender value input requested) with
      | none =>
        rw [found] at lookup
        rw [EnvironmentSteps.missing_instance global n depth mode requested state target sender value input choice guard lookup]
        exact ih depth (completed (entered state target sender value input requested) (.revert []))
      | some code =>
        rw [found] at lookup
        have prior := credit_history target value (L0 E) (entered state target sender value input requested) mode
        rcases creditRun : (credit target value : EM E [] Unit).run
            (L0 E, entered state target sender value input requested) with ⟨result, locals, credited⟩
        cases locals
        rw [creditRun] at prior
        cases result with
        | error halt =>
          rw [callback_credit_failed global n depth mode requested state credited target sender value input code halt choice guard lookup creditRun]
          exact prior
        | ok done =>
          cases done
          have staticCredit := credit_history target value (L0 E) (entered state target sender value input requested) (requested || mode)
          rw [creditRun] at staticCredit
          have nested := history.enterInstance target sender value input (requested || mode) code (depth + 1) state credited staticCredit
          rcases childRun : (enterInstance global n target sender value input (requested || mode) code (depth + 1)
              (checkpoint state)).run (L0 E, credited) with ⟨result, locals, final⟩
          cases locals
          change History state.ex (requested || mode)
            ((enterInstance global n target sender value input (requested || mode) code (depth + 1)
              (checkpoint state)).run (L0 E, credited)).2.2.ex at nested
          rw [childRun] at nested
          have priorChild : History state.ex mode final.ex := .child (.start _ _) requested nested
          cases result with
          | error halt =>
            rw [child_halt global n depth mode requested state credited final target sender value input code halt
              choice guard lookup creditRun childRun]
            exact priorChild
          | ok out =>
            rw [child_success global n depth mode requested state credited final target sender value input code out
              choice guard lookup creditRun childRun]
            exact JournalLeaves.chain (ih depth (completed final out)) _ priorChild

end Solidity.Lowering.Readonly.SourceHistory
