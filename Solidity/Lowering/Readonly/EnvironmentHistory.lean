import Solidity.Lowering.Readonly.EnvironmentCredit
import Solidity.Lowering.Readonly.JournalLeaves

/-! Conditional structural-history induction over the ACTUAL source envLoop.
The Source callback induction must produce the exact admitted callback history, including its preceding
credit from the live pre-credit mark. No arbitrary source execution is assumed
to produce that history. No outcome/byte/ABI or whole-world frame is inferred. -/
namespace Solidity.Lowering.Readonly.EnvironmentHistory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open StaticJournal EnvironmentSteps EnvironmentCredit
variable {E : Env}

/-- The bounded Source input for actual admitted callbacks. All provenance fields
are from this source step and the child .run is indexed by its inherited mode.
History starts before credit, matching the actual rollback mark. -/
def CallbackHistories (global : Glob E) (mode : Bool) (bound : Nat) : Prop :=
  ∀ n, n < bound → ∀ depth (state : St E) target sender (value : Word) input requested code credited,
    global.callee state.events = .reenter target sender value input requested →
    (decide (depth ≥ 1024) || (mode && decide (value.val ≠ 0))) = false →
    (instanceAt global target : EM E [] _).run (L0 E, entered state target sender value input requested) =
      (.ok (some code), (L0 E, entered state target sender value input requested)) →
    (credit target value : EM E [] Unit).run (L0 E, entered state target sender value input requested) =
      (.ok (), (L0 E, credited)) →
    History state.ex (requested || mode)
      ((enterInstance global n target sender value input (requested || mode) code (depth + 1)
        (checkpoint state)).run (L0 E, credited)).2.2.ex

/-- Restriction is in horizon only; no invocation fields or premises are dropped. -/
theorem restrict {global : Glob E} {mode : Bool} {small large : Nat}
    (h : CallbackHistories global mode large) (bound : small ≤ large) :
    CallbackHistories global mode small := by
  intro n hn
  exact h n (Nat.lt_of_lt_of_le hn bound)

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

/-- All permitted credits/refusals/outcomes/halts are retained. Only actual
admitted child histories are delegated to the bounded Source premise. -/
theorem loop (global : Glob E) (mode : Bool) (n : Nat)
    (children : CallbackHistories global mode n) (depth : Nat) (state : St E) :
    History state.ex mode ((envLoop global n depth mode).run (L0 E, state)).2.2.ex := by
  induction n generalizing depth state with
  | zero => exact .start _ _
  | succ n ih =>
    have smaller : CallbackHistories global mode n := restrict children (Nat.le_succ n)
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
        exact ih smaller depth (recorded state target value)
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
          exact JournalLeaves.chain (ih smaller depth final) _ prior
    | reenter target sender value input requested =>
      cases guard : decide (depth ≥ 1024) || (mode && decide (value.val ≠ 0)) with
      | true =>
        rw [EnvironmentSteps.refused global n depth mode requested state target sender value input choice guard]
        exact ih smaller depth (completed (entered state target sender value input requested) (.revert []))
      | false =>
        have lookup := instance_run global target (entered state target sender value input requested)
        cases found : lookupCode global target (entered state target sender value input requested) with
        | none =>
          rw [found] at lookup
          rw [EnvironmentSteps.missing_instance global n depth mode requested state target sender value input choice guard lookup]
          exact ih smaller depth (completed (entered state target sender value input requested) (.revert []))
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
            have nested := children n (Nat.lt_succ_self n) depth state target sender value input requested code credited
              choice guard lookup creditRun
            rcases childRun : (enterInstance global n target sender value input (requested || mode) code (depth + 1)
                (checkpoint state)).run (L0 E, credited) with ⟨result, locals, final⟩
            cases locals
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
              exact JournalLeaves.chain (ih smaller depth (completed final out)) _ priorChild

/-- Storage only. Balance, ledger, logs and other world components are not
concluded equal by the static history law. -/
theorem storage (global : Glob E) (n depth : Nat) (state : St E)
    (children : CallbackHistories global true n) :
    SameStorage ((envLoop global n depth true).run (L0 E, state)).2.2.ex state.ex :=
  (loop global true n children depth state).storage rfl

end Solidity.Lowering.Readonly.EnvironmentHistory
