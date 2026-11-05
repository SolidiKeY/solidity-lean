import Solidity.Yul.RawNoGuardFailure
import Solidity.Yul.RawAdapterLoopHorizon

/-! Finite noncompletion for actual no-post omitted-guard drivers and Source.
The existing structural no-break premise is sufficient only. Coherent/clean
Source boundaries remain explicit; no error classification or divergence claim. -/
namespace Solidity.Yul.RawNoPostFailure

theorem loop_no_ok : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawControlledWhile.run (.base (.literal true)) body fuel state).1 ≠ .ok () := by
  intro ctx returns modifier u stmt body safe fuel
  induction fuel with
  | zero => intro state bad; cases bad
  | succ fuel ih =>
    intro state bad
    rw [Solidity.Yul.RawControlledWhile.run] at bad
    cases guardActual : Solidity.Yul.RawCondition.eval (.base (.literal true)) fuel state with
    | mk tag next =>
      rw [guardActual] at bad
      cases tag with
      | error halt => cases bad
      | ok choice =>
        cases choice with
        | false => exact Solidity.Yul.RawNoGuardFailure.literal_no_false ctx fuel state (by rw [guardActual])
        | true =>
          cases bodyActual : Solidity.Yul.RawLoopBody.run body fuel next with
          | mk tag after =>
            rw [bodyActual] at bad
            cases tag with
            | error halt => cases bad
            | ok flow =>
              cases flow with
              | normal | continue_ _ => exact ih after bad
              | break_ h =>
                exact Solidity.Yul.RawNoGuardFailure.run_no_break ctx returns modifier u stmt body safe fuel next (by rw [bodyActual])
              | leave_ impossible => cases impossible

theorem initialized_no_ok : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceAdapterFor.run initializer (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 ≠ .ok () := by
  intro ctx returns modifier u stmt body safe initial initializer fuel state bad
  cases fuel with
  | zero => cases bad
  | succ fuel =>
    rw [Solidity.Yul.RawSourceAdapterFor.run] at bad
    cases actual : initializer.run fuel state with
    | mk tag next =>
      rw [actual] at bad
      cases tag with
      | error halt => cases bad
      | ok flow =>
        cases flow with
        | normal =>
          rw [Solidity.Yul.RawAdapterLoopHorizon.body_agrees] at bad
          exact loop_no_ok ctx returns modifier u stmt body safe fuel next bad
        | break_ _ | continue_ _ => cases bad
        | leave_ impossible => cases impossible

theorem adapter_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 ((Solidity.Yul.RawSourceForPost.Absent.adapter (Solidity.Yul.RawSourceAdapterFor.adapter initializer (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body body))).run fuel state).1 ≠ .ok .normal := by
  intro ctx returns modifier u stmt body safe initial initializer fuel state
  change (Solidity.Yul.RawSourceAdapterFor.run initializer (.base (.literal true))
    (Solidity.Yul.RawSourceAdapter.body body) fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)) ≠ .ok .normal
  intro bad
  cases actual : (Solidity.Yul.RawSourceAdapterFor.run initializer (.base (.literal true))
      (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 with
  | error halt =>
    rw [actual] at bad
    cases bad
  | ok value =>
    cases value
    exact initialized_no_ok ctx returns modifier u stmt body safe initial initializer fuel state actual

theorem source_iter_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx)
 (_same : Solidity.Yul.RawCoherent.coherent state = true)
 (next : Solidity.Source.Locals ctx.env.layout ctx.tys)
 (finalWorld : Solidity.Source.St ctx.env),
 (Solidity.Source.forIter glob frame fuel nps ph .none .none stmt state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) ≠ (.ok (.normal next),(Solidity.Source.L0 ctx.env,finalWorld)) := by
  intro ctx returns modifier u stmt body safe glob frame fuel nps ph state same next finalWorld
  rw [Solidity.Yul.RawSourceForPost.Absent.source_true]
  have agreement := (Solidity.Yul.RawSourceForIter.correct (.base (.literal true))
    (Solidity.Yul.RawSourceAdapter.body body) glob frame fuel nps ph state same).2
  cases raw : Solidity.Yul.RawSourceAdapterLoop.run (.base (.literal true))
      (Solidity.Yul.RawSourceAdapter.body body) fuel state with
  | mk tag after =>
    rw [raw] at agreement
    cases tag with
    | error halt =>
      change (Solidity.Source.forIter glob frame fuel nps ph (.some (.bool true)) .none stmt state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) = (.error halt,(Solidity.Source.L0 ctx.env,after.world)) at agreement
      intro bad
      rw [bad] at agreement
      cases agreement
    | ok value =>
      cases value
      have impossible : (Solidity.Yul.RawSourceAdapterLoop.run (.base (.literal true))
          (Solidity.Yul.RawSourceAdapter.body body) fuel state).1 = .ok () := by rw [raw]
      rw [Solidity.Yul.RawAdapterLoopHorizon.body_agrees] at impossible
      exact False.elim (loop_no_ok ctx returns modifier u stmt body safe fuel state impossible)

theorem source_initialized_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (l : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (_initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx)
 (_same : Solidity.Yul.RawCoherent.coherent state = true)
 (next : Solidity.Source.Locals ctx.env.layout ctx.tys)
 (finalWorld : Solidity.Source.St ctx.env),
 (Solidity.Source.execS glob frame fuel nps ph
 (Solidity.Source.RStmt.forLoop (l := l) initial .none .none stmt) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) ≠ (.ok (.normal next),(Solidity.Source.L0 ctx.env,finalWorld)) := by
  intro ctx returns modifier u stmt body safe l initial initializer glob frame fuel nps ph state same next finalWorld
  rw [Solidity.Yul.RawSourceForPost.Absent.source_initialized]
  have agreement := (Solidity.Yul.RawSourceAdapterFor.correct (l := l) initializer
    (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body body)
    glob frame fuel nps ph state same).2
  cases raw : Solidity.Yul.RawSourceAdapterFor.run initializer (.base (.literal true))
      (Solidity.Yul.RawSourceAdapter.body body) fuel state with
  | mk tag after =>
    rw [raw] at agreement
    cases tag with
    | error halt =>
      change (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.forLoop (l := l) initial (.some (.bool true)) .none stmt) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) = (.error halt,(Solidity.Source.L0 ctx.env,after.world)) at agreement
      intro bad
      rw [bad] at agreement
      cases agreement
    | ok value =>
      cases value
      exact False.elim (initialized_no_ok ctx returns modifier u stmt body safe initial initializer fuel state (by rw [raw]))

theorem source_clean_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (l : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (_initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (locals next : Solidity.Source.Locals ctx.env.layout ctx.tys)
 (world finalWorld : Solidity.Source.St ctx.env),
 (Solidity.Source.execS glob frame fuel nps ph
 (Solidity.Source.RStmt.forLoop (l := l) initial .none .none stmt) locals).run
 (Solidity.Source.L0 ctx.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 ctx.env,finalWorld)) := by
  intro ctx returns modifier u stmt body safe l initial initializer glob frame fuel nps ph locals next world finalWorld
  exact source_initialized_no_normal ctx returns modifier u stmt body safe l initial initializer
    glob frame fuel nps ph (Solidity.Yul.RawFrame.ofClean locals world)
    (Solidity.Yul.RawCoherent.coherent_ofClean locals world) next finalWorld

end Solidity.Yul.RawNoPostFailure
