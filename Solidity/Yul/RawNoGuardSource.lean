import Solidity.Yul.RawNoGuardFailure

/-! Actual Source finite noncompletion for the concrete no-break omitted-guard
fragment. Coherent-input laws use real execution correspondence; the clean-input
corollary discharges coherence with ofClean. No dirty readback, error classification
or general divergence/admission completeness is asserted. -/
namespace Solidity.Yul.RawNoGuardSource

theorem source_iter_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx)
 (_same : Solidity.Yul.RawCoherent.coherent state = true)
 (next : Solidity.Source.Locals ctx.env.layout ctx.tys)
 (finalWorld : Solidity.Source.St ctx.env),
 (Solidity.Source.forIter glob frame fuel nps ph .none (.some post) stmt state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) ≠ (.ok (.normal next),(Solidity.Source.L0 ctx.env,finalWorld)) := by
  intro ctx returns modifier u stmt body safe post step glob frame fuel nps ph state same next finalWorld
  rw [Solidity.Yul.RawSourceForPost.Absent.source_true]
  have agreement := (Solidity.Yul.RawSourceForPost.correct (.base (.literal true)) step
    (Solidity.Yul.RawSourceAdapter.body body) glob frame fuel nps ph state same).2
  cases raw : Solidity.Yul.RawSourceForPost.run (.base (.literal true)) step
      (Solidity.Yul.RawSourceAdapter.body body) fuel state with
  | mk tag after =>
    rw [raw] at agreement
    cases tag with
    | error halt =>
      change (Solidity.Source.forIter glob frame fuel nps ph (.some (.bool true)) (.some post) stmt state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) = (.error halt,(Solidity.Source.L0 ctx.env,after.world)) at agreement
      intro bad
      rw [bad] at agreement
      cases agreement
    | ok value =>
      cases value
      exact False.elim (Solidity.Yul.RawNoGuardFailure.run_no_ok ctx returns modifier u stmt body safe post step fuel state (by rw [raw]))

theorem source_initialized_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
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
 (Solidity.Source.RStmt.forLoop (l := l) initial .none (.some post) stmt) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) ≠ (.ok (.normal next),(Solidity.Source.L0 ctx.env,finalWorld)) := by
  intro ctx returns modifier u stmt body safe post step l initial initializer glob frame fuel nps ph state same next finalWorld
  rw [Solidity.Yul.RawSourceForPost.Absent.source_initialized]
  have agreement := (Solidity.Yul.RawSourceForPost.Initialized.correct (l := l) initializer
    (.base (.literal true)) step (Solidity.Yul.RawSourceAdapter.body body)
    glob frame fuel nps ph state same).2
  cases raw : Solidity.Yul.RawSourceForPost.Initialized.run initializer (.base (.literal true)) step
      (Solidity.Yul.RawSourceAdapter.body body) fuel state with
  | mk tag after =>
    rw [raw] at agreement
    cases tag with
    | error halt =>
      change (Solidity.Source.execS glob frame fuel nps ph
        (Solidity.Source.RStmt.forLoop (l := l) initial (.some (.bool true)) (.some post) stmt) state.clean).run
        (Solidity.Source.L0 ctx.env,state.world) = (.error halt,(Solidity.Source.L0 ctx.env,after.world)) at agreement
      intro bad
      rw [bad] at agreement
      cases agreement
    | ok value =>
      cases value
      exact False.elim (Solidity.Yul.RawNoGuardFailure.initialized_no_ok ctx returns modifier u stmt body safe post step initial initializer fuel state (by rw [raw]))

theorem source_clean_no_normal : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (body : Solidity.Yul.RawLoopBody.Supported ctx returns modifier u stmt)
 (_safe : Solidity.Yul.RawNoGuardFailure.noBreak body = true)
 (post : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys post)
 (l : Bool)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (_initializer : Solidity.Yul.RawSourceAdapter.Adapter ctx returns modifier u initial)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (locals next : Solidity.Source.Locals ctx.env.layout ctx.tys)
 (world finalWorld : Solidity.Source.St ctx.env),
 (Solidity.Source.execS glob frame fuel nps ph
 (Solidity.Source.RStmt.forLoop (l := l) initial .none (.some post) stmt) locals).run
 (Solidity.Source.L0 ctx.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 ctx.env,finalWorld)) := by
  intro ctx returns modifier u stmt body safe post step l initial initializer glob frame fuel nps ph locals next world finalWorld
  exact source_initialized_no_normal ctx returns modifier u stmt body safe post step l initial initializer
    glob frame fuel nps ph (Solidity.Yul.RawFrame.ofClean locals world)
    (Solidity.Yul.RawCoherent.coherent_ofClean locals world) next finalWorld

end Solidity.Yul.RawNoGuardSource
