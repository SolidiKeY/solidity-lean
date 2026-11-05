import Solidity.Yul.LocalForNoGuardFailure
import Solidity.Yul.LocalForNoPostHorizon
import Solidity.Yul.LocalPostHorizon

/-! Concrete finite timeout classification for certified full Boolean for adapters.
Omitted guards cannot complete normally; exact reached frames are retained. -/
namespace Solidity.Yul.LocalForTimeout

theorem halt_kind : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types)
 (reached : Solidity.Source.RCtx) (halt : Solidity.Source.Halt)
 (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalBoolForPost.run initializer test step body fuel state = .halted halt next → halt = .timeout := by
  intro env returns modifier u types out init initializer condition test post step items body fuel state reached halt next failed
  cases fuel with
  | zero => cases failed; rfl
  | succ fuel =>
    rw [Solidity.Yul.LocalBoolForPost.run] at failed
    cases initialized : Solidity.Yul.LocalBoolInitialization.run initializer fuel state with
    | halted error previous =>
      rw [initialized] at failed
      have same := Solidity.Yul.LocalItemFailure.initialization env types init initializer fuel state previous error initialized
      cases failed
      exact same
    | normal entered =>
      rw [initialized] at failed
      dsimp only at failed
      cases iterated : Solidity.Yul.LocalBoolPostIter.run test step body fuel entered with
      | normal after =>
        rw [iterated] at failed
        cases failed
      | halted error after =>
        rw [iterated] at failed
        have agreement := Solidity.Yul.LocalForInitHorizon.iteration_agrees env returns modifier u
          (.bool :: types) out condition test post step items body fuel entered
        have same := Solidity.Yul.LocalPostHorizon.postIteration env returns modifier u
          (.bool :: types) out condition test post step items (.body body) fuel entered _ error after
          (agreement.symm.trans iterated)
        cases failed
        exact same

theorem no_post_halt_kind : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (condition : Solidity.Source.RExpr env (.bool :: types) .bool)
 (test : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) condition)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types)
 (reached : Solidity.Source.RCtx) (halt : Solidity.Source.Halt)
 (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalBoolFor.run initializer test body fuel state = .halted halt next → halt = .timeout := by
  intro env returns modifier u types out init initializer condition test items body fuel state reached halt next failed
  cases fuel with
  | zero => cases failed; rfl
  | succ fuel =>
    rw [Solidity.Yul.LocalBoolFor.run] at failed
    cases initialized : Solidity.Yul.LocalBoolInitialization.run initializer fuel state with
    | halted error previous =>
      rw [initialized] at failed
      have same := Solidity.Yul.LocalItemFailure.initialization env types init initializer fuel state previous error initialized
      cases failed
      exact same
    | normal entered =>
      rw [initialized] at failed
      dsimp only at failed
      cases iterated : Solidity.Yul.LocalBoolWhile.run test body fuel entered with
      | normal after =>
        rw [iterated] at failed
        cases failed
      | halted error after =>
        rw [iterated] at failed
        have agreement := Solidity.Yul.LocalForNoPostHorizon.iteration_agrees env returns modifier u
          (.bool :: types) out condition test items body fuel entered
        have same := Solidity.Yul.LocalLoopFailure.whileLoop env returns modifier u
          (.bool :: types) out condition test items (.body body) fuel entered _ error after
          (agreement.symm.trans iterated)
        cases failed
        exact same

theorem omitted : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 ∃ (reached : Solidity.Source.RCtx) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalBoolForNoGuard.run initializer step body fuel state = .halted .timeout next := by
  intro env returns modifier u types out init initializer post step items body fuel state
  cases actual : Solidity.Yul.LocalBoolForNoGuard.run initializer step body fuel state with
  | normal next =>
    exact False.elim (Solidity.Yul.LocalForNoGuardFailure.no_normal env returns modifier u types out
      init initializer post step items body fuel state next actual)
  | halted halt next =>
    have same := Solidity.Yul.LocalForTimeout.halt_kind env returns modifier u types out
      init initializer (.bool true) (.base (.literal true)) post step items body fuel state _ halt next actual
    cases same
    exact ⟨_,next,rfl⟩

theorem omitted_no_post : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 ∃ (reached : Solidity.Source.RCtx) (next : Solidity.Yul.LocalState env reached),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost initializer body fuel state = .halted .timeout next := by
  intro env returns modifier u types out init initializer items body fuel state
  cases actual : Solidity.Yul.LocalBoolForNoGuard.runNoPost initializer body fuel state with
  | normal next =>
    exact False.elim (Solidity.Yul.LocalForNoGuardFailure.no_post_normal env returns modifier u types out
      init initializer items body fuel state next actual)
  | halted halt next =>
    have same := Solidity.Yul.LocalForTimeout.no_post_halt_kind env returns modifier u types out
      init initializer (.bool true) (.base (.literal true)) items body fuel state _ halt next actual
    cases same
    exact ⟨_,next,rfl⟩

theorem source_omitted : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (_initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (_body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 ∃ finalWorld : Solidity.Source.St env,
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none (.some post) (.block items)) locals).run
   (Solidity.Source.L0 env,world) = (.error .timeout,(Solidity.Source.L0 env,finalWorld)) := by
  intro env returns modifier l u types out init initializer post step items body glob frame fuel nps ph locals world
  have agreement := Solidity.Yul.LocalBoolForNoGuard.source_agrees env returns modifier l u types out
    init initializer post step items body glob frame fuel nps ph locals world
  obtain ⟨reached,next,actual⟩ := Solidity.Yul.LocalForTimeout.omitted env returns modifier u types out
    init initializer post step items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  rw [actual] at agreement
  change some ((Except.error Solidity.Source.Halt.timeout : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
    (Solidity.Source.L0 env,next.2)) = some _ at agreement
  exact ⟨next.2,(Option.some.inj agreement).symm⟩

theorem source_omitted_no_post : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (_initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (_body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 ∃ finalWorld : Solidity.Source.St env,
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none .none (.block items)) locals).run
   (Solidity.Source.L0 env,world) = (.error .timeout,(Solidity.Source.L0 env,finalWorld)) := by
  intro env returns modifier l u types out init initializer items body glob frame fuel nps ph locals world
  have agreement := Solidity.Yul.LocalBoolForNoGuard.source_no_post_agrees env returns modifier l u types out
    init initializer items body glob frame fuel nps ph locals world
  obtain ⟨reached,next,actual⟩ := Solidity.Yul.LocalForTimeout.omitted_no_post env returns modifier u types out
    init initializer items body fuel (Solidity.Yul.LocalState.ofClean (locals,world))
  rw [actual] at agreement
  change some ((Except.error Solidity.Source.Halt.timeout : Solidity.Source.R (Solidity.Source.Out env.layout types types)),
    (Solidity.Source.L0 env,next.2)) = some _ at agreement
  exact ⟨next.2,(Option.some.inj agreement).symm⟩

end Solidity.Yul.LocalForTimeout
