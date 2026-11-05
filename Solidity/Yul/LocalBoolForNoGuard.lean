import Solidity.Yul.LocalBoolForPost

/-! Omitted for guards reuse the actual literal-true evaluator after exact Source transport. -/
namespace Solidity.Yul.LocalBoolForNoGuard

theorem iter_eq : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx)
 (post : Solidity.Source.ROptExpr env types)
 (body : Solidity.Source.RStmt env returns modifier ⟨true,u⟩ types out)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types),
 Solidity.Source.forIter glob frame fuel nps ph .none post body locals =
 Solidity.Source.forIter glob frame fuel nps ph (.some (.bool true)) post body locals := by

  intro env returns modifier u types out post body glob frame fuel nps ph locals
  induction fuel generalizing locals with
  | zero => rfl
  | succ fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      conv => lhs; rw [Solidity.Source.forIter]
      conv => rhs; rw [Solidity.Source.forIter]
      simp only [pure_bind,ih]
      rfl


theorem for_eq : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types middle out : Solidity.Source.RCtx)
 (init : Solidity.Source.RStmt env returns modifier ⟨true,u⟩ types middle)
 (post : Solidity.Source.ROptExpr env middle)
 (body : Solidity.Source.RStmt env returns modifier ⟨true,u⟩ middle out)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types),
 Solidity.Source.execS glob frame fuel nps ph (.forLoop (l := l) init .none post body) locals =
 Solidity.Source.execS glob frame fuel nps ph (.forLoop (l := l) init (.some (.bool true)) post body) locals := by

  intro env returns modifier l u types middle out init post body glob frame fuel nps ph locals
  cases fuel with
  | zero => rfl
  | succ fuel =>
    conv => lhs; rw [Solidity.Source.execS]
    conv => rhs; rw [Solidity.Source.execS]
    simp only [Solidity.Yul.LocalBoolForNoGuard.iter_eq]

def run {env returns modifier types out init post u items}
    (initializer : LocalBoolControl.Supported env types init)
    (step : LocalBoolControl.Supported env (.bool :: types) post)
    (body : LocalBoolItems.Supported env returns modifier ⟨true,u⟩
      (types := .bool :: types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  LocalBoolForPost.run initializer (.base (.literal true)) step body fuel state

def runNoPost {env returns modifier types out init u items}
    (initializer : LocalBoolControl.Supported env types init)
    (body : LocalBoolItems.Supported env returns modifier ⟨true,u⟩
      (types := .bool :: types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  LocalBoolFor.run initializer (.base (.literal true)) body fuel state


/-- Concrete clean-input Source agreement via exact omitted-guard transport. -/
theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolForNoGuard.run initializer step body fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none (.some post) (.block items))
   locals).run (Solidity.Source.L0 env,world)) := by

  intro env returns modifier l u types out init initializer post step items body glob frame fuel nps ph locals world
  rw [Solidity.Yul.LocalBoolForNoGuard.for_eq]
  exact Solidity.Yul.LocalBoolForPost.source_agrees env returns modifier l u types out init initializer
    (.bool true) (.base (.literal true)) post step items body glob frame fuel nps ph locals world


/-- Concrete clean-input Source agreement via exact omitted-guard transport. -/
theorem source_no_post_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
   (Solidity.Yul.LocalBoolForNoGuard.runNoPost initializer body fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none .none (.block items))
   locals).run (Solidity.Source.L0 env,world)) := by

  intro env returns modifier l u types out init initializer items body glob frame fuel nps ph locals world
  rw [Solidity.Yul.LocalBoolForNoGuard.for_eq]
  exact Solidity.Yul.LocalBoolFor.source_agrees env returns modifier l u types out init initializer
    (.bool true) (.base (.literal true)) items body glob frame fuel nps ph locals world


end Solidity.Yul.LocalBoolForNoGuard

