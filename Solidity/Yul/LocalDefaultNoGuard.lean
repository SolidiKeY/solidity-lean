import Solidity.Yul.LocalDefaultPostIter
import Solidity.Yul.LocalBoolForNoGuard

/-! Concrete omitted-guard iterations reuse proved literal-true runners and Source transport. -/
namespace Solidity.Yul.LocalDefaultNoGuard

def run {env returns modifier types out post u items}
    (step : LocalBoolControl.Supported env types post)
    (body : LocalDefaultItems.Supported env returns modifier ⟨true,u⟩
      (types := types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  LocalDefaultPostIter.run (.base (.literal true)) step body fuel state

def runNoPost {env returns modifier types out u items}
    (body : LocalDefaultItems.Supported env returns modifier ⟨true,u⟩
      (types := types) (out := out) items)
    (fuel : Nat) (state : LocalState env types) : LocalBoolItems.Result env types :=
  LocalDefaultWhile.run (.base (.literal true)) body fuel state


theorem source_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items) (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
 (Solidity.Yul.LocalDefaultNoGuard.run step body fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.forIter glob frame fuel nps ph .none (.some post) (.block items) locals).run
 (Solidity.Source.L0 env,world)) := by

  intro env returns modifier u types out post step items body glob frame fuel nps ph locals world
  rw [Solidity.Yul.LocalBoolForNoGuard.iter_eq]
  exact Solidity.Yul.LocalDefaultPostIter.source_agrees env returns modifier u types out
    (.bool true) (.base (.literal true)) post step items body glob frame fuel nps ph locals world

theorem source_no_post_agrees : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items) (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 Solidity.Yul.LocalBoolItems.project types
 (Solidity.Yul.LocalDefaultNoGuard.runNoPost body fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.forIter glob frame fuel nps ph .none .none (.block items) locals).run
 (Solidity.Source.L0 env,world)) := by

  intro env returns modifier u types out items body glob frame fuel nps ph locals world
  rw [Solidity.Yul.LocalBoolForNoGuard.iter_eq,Solidity.Yul.RawSourceForIter.source_while]
  exact Solidity.Yul.LocalDefaultWhile.source_agrees env returns modifier true u types out
    (.bool true) (.base (.literal true)) items body glob frame fuel nps ph locals world

theorem world : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items) (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultNoGuard.run step body fuel state) = state.2 := by

  intro env returns modifier u types out post step items body fuel state
  exact Solidity.Yul.LocalDefaultPostIter.world env returns modifier u types out (.bool true) (.base (.literal true)) post step items body fuel state

theorem no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (post : Solidity.Source.RExpr env types .bool)
 (step : Solidity.Yul.LocalBoolControl.Supported env types post) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items) (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultNoGuard.run step body fuel state ≠ .normal next := by

  intro env returns modifier u types out post step items body fuel state next
  exact Solidity.Yul.LocalDefaultPostIter.no_normal env returns modifier u types out post step items body fuel state next

theorem source_no_normal : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (post : Solidity.Source.RExpr env types .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported env types post) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (_body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.forIter glob frame fuel nps ph .none (.some post) (.block items) locals).run
 (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by

  intro env returns modifier u types out post step items body glob frame fuel nps ph locals next world finalWorld
  rw [Solidity.Yul.LocalBoolForNoGuard.iter_eq]
  exact Solidity.Yul.LocalDefaultPostIter.source_no_normal env returns modifier u types out post step items body glob frame fuel nps ph locals next world finalWorld

theorem world_no_post : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items) (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalItemWorld.world (Solidity.Yul.LocalDefaultNoGuard.runNoPost body fuel state) = state.2 := by

  intro env returns modifier u types out items body fuel state
  exact Solidity.Yul.LocalDefaultWhile.world env returns modifier u types out (.bool true) (.base (.literal true)) items body fuel state

theorem no_normal_no_post : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items) (fuel : Nat) (state next : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultNoGuard.runNoPost body fuel state ≠ .normal next := by

  intro env returns modifier u types out items body fuel state next
  exact Solidity.Yul.LocalDefaultWhile.no_normal env returns modifier u types out items body fuel state next

theorem source_no_normal_no_post : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier u : Bool) (types out : Solidity.Source.RCtx) (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ types out)
 (_body : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals next : Solidity.Source.Locals env.layout types) (world finalWorld : Solidity.Source.St env),
 (Solidity.Source.forIter glob frame fuel nps ph .none .none (.block items) locals).run
 (Solidity.Source.L0 env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 env,finalWorld)) := by

  intro env returns modifier u types out items body glob frame fuel nps ph locals next world finalWorld
  rw [Solidity.Yul.LocalBoolForNoGuard.iter_eq,Solidity.Yul.RawSourceForIter.source_while]
  exact Solidity.Yul.LocalDefaultWhile.source_no_normal env returns modifier true u types out items body glob frame fuel nps ph locals next world finalWorld
end Solidity.Yul.LocalDefaultNoGuard
