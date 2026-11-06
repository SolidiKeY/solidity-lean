import Solidity.Yul.LocalForTimeout
import Solidity.Source.Semantics

/-! Actual Source firstDone horizons for certified initialized omitted-guard loops.
Uses concrete timeout producers, not an abstract divergence premise. -/
namespace Solidity.Yul.LocalForFirstDone

theorem post : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (_initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (post : Solidity.Source.RExpr env (.bool :: types) .bool)
 (_step : Solidity.Yul.LocalBoolControl.Supported env (.bool :: types) post)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (_body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 ∀ bound, Solidity.Source.firstDone (fun fuel =>
   (Solidity.Source.execS glob frame fuel nps ph
     (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none (.some post) (.block items)) locals).run
     (Solidity.Source.L0 env,world)) bound = none := by
  intro env returns modifier l u types out init initializer post step items body glob frame nps ph locals world
  apply (Solidity.Source.firstDone_none_iff _).2
  intro fuel
  obtain ⟨finalWorld,actual⟩ := Solidity.Yul.LocalForTimeout.source_omitted env returns modifier l u types out
    init initializer post step items body glob frame fuel nps ph locals world
  rw [actual]
  rfl

theorem no_post : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l u : Bool) (types out : Solidity.Source.RCtx)
 (init : Solidity.Source.RExpr env types .bool)
 (_initializer : Solidity.Yul.LocalBoolControl.Supported env types init)
 (items : Solidity.Source.RItems env returns modifier ⟨true,u⟩ (.bool :: types) out)
 (_body : Solidity.Yul.LocalBoolItems.Supported env returns modifier ⟨true,u⟩ items)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph env))
 (locals : Solidity.Source.Locals env.layout types) (world : Solidity.Source.St env),
 ∀ bound, Solidity.Source.firstDone (fun fuel =>
   (Solidity.Source.execS glob frame fuel nps ph
     (.forLoop (l := l) (.declInit (τ := .bool) init (by rfl)) .none .none (.block items)) locals).run
     (Solidity.Source.L0 env,world)) bound = none := by
  intro env returns modifier l u types out init initializer items body glob frame nps ph locals world
  apply (Solidity.Source.firstDone_none_iff _).2
  intro fuel
  obtain ⟨finalWorld,actual⟩ := Solidity.Yul.LocalForTimeout.source_omitted_no_post env returns modifier l u types out
    init initializer items body glob frame fuel nps ph locals world
  rw [actual]
  rfl

end Solidity.Yul.LocalForFirstDone
