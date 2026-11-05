import Solidity.Yul.LocalForFirstDone
import Solidity.Yul.Checks.LocalForTimeout

namespace Solidity.Yul.Checks.LocalForFirstDone
export LocalForTimeout (env read post items body)
abbrev Statement := Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool]
def locals : Solidity.Source.Locals env.layout [.bool] := .cons (.bool true) .nil
def finalLocals : Solidity.Source.Locals env.layout [.bool] := .cons (.bool false) .nil
def loop (guard : Solidity.Source.ROptBool env [.bool,.bool])
    (post : Solidity.Source.ROptExpr env [.bool,.bool]) : Statement :=
  .forLoop (.declInit (τ := .bool) (.local .here) (by rfl)) guard post (.block items)
def noPost : Statement := loop .none .none
def withPost : Statement := loop .none (.some (.assign (.local .here) (.bool false)))
def guarded : Statement := loop (.some (.local .here)) .none
def stopped : Statement := loop (.some (.bool false)) .none
/-- Outside the Boolean body certificates: break is a real terminating control. -/
def breaker : Statement := .forLoop .skip .none .none .brk
def continuer : Statement := .forLoop .skip .none .none .cont
/-- Outside initializer certificates: existing Source reports its invalid control result. -/
def failedInit : Statement := .forLoop .brk .none .none .skip
def search (stmt : Statement) (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr)
    (nps : Nat) (ph : Option (Solidity.Source.Ph env)) (world : Solidity.Source.St env) (bound : Nat) :=
  Solidity.Source.firstDone (fun fuel => (Solidity.Source.execS glob frame fuel nps ph stmt locals).run
    (Solidity.Source.L0 env,world)) bound
def witness : Nonempty (LocalBoolItems.Supported env [] false ⟨true,false⟩ items) := ⟨body⟩
theorem noPostAllBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env) (bound : Nat), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.noPost glob frame nps ph world bound = none := by
  intro glob frame nps ph world bound
  exact Solidity.Yul.LocalForFirstDone.no_post Solidity.Yul.Checks.LocalForFirstDone.env [] false false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForFirstDone.read Solidity.Yul.Checks.LocalForFirstDone.items Solidity.Yul.Checks.LocalForFirstDone.body glob frame nps ph Solidity.Yul.Checks.LocalForFirstDone.locals world bound


theorem postAllBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env) (bound : Nat), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.withPost glob frame nps ph world bound = none := by
  intro glob frame nps ph world bound
  exact Solidity.Yul.LocalForFirstDone.post Solidity.Yul.Checks.LocalForFirstDone.env [] false false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForFirstDone.read (.assign (.local .here) (.bool false)) Solidity.Yul.Checks.LocalForFirstDone.post Solidity.Yul.Checks.LocalForFirstDone.items Solidity.Yul.Checks.LocalForFirstDone.body glob frame nps ph Solidity.Yul.Checks.LocalForFirstDone.locals world bound


theorem beforeGuardedCompletion : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.guarded glob frame nps ph world 8 = none := by
  intro glob frame nps ph world; rfl


theorem guardedFirstCompletion : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.guarded glob frame nps ph world 9 = some (9,(.ok (.normal Solidity.Yul.Checks.LocalForFirstDone.finalLocals),(Solidity.Source.L0 Solidity.Yul.Checks.LocalForFirstDone.env,world))) := by
  intro glob frame nps ph world; rfl


theorem guardedExtended : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env) (extra : Nat), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.guarded glob frame nps ph world (9+extra) = some (9,(.ok (.normal Solidity.Yul.Checks.LocalForFirstDone.finalLocals),(Solidity.Source.L0 Solidity.Yul.Checks.LocalForFirstDone.env,world))) := by
  intro glob frame nps ph world extra
  exact Solidity.Source.firstDone_mono _ (Nat.le_add_right 9 extra) (Solidity.Yul.Checks.LocalForFirstDone.guardedFirstCompletion glob frame nps ph world)


theorem breakCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.breaker glob frame nps ph world 3 = some (3,(.ok (.normal Solidity.Yul.Checks.LocalForFirstDone.locals),(Solidity.Source.L0 Solidity.Yul.Checks.LocalForFirstDone.env,world))) := by
  intro glob frame nps ph world; rfl


theorem continueUnfinished : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.continuer glob frame nps ph world 8 = none := by
  intro glob frame nps ph world; rfl


theorem failureCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.failedInit glob frame nps ph world 2 = some (2,(.error (.stuck "for initializer"),(Solidity.Source.L0 Solidity.Yul.Checks.LocalForFirstDone.env,world))) := by
  intro glob frame nps ph world; rfl


theorem falseGuardCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForFirstDone.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForFirstDone.env)) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForFirstDone.env), Solidity.Yul.Checks.LocalForFirstDone.search Solidity.Yul.Checks.LocalForFirstDone.stopped glob frame nps ph world 3 = some (3,(.ok (.normal Solidity.Yul.Checks.LocalForFirstDone.locals),(Solidity.Source.L0 Solidity.Yul.Checks.LocalForFirstDone.env,world))) := by
  intro glob frame nps ph world; rfl

#print axioms Solidity.Yul.LocalForFirstDone.post
#print axioms Solidity.Yul.LocalForFirstDone.no_post
#print axioms noPostAllBounds
#print axioms postAllBounds
#print axioms beforeGuardedCompletion
#print axioms guardedFirstCompletion
#print axioms guardedExtended
#print axioms breakCompletes
#print axioms continueUnfinished
#print axioms failureCompletes
#print axioms falseGuardCompletes
end Solidity.Yul.Checks.LocalForFirstDone
