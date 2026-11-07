import Solidity.Yul.LocalForNoGuardFailure
import Solidity.Yul.Checks.LocalForNoPostHorizon
import Solidity.Yul.Checks.LocalBoolForNoGuard

namespace Solidity.Yul.Checks.LocalForNoGuardFailure
export LocalForNoPostHorizon (env state raw cleanFalse read stop test items body counterChanged)
def post : LocalBoolControl.Supported env [.bool,.bool]
    (.assign (.local .here) (.bool false)) := .assign .here (.base (.literal false))
def enteredFalse (world : Solidity.Source.St env) : LocalState env [.bool,.bool] :=
  ((cleanFalse,(raw 2,())),world)
def witness : Nonempty (LocalBoolItems.Supported env [] false ⟨true,false⟩ items) := ⟨body⟩
theorem noPostAllFuel : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env) (fuel : Nat) (next : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalForNoGuardFailure.env [.bool]),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalForNoGuardFailure.read Solidity.Yul.Checks.LocalForNoGuardFailure.body fuel (Solidity.Yul.Checks.LocalForNoGuardFailure.state (Solidity.Yul.Checks.LocalForNoGuardFailure.raw 2) world) ≠ .normal next := by
  intro world fuel next
  exact Solidity.Yul.LocalForNoGuardFailure.no_post_normal Solidity.Yul.Checks.LocalForNoGuardFailure.env [] false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForNoGuardFailure.read Solidity.Yul.Checks.LocalForNoGuardFailure.items Solidity.Yul.Checks.LocalForNoGuardFailure.body fuel (Solidity.Yul.Checks.LocalForNoGuardFailure.state (Solidity.Yul.Checks.LocalForNoGuardFailure.raw 2) world) next


theorem postAllFuel : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env) (fuel : Nat) (next : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalForNoGuardFailure.env [.bool]),
 Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalForNoGuardFailure.read Solidity.Yul.Checks.LocalForNoGuardFailure.post Solidity.Yul.Checks.LocalForNoGuardFailure.body fuel (Solidity.Yul.Checks.LocalForNoGuardFailure.state (Solidity.Yul.Checks.LocalForNoGuardFailure.raw 2) world) ≠ .normal next := by
  intro world fuel next
  exact Solidity.Yul.LocalForNoGuardFailure.no_normal Solidity.Yul.Checks.LocalForNoGuardFailure.env [] false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForNoGuardFailure.read (.assign (.local .here) (.bool false)) Solidity.Yul.Checks.LocalForNoGuardFailure.post Solidity.Yul.Checks.LocalForNoGuardFailure.items Solidity.Yul.Checks.LocalForNoGuardFailure.body fuel (Solidity.Yul.Checks.LocalForNoGuardFailure.state (Solidity.Yul.Checks.LocalForNoGuardFailure.raw 2) world) next


theorem counterPrefix : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalForNoGuardFailure.read Solidity.Yul.Checks.LocalForNoGuardFailure.body 8 (Solidity.Yul.Checks.LocalForNoGuardFailure.state (Solidity.Yul.Checks.LocalForNoGuardFailure.raw 2) world) =
 .halted .timeout (Solidity.Yul.Checks.LocalForNoGuardFailure.counterChanged world) := by
  intro world; rfl


theorem guardedCompletion : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env),
 Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoGuardFailure.read Solidity.Yul.Checks.LocalForNoGuardFailure.test Solidity.Yul.Checks.LocalForNoGuardFailure.body 9 (Solidity.Yul.Checks.LocalForNoGuardFailure.state (Solidity.Yul.Checks.LocalForNoGuardFailure.raw 2) world) =
 .normal (Solidity.Yul.Checks.LocalForNoGuardFailure.state Solidity.Yul.Checks.LocalForNoGuardFailure.cleanFalse world) := by
  intro world; rfl


theorem falseInitializerEnters : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalForNoGuardFailure.stop Solidity.Yul.Checks.LocalForNoGuardFailure.body 3 (Solidity.Yul.Checks.LocalForNoGuardFailure.state (Solidity.Yul.Checks.LocalForNoGuardFailure.raw 2) world) =
 .halted .timeout (Solidity.Yul.Checks.LocalForNoGuardFailure.enteredFalse world) := by
  intro world; rfl


theorem dirtyPrefix : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env),
 Solidity.Yul.LocalValues.clean? [.bool,.bool] (Solidity.Yul.Checks.LocalForNoGuardFailure.enteredFalse world).1 = none := by
  intro world; rfl


theorem postFailurePrefix : Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalBoolForNoGuard.yes Solidity.Yul.Checks.LocalBoolForNoGuard.failing Solidity.Yul.Checks.LocalBoolForNoGuard.proof 8 Solidity.Yul.Checks.LocalBoolForNoGuard.initial =
 .halted .timeout Solidity.Yul.Checks.LocalBoolForNoGuard.postFailed := by
  rfl


theorem sourcePostAllFuel : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForNoGuardFailure.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForNoGuardFailure.env))
 (locals next : Solidity.Source.Locals Solidity.Yul.Checks.LocalForNoGuardFailure.env.layout [.bool])
 (world finalWorld : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env),
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := false) (.declInit (τ := .bool) (.local .here) (by rfl)) .none (.some (.assign (.local .here) (.bool false))) (.block Solidity.Yul.Checks.LocalForNoGuardFailure.items)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalForNoGuardFailure.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.LocalForNoGuardFailure.env,finalWorld)) := by
  intro glob frame fuel nps ph locals next world finalWorld
  exact Solidity.Yul.LocalForNoGuardFailure.source_no_normal Solidity.Yul.Checks.LocalForNoGuardFailure.env [] false false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForNoGuardFailure.read (.assign (.local .here) (.bool false)) Solidity.Yul.Checks.LocalForNoGuardFailure.post Solidity.Yul.Checks.LocalForNoGuardFailure.items Solidity.Yul.Checks.LocalForNoGuardFailure.body glob frame fuel nps ph locals next world finalWorld


theorem sourceNoPostAllFuel : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForNoGuardFailure.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForNoGuardFailure.env))
 (locals next : Solidity.Source.Locals Solidity.Yul.Checks.LocalForNoGuardFailure.env.layout [.bool])
 (world finalWorld : Solidity.Source.St Solidity.Yul.Checks.LocalForNoGuardFailure.env),
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := false) (.declInit (τ := .bool) (.local .here) (by rfl)) .none .none (.block Solidity.Yul.Checks.LocalForNoGuardFailure.items)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalForNoGuardFailure.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.LocalForNoGuardFailure.env,finalWorld)) := by
  intro glob frame fuel nps ph locals next world finalWorld
  exact Solidity.Yul.LocalForNoGuardFailure.source_no_post_normal Solidity.Yul.Checks.LocalForNoGuardFailure.env [] false false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForNoGuardFailure.read Solidity.Yul.Checks.LocalForNoGuardFailure.items Solidity.Yul.Checks.LocalForNoGuardFailure.body glob frame fuel nps ph locals next world finalWorld

#print axioms Solidity.Yul.LocalForNoGuardFailure.no_normal
#print axioms Solidity.Yul.LocalForNoGuardFailure.no_post_normal
#print axioms Solidity.Yul.LocalForNoGuardFailure.source_no_normal
#print axioms Solidity.Yul.LocalForNoGuardFailure.source_no_post_normal
#print axioms noPostAllFuel
#print axioms postAllFuel
#print axioms counterPrefix
#print axioms guardedCompletion
#print axioms falseInitializerEnters
#print axioms dirtyPrefix
#print axioms postFailurePrefix
#print axioms sourcePostAllFuel
#print axioms sourceNoPostAllFuel
end Solidity.Yul.Checks.LocalForNoGuardFailure
