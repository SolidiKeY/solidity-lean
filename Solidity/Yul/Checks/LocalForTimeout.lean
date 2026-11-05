import Solidity.Yul.LocalForTimeout
import Solidity.Yul.Checks.LocalForNoGuardFailure

namespace Solidity.Yul.Checks.LocalForTimeout
export LocalForNoGuardFailure (env state raw cleanFalse read stop test items body post counterChanged)
def witness : Nonempty (LocalBoolItems.Supported env [] false ⟨true,false⟩ items) := ⟨body⟩
theorem postTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env) (fuel : Nat),
 ∃ (reached : Solidity.Source.RCtx) (next : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalForTimeout.env reached),
 Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.post Solidity.Yul.Checks.LocalForTimeout.body fuel (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) = .halted .timeout next := by
  intro world fuel
  exact Solidity.Yul.LocalForTimeout.omitted Solidity.Yul.Checks.LocalForTimeout.env [] false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForTimeout.read (.assign (.local .here) (.bool false)) Solidity.Yul.Checks.LocalForTimeout.post Solidity.Yul.Checks.LocalForTimeout.items Solidity.Yul.Checks.LocalForTimeout.body fuel (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world)


theorem noPostTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env) (fuel : Nat),
 ∃ (reached : Solidity.Source.RCtx) (next : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalForTimeout.env reached),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.body fuel (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) = .halted .timeout next := by
  intro world fuel
  exact Solidity.Yul.LocalForTimeout.omitted_no_post Solidity.Yul.Checks.LocalForTimeout.env [] false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.items Solidity.Yul.Checks.LocalForTimeout.body fuel (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world)


theorem zeroCaller : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.body 0 (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) := by
  intro world; rfl


theorem retainedCounter : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env),
 Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.body 8 (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForTimeout.counterChanged world) := by
  intro world; rfl


theorem postEffects : Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalBoolForNoGuard.yes Solidity.Yul.Checks.LocalBoolForNoGuard.failing Solidity.Yul.Checks.LocalBoolForNoGuard.proof 8 Solidity.Yul.Checks.LocalBoolForNoGuard.initial =
 .halted .timeout Solidity.Yul.Checks.LocalBoolForNoGuard.postFailed := by
  rfl


theorem presentGuardNormal : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env),
 Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.test Solidity.Yul.Checks.LocalForTimeout.body 9 (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForTimeout.state Solidity.Yul.Checks.LocalForTimeout.cleanFalse world) := by
  intro world; rfl


theorem falseGuardNormal : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env),
 Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForTimeout.stop Solidity.Yul.Checks.LocalForTimeout.test Solidity.Yul.Checks.LocalForTimeout.body 3 (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) := by
  intro world; rfl


theorem nonTimeoutRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env) (fuel : Nat) (reached : Solidity.Source.RCtx) (halt : Solidity.Source.Halt)
 (next : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalForTimeout.env reached), halt ≠ .timeout →
 Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.body fuel (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) ≠ .halted halt next := by
  intro world fuel reached halt next different failed
  exact different (Solidity.Yul.LocalForTimeout.no_post_halt_kind Solidity.Yul.Checks.LocalForTimeout.env [] false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForTimeout.read (.bool true) (.base (.literal true)) Solidity.Yul.Checks.LocalForTimeout.items Solidity.Yul.Checks.LocalForTimeout.body fuel (Solidity.Yul.Checks.LocalForTimeout.state (Solidity.Yul.Checks.LocalForTimeout.raw 2) world) reached halt next failed)


theorem sourcePostTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForTimeout.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForTimeout.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalForTimeout.env.layout [.bool]) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env),
 ∃ finalWorld : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env,
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := false) (.declInit (τ := .bool) (.local .here) (by rfl)) .none (.some (.assign (.local .here) (.bool false))) (.block Solidity.Yul.Checks.LocalForTimeout.items)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalForTimeout.env,world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalForTimeout.env,finalWorld)) := by
  intro glob frame fuel nps ph locals world
  exact Solidity.Yul.LocalForTimeout.source_omitted Solidity.Yul.Checks.LocalForTimeout.env [] false false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForTimeout.read (.assign (.local .here) (.bool false)) Solidity.Yul.Checks.LocalForTimeout.post Solidity.Yul.Checks.LocalForTimeout.items Solidity.Yul.Checks.LocalForTimeout.body glob frame fuel nps ph locals world


theorem sourceNoPostTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalForTimeout.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalForTimeout.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalForTimeout.env.layout [.bool]) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env),
 ∃ finalWorld : Solidity.Source.St Solidity.Yul.Checks.LocalForTimeout.env,
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := false) (.declInit (τ := .bool) (.local .here) (by rfl)) .none .none (.block Solidity.Yul.Checks.LocalForTimeout.items)) locals).run
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalForTimeout.env,world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalForTimeout.env,finalWorld)) := by
  intro glob frame fuel nps ph locals world
  exact Solidity.Yul.LocalForTimeout.source_omitted_no_post Solidity.Yul.Checks.LocalForTimeout.env [] false false false [.bool] Solidity.Yul.Checks.LocalForNoPostHorizon.Out (.local .here) Solidity.Yul.Checks.LocalForTimeout.read Solidity.Yul.Checks.LocalForTimeout.items Solidity.Yul.Checks.LocalForTimeout.body glob frame fuel nps ph locals world

#print axioms Solidity.Yul.LocalForTimeout.halt_kind
#print axioms Solidity.Yul.LocalForTimeout.no_post_halt_kind
#print axioms Solidity.Yul.LocalForTimeout.omitted
#print axioms Solidity.Yul.LocalForTimeout.omitted_no_post
#print axioms Solidity.Yul.LocalForTimeout.source_omitted
#print axioms Solidity.Yul.LocalForTimeout.source_omitted_no_post
#print axioms postTimeout
#print axioms noPostTimeout
#print axioms zeroCaller
#print axioms retainedCounter
#print axioms postEffects
#print axioms presentGuardNormal
#print axioms falseGuardNormal
#print axioms nonTimeoutRefused
#print axioms sourcePostTimeout
#print axioms sourceNoPostTimeout
end Solidity.Yul.Checks.LocalForTimeout
