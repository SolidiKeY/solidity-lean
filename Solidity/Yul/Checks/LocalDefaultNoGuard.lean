import Solidity.Yul.LocalDefaultNoGuard
import Solidity.Yul.Checks.LocalDefaultPostIter
namespace Solidity.Yul.Checks.LocalDefaultNoGuard
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultPostIter.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalDefaultPostIter
 (initial assigned items proof Out postFalse postFault postFaultExpr afterFalsePostBody body)
def witness := Solidity.Yul.Checks.LocalDefaultPostIter.witness
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
 Solidity.Yul.LocalDefaultNoGuard.source_agrees Fixture.env [] false false Fixture.ctx.tys Out
  (.bool false) postFalse items proof glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world
def concreteNoPost (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
 Solidity.Yul.LocalDefaultNoGuard.source_no_post_agrees Fixture.env [] false false Fixture.ctx.tys Out
  items proof glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world
def concreteWorld (fuel : Nat) (state : LocalState Fixture.env Fixture.ctx.tys) :=
 Solidity.Yul.LocalDefaultNoGuard.world_no_post Fixture.env [] false false Fixture.ctx.tys Out items proof fuel state
def neverNoPost (fuel : Nat) (state next : LocalState Fixture.env Fixture.ctx.tys) :=
 Solidity.Yul.LocalDefaultNoGuard.no_normal_no_post Fixture.env [] false false Fixture.ctx.tys Out items proof fuel state next

theorem withPost : Solidity.Yul.LocalDefaultNoGuard.run Solidity.Yul.Checks.LocalDefaultNoGuard.postFalse Solidity.Yul.Checks.LocalDefaultNoGuard.proof 9 Solidity.Yul.Checks.LocalDefaultNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultNoGuard.afterFalsePostBody := by

  rfl

theorem withoutPost : Solidity.Yul.LocalDefaultNoGuard.runNoPost Solidity.Yul.Checks.LocalDefaultNoGuard.proof 9 Solidity.Yul.Checks.LocalDefaultNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultNoGuard.afterFalsePostBody := by

  rfl

theorem partialPost : Solidity.Yul.LocalDefaultNoGuard.run Solidity.Yul.Checks.LocalDefaultNoGuard.postFault Solidity.Yul.Checks.LocalDefaultNoGuard.proof 9 Solidity.Yul.Checks.LocalDefaultNoGuard.initial = .halted .timeout (Solidity.Yul.Checks.LocalDefaultNoGuard.assigned true) := by

  rfl

theorem sourceOmittedPost : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env)),
 (Solidity.Source.forIter glob frame 9 nps ph .none (.some (.bool false)) Solidity.Yul.Checks.LocalDefaultNoGuard.body
 (Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceOmittedNoPost : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env)),
 (Solidity.Source.forIter glob frame 9 nps ph .none .none Solidity.Yul.Checks.LocalDefaultNoGuard.body
 (Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourcePresentGuard : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env)),
 (Solidity.Source.forIter glob frame 9 nps ph (.some (.local .here)) .none Solidity.Yul.Checks.LocalDefaultNoGuard.body
 (Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.clean.set .here (.bool false))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl
#print axioms Solidity.Yul.LocalDefaultNoGuard.source_agrees
#print axioms Solidity.Yul.LocalDefaultNoGuard.source_no_post_agrees
#print axioms Solidity.Yul.LocalDefaultNoGuard.world
#print axioms Solidity.Yul.LocalDefaultNoGuard.no_normal
#print axioms Solidity.Yul.LocalDefaultNoGuard.source_no_normal
#print axioms Solidity.Yul.LocalDefaultNoGuard.world_no_post
#print axioms Solidity.Yul.LocalDefaultNoGuard.no_normal_no_post
#print axioms Solidity.Yul.LocalDefaultNoGuard.source_no_normal_no_post
#print axioms withPost
#print axioms withoutPost
#print axioms partialPost
#print axioms sourceOmittedPost
#print axioms sourceOmittedNoPost
#print axioms sourcePresentGuard
end Solidity.Yul.Checks.LocalDefaultNoGuard
