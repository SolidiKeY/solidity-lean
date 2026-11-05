import Solidity.Yul.LocalBoolForNoGuard
import Solidity.Yul.Checks.LocalBoolForPost

namespace Solidity.Yul.Checks.LocalBoolForNoGuard
namespace Fixture
export Solidity.Yul.Checks.LocalBoolForPost.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolForPost
  (LoopCtx BodyCtx initial assigned yes no test entered items proof post failing postFailed partialProof)
def enteredFalse : LocalState Fixture.env LoopCtx := ((.clean (.bool false),initial.1),initial.2)
def repeatFalse : LocalState Fixture.env BodyCtx :=
  ((.clean (.bool false),(.clean (.bool false),(assigned true).1)),(assigned true).2)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .forLoop (.declInit (.bool true) (by rfl)) .none
    (.some (.assign (.local .here) (.bool false))) (.block items)
def falseInit (guard : Solidity.Source.ROptBool Fixture.env LoopCtx) :
    Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .forLoop (.declInit (.bool false) (by rfl)) guard
    (.some (.assign (.local .here) (.bool false))) (.block items)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolForNoGuard.source_agrees Fixture.env [] false false false Fixture.ctx.tys BodyCtx
    (.bool true) yes (.assign (.local .here) (.bool false)) post
    items proof glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world
def concreteNoPost (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolForNoGuard.source_no_post_agrees Fixture.env [] false false false Fixture.ctx.tys BodyCtx
    (.bool true) yes Solidity.Yul.Checks.LocalBoolFor.items Solidity.Yul.Checks.LocalBoolFor.proof
    glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

theorem guards : Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalBoolForNoGuard.yes Solidity.Yul.Checks.LocalBoolForNoGuard.post Solidity.Yul.Checks.LocalBoolForNoGuard.proof 8 Solidity.Yul.Checks.LocalBoolForNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForNoGuard.repeatFalse ∧
Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForNoGuard.yes Solidity.Yul.Checks.LocalBoolForNoGuard.test Solidity.Yul.Checks.LocalBoolForNoGuard.post Solidity.Yul.Checks.LocalBoolForNoGuard.proof 8 Solidity.Yul.Checks.LocalBoolForNoGuard.initial = .normal (Solidity.Yul.Checks.LocalBoolForNoGuard.assigned true) ∧
Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalBoolForNoGuard.no Solidity.Yul.Checks.LocalBoolForNoGuard.post Solidity.Yul.Checks.LocalBoolForNoGuard.proof 3 Solidity.Yul.Checks.LocalBoolForNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForNoGuard.enteredFalse ∧
Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForNoGuard.no Solidity.Yul.Checks.LocalBoolForNoGuard.test Solidity.Yul.Checks.LocalBoolForNoGuard.post Solidity.Yul.Checks.LocalBoolForNoGuard.proof 3 Solidity.Yul.Checks.LocalBoolForNoGuard.initial = .normal Solidity.Yul.Checks.LocalBoolForNoGuard.initial := by

  exact ⟨rfl,rfl,rfl,rfl⟩

theorem noPost : Solidity.Yul.LocalBoolForNoGuard.runNoPost Solidity.Yul.Checks.LocalBoolForNoGuard.yes Solidity.Yul.Checks.LocalBoolFor.proof 9 Solidity.Yul.Checks.LocalBoolForNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForNoGuard.repeatFalse := by

  rfl

theorem partialEffects : Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalBoolForNoGuard.yes Solidity.Yul.Checks.LocalBoolForNoGuard.failing Solidity.Yul.Checks.LocalBoolForNoGuard.proof 8 Solidity.Yul.Checks.LocalBoolForNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForNoGuard.postFailed ∧
Solidity.Yul.LocalBoolForNoGuard.run Solidity.Yul.Checks.LocalBoolForNoGuard.partialProof Solidity.Yul.Checks.LocalBoolForNoGuard.post Solidity.Yul.Checks.LocalBoolForNoGuard.proof 5 Solidity.Yul.Checks.LocalBoolForNoGuard.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolForNoGuard.assigned true) := by

  exact ⟨rfl,rfl⟩

theorem sourceControls : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.env)),
 (Solidity.Source.execS glob frame 3 nps ph (Solidity.Yul.Checks.LocalBoolForNoGuard.falseInit .none) Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.env,Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.env,Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.initial.world)) ∧
 (Solidity.Source.execS glob frame 3 nps ph (Solidity.Yul.Checks.LocalBoolForNoGuard.falseInit (.some (.local .here))) Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.env,Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.initial.world) =
 (.ok (.normal Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.initial.clean),(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.env,Solidity.Yul.Checks.LocalBoolForNoGuard.Fixture.initial.world)) := by

  intro glob frame nps ph
  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolForNoGuard.iter_eq
#print axioms Solidity.Yul.LocalBoolForNoGuard.for_eq
#print axioms Solidity.Yul.LocalBoolForNoGuard.source_agrees
#print axioms Solidity.Yul.LocalBoolForNoGuard.source_no_post_agrees
#print axioms concrete
#print axioms concreteNoPost
#print axioms guards
#print axioms noPost
#print axioms partialEffects
#print axioms sourceControls
end Solidity.Yul.Checks.LocalBoolForNoGuard
