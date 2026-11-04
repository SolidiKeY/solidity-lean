import Solidity.Yul.LocalBoolFor
import Solidity.Yul.Checks.LocalBoolWhile

namespace Solidity.Yul.Checks.LocalBoolFor
namespace Fixture
export Solidity.Yul.Checks.LocalBoolWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolWhile (initial assigned yes no)
export Solidity.Yul.Checks.LocalBoolInitialization (partialProof)
abbrev LoopCtx := Solidity.Source.STy.bool :: Fixture.ctx.tys
abbrev BodyCtx := Solidity.Source.STy.bool :: LoopCtx
def test : LocalBoolControl.Supported Fixture.env LoopCtx (.local .here) := .base (.local .here)
def items : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ LoopCtx BodyCtx :=
  .stmt (.declInit (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local (.there .here)) (.bool false)))
      (.stmt (.expr (.assign (.local (.there (.there .here))) (.local .here))) .nil))
def proof : LocalBoolItems.Supported Fixture.env [] false ⟨true,false⟩ items :=
  .declaration (.base (.local .here))
    (.expression (.assign (.there .here) (.base (.literal false)))
      (.expression (.assign (.there (.there .here)) (.base (.local .here))) .nil))
def entered : LocalState Fixture.env LoopCtx := ((.clean (.bool true),initial.1),initial.2)
def bodyEntered : LocalState Fixture.env BodyCtx := ((.clean (.bool true),entered.1),entered.2)
def bodyChanged : LocalState Fixture.env BodyCtx :=
  (bodyEntered.1.set (.there .here) (.clean (.bool false)),bodyEntered.2)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .forLoop (.declInit (.bool true) (by rfl)) (.some (.local .here)) .none (.block items)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolFor.source_agrees Fixture.env [] false false false Fixture.ctx.tys BodyCtx
    (.bool true) yes (.local .here) test items proof glob frame fuel nps ph
    Fixture.initial.clean Fixture.initial.world

theorem stages : Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.yes Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 2 Solidity.Yul.Checks.LocalBoolFor.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolFor.initial ∧
Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.yes Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 3 Solidity.Yul.Checks.LocalBoolFor.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolFor.entered ∧
Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.yes Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 6 Solidity.Yul.Checks.LocalBoolFor.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolFor.bodyEntered ∧
Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.yes Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 8 Solidity.Yul.Checks.LocalBoolFor.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolFor.bodyChanged := by

  exact ⟨rfl,rfl,rfl,rfl⟩

theorem completion : Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.yes Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 9 Solidity.Yul.Checks.LocalBoolFor.initial = .normal (Solidity.Yul.Checks.LocalBoolFor.assigned true) ∧
Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.no Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 3 Solidity.Yul.Checks.LocalBoolFor.initial = .normal Solidity.Yul.Checks.LocalBoolFor.initial := by

  exact ⟨rfl,rfl⟩

theorem initializerEffects : Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.partialProof Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 5 Solidity.Yul.Checks.LocalBoolFor.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolFor.assigned true) := by

  rfl

theorem rawProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolFor.Fixture.ctx.tys (Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolFor.yes Solidity.Yul.Checks.LocalBoolFor.test Solidity.Yul.Checks.LocalBoolFor.proof 9 Solidity.Yul.Checks.LocalBoolFor.initial) = none := by

  rfl

#print axioms Solidity.Yul.LocalBoolFor.source_agrees
#print axioms concrete
#print axioms stages
#print axioms completion
#print axioms initializerEffects
#print axioms rawProjection
end Solidity.Yul.Checks.LocalBoolFor
