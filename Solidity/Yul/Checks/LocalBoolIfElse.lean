import Solidity.Yul.LocalBoolIfElse
import Solidity.Yul.Checks.LocalBoolIf

namespace Solidity.Yul.Checks.LocalBoolIfElse
namespace Fixture
export Solidity.Yul.Checks.LocalBoolIf.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolIf (yes no assignNo)
export Solidity.Yul.Checks.LocalBoolItems (proof initial three)
def noItems : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
    (.bool :: .bool :: Fixture.ctx.tys) :=
  .stmt (.declInit (.bool false) (by rfl)) (.stmt (.declInit (.bool true) (by rfl)) .nil)
def noProof : LocalBoolItems.Supported Fixture.env [] false ⟨false,false⟩ noItems :=
  .declaration (.base (.literal false)) (.declaration (.base (.literal true)) .nil)
def noOne : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  ((.clean (.bool false),initial.1),initial.2)
def body : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .ifElse (.bool true) (.block Solidity.Yul.Checks.LocalBoolItems.program) (.block noItems)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨body⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolIfElse.source_agrees Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
    Solidity.Yul.Checks.LocalBoolItems.C3 (.bool :: .bool :: Fixture.ctx.tys)
    (.bool true) yes Solidity.Yul.Checks.LocalBoolItems.program proof noItems noProof
    glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

theorem branches : Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolIfElse.yes Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 9 Solidity.Yul.Checks.LocalBoolIfElse.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolIfElse.three ∧
Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolIfElse.yes Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 10 Solidity.Yul.Checks.LocalBoolIfElse.initial = .normal Solidity.Yul.Checks.LocalBoolItemScope.closed ∧
Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolIfElse.no Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 5 Solidity.Yul.Checks.LocalBoolIfElse.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolIfElse.noOne ∧
Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolIfElse.no Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 6 Solidity.Yul.Checks.LocalBoolIfElse.initial = .normal Solidity.Yul.Checks.LocalBoolIfElse.initial := by

  exact ⟨rfl,rfl,rfl,rfl⟩

theorem conditionEffects : Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolIfElse.assignNo Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 6 Solidity.Yul.Checks.LocalBoolIfElse.initial = .normal (Solidity.Yul.Checks.LocalBoolInitialization.assigned false) ∧
Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolInitialization.partialProof Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 4 Solidity.Yul.Checks.LocalBoolIfElse.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolInitialization.assigned true) := by

  exact ⟨rfl,rfl⟩

theorem rawTruth : Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolInitialization.readProof Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 10 Solidity.Yul.Checks.LocalBoolIfElse.initial = .normal Solidity.Yul.Checks.LocalBoolItemScope.closed ∧
Solidity.Yul.LocalBoolIfElse.run Solidity.Yul.Checks.LocalBoolIfElse.no Solidity.Yul.Checks.LocalBoolIfElse.proof Solidity.Yul.Checks.LocalBoolIfElse.noProof 10 Solidity.Yul.Checks.LocalBoolIfElse.initial = .normal Solidity.Yul.Checks.LocalBoolIfElse.initial ∧
Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolIfElse.Fixture.ctx.tys (.normal Solidity.Yul.Checks.LocalBoolItemScope.closed) = none := by

  exact ⟨rfl,rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolIfElse.source_agrees
#print axioms concrete
#print axioms branches
#print axioms conditionEffects
#print axioms rawTruth
end Solidity.Yul.Checks.LocalBoolIfElse
