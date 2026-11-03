import Solidity.Yul.LocalBoolIf
import Solidity.Yul.Checks.LocalBoolItemScope
import Solidity.Yul.Checks.LocalBoolInitialization

namespace Solidity.Yul.Checks.LocalBoolIf
namespace Fixture
export Solidity.Yul.Checks.LocalBoolItems.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolItems (initial proof three)
def yes : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool true) :=
  .base (.literal true)
def no : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool false) :=
  .base (.literal false)
def assignNo : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys
    (.assign (.local .here) (.bool false)) := .assign .here (.base (.literal false))
def empty : LocalBoolItems.Supported Fixture.env [] false ⟨false,false⟩
    (Solidity.Source.RItems.nil (Γ := Fixture.ctx.tys)) := .nil
def body : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .ifThen (.bool true) (.block Solidity.Yul.Checks.LocalBoolItems.program)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨body⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolIf.source_agrees Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
    Solidity.Yul.Checks.LocalBoolItems.C3 (.bool true) yes
    Solidity.Yul.Checks.LocalBoolItems.program proof glob frame fuel nps ph
    Fixture.initial.clean Fixture.initial.world

theorem branches : Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolIf.yes Solidity.Yul.Checks.LocalBoolIf.proof 9 Solidity.Yul.Checks.LocalBoolIf.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolIf.three ∧
Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolIf.yes Solidity.Yul.Checks.LocalBoolIf.proof 10 Solidity.Yul.Checks.LocalBoolIf.initial = .normal Solidity.Yul.Checks.LocalBoolItemScope.closed ∧
Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolIf.no Solidity.Yul.Checks.LocalBoolIf.proof 2 Solidity.Yul.Checks.LocalBoolIf.initial = .normal Solidity.Yul.Checks.LocalBoolIf.initial ∧
Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolIf.yes Solidity.Yul.Checks.LocalBoolIf.proof 2 Solidity.Yul.Checks.LocalBoolIf.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolIf.initial := by

  exact ⟨rfl,rfl,rfl,rfl⟩

theorem conditionEffects : Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolIf.assignNo Solidity.Yul.Checks.LocalBoolIf.proof 3 Solidity.Yul.Checks.LocalBoolIf.initial = .normal (Solidity.Yul.Checks.LocalBoolInitialization.assigned false) ∧
Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolInitialization.partialProof Solidity.Yul.Checks.LocalBoolIf.proof 4 Solidity.Yul.Checks.LocalBoolIf.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolInitialization.assigned true) := by

  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolIf.restore_self
#print axioms Solidity.Yul.LocalBoolIf.source_agrees
#print axioms concrete
#print axioms branches
#print axioms conditionEffects
theorem rawTruth : Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolInitialization.readProof Solidity.Yul.Checks.LocalBoolIf.proof 3 Solidity.Yul.Checks.LocalBoolIf.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolIf.initial ∧
Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolIf.Fixture.ctx.tys (.normal Solidity.Yul.Checks.LocalBoolIf.initial) = none := by

  exact ⟨rfl,rfl⟩

#print axioms rawTruth
end Solidity.Yul.Checks.LocalBoolIf
