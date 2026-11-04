import Solidity.Yul.LocalBoolDoWhile
import Solidity.Yul.Checks.LocalBoolWhile

namespace Solidity.Yul.Checks.LocalBoolDoWhile
namespace Fixture
export Solidity.Yul.Checks.LocalBoolWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolWhile (proof items initial assigned one repeatedOne yes no readProof)
def failingCondition : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool :=
  .binary .and (.assign (.local .here) (.bool true))
    (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.bool false)))))))
def failing : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys failingCondition :=
  .and (.assign .here (.base (.literal true)))
    (.not (.not (.not (.not (.not (.not (.base (.literal false))))))))
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .doWhile (.block items) (.local .here)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolDoWhile.source_agrees Fixture.env [] false false false Fixture.ctx.tys
    (.bool :: Fixture.ctx.tys) (.local .here) readProof items proof glob frame fuel nps ph
    (Fixture.initial.clean.set .here (.bool true)) Fixture.initial.world

theorem bodyFirst : Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.no Solidity.Yul.Checks.LocalBoolDoWhile.proof 2 Solidity.Yul.Checks.LocalBoolDoWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolDoWhile.initial ∧
Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.no Solidity.Yul.Checks.LocalBoolDoWhile.proof 7 Solidity.Yul.Checks.LocalBoolDoWhile.initial = .normal (Solidity.Yul.Checks.LocalBoolDoWhile.assigned false) ∧
Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.no Solidity.Yul.Checks.LocalBoolDoWhile.proof 7 Solidity.Yul.Checks.LocalBoolDoWhile.initial = .normal Solidity.Yul.Checks.LocalBoolDoWhile.initial := by

  exact ⟨rfl,rfl,rfl⟩

theorem stages : Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.readProof Solidity.Yul.Checks.LocalBoolDoWhile.proof 5 Solidity.Yul.Checks.LocalBoolDoWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolDoWhile.one ∧
Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.readProof Solidity.Yul.Checks.LocalBoolDoWhile.proof 7 Solidity.Yul.Checks.LocalBoolDoWhile.initial = .normal (Solidity.Yul.Checks.LocalBoolDoWhile.assigned false) := by

  exact ⟨rfl,rfl⟩

theorem conditionEffects : Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.failing Solidity.Yul.Checks.LocalBoolDoWhile.proof 7 Solidity.Yul.Checks.LocalBoolDoWhile.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolDoWhile.assigned true) := by

  rfl

theorem recursion : Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.yes Solidity.Yul.Checks.LocalBoolDoWhile.proof 7 Solidity.Yul.Checks.LocalBoolDoWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolDoWhile.repeatedOne := by

  rfl

theorem rawProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolDoWhile.Fixture.ctx.tys (Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoWhile.readProof Solidity.Yul.Checks.LocalBoolDoWhile.proof 7 Solidity.Yul.Checks.LocalBoolDoWhile.initial) = none := by

  rfl

#print axioms Solidity.Yul.LocalBoolDoWhile.source_agrees
#print axioms concrete
#print axioms bodyFirst
#print axioms stages
#print axioms conditionEffects
#print axioms recursion
#print axioms rawProjection
end Solidity.Yul.Checks.LocalBoolDoWhile
