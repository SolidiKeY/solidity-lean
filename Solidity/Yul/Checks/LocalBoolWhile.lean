import Solidity.Yul.LocalBoolWhile
import Solidity.Yul.Checks.LocalBoolIf

namespace Solidity.Yul.Checks.LocalBoolWhile
namespace Fixture
export Solidity.Yul.Checks.LocalBoolIf.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolIf (yes no)
export Solidity.Yul.Checks.LocalBoolInitialization (readProof partialProof initial assigned)
def items : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys
    (.bool :: Fixture.ctx.tys) :=
  .stmt (.declInit (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local (.there .here)) (.bool false))) .nil)
def proof : LocalBoolItems.Supported Fixture.env [] false ⟨true,false⟩ items :=
  .declaration (.base (.local .here))
    (.expression (.assign (.there .here) (.base (.literal false))) .nil)
def one : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  ((initial.1.get .here,initial.1),initial.2)
def repeatedOne : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  ((.clean (.bool false),(assigned false).1),(assigned false).2)
def cleanTrue : LocalState Fixture.env Fixture.ctx.tys :=
  LocalState.ofClean (Fixture.initial.clean.set .here (.bool true),Fixture.initial.world)
def body : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .whileLoop (.local .here) (.block items)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨body⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolWhile.source_agrees Fixture.env [] false false false
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) (.local .here) readProof items proof
    glob frame fuel nps ph (Fixture.initial.clean.set .here (.bool true)) Fixture.initial.world
theorem iteration : ∀ (fuel : Nat) (state : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalBoolWhile.Fixture.env Solidity.Yul.Checks.LocalBoolWhile.Fixture.ctx.tys),
Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.yes Solidity.Yul.Checks.LocalBoolWhile.proof (fuel+7) state = Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.yes Solidity.Yul.Checks.LocalBoolWhile.proof (fuel+6) (state.1.set .here (.clean (.bool false)),state.2) := by

  intro fuel state
  rfl


theorem stages : Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.readProof Solidity.Yul.Checks.LocalBoolWhile.proof 5 Solidity.Yul.Checks.LocalBoolWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolWhile.one ∧
Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.readProof Solidity.Yul.Checks.LocalBoolWhile.proof 7 Solidity.Yul.Checks.LocalBoolWhile.initial = .normal (Solidity.Yul.Checks.LocalBoolWhile.assigned false) ∧
Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.no Solidity.Yul.Checks.LocalBoolWhile.proof 2 Solidity.Yul.Checks.LocalBoolWhile.initial = .normal Solidity.Yul.Checks.LocalBoolWhile.initial := by

  exact ⟨rfl,rfl,rfl⟩

theorem conditionEffects : Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.partialProof Solidity.Yul.Checks.LocalBoolWhile.proof 4 Solidity.Yul.Checks.LocalBoolWhile.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolWhile.assigned true) := by

  rfl

theorem repeated : Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.yes Solidity.Yul.Checks.LocalBoolWhile.proof 8 Solidity.Yul.Checks.LocalBoolWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolWhile.repeatedOne ∧
Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.yes Solidity.Yul.Checks.LocalBoolWhile.proof 12 Solidity.Yul.Checks.LocalBoolWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolWhile.repeatedOne := by

  constructor
  · rw [Solidity.Yul.Checks.LocalBoolWhile.iteration 1,Solidity.Yul.Checks.LocalBoolWhile.iteration 0]
    rfl
  · rw [Solidity.Yul.Checks.LocalBoolWhile.iteration 5,Solidity.Yul.Checks.LocalBoolWhile.iteration 4,
      Solidity.Yul.Checks.LocalBoolWhile.iteration 3,Solidity.Yul.Checks.LocalBoolWhile.iteration 2,
      Solidity.Yul.Checks.LocalBoolWhile.iteration 1,Solidity.Yul.Checks.LocalBoolWhile.iteration 0]
    rfl

theorem rawProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolWhile.Fixture.ctx.tys (Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhile.readProof Solidity.Yul.Checks.LocalBoolWhile.proof 7 Solidity.Yul.Checks.LocalBoolWhile.initial) = none ∧
(Solidity.Yul.Checks.LocalBoolWhile.assigned false).1.get (.there (.there .here)) = Solidity.Yul.Checks.LocalBoolWhile.initial.1.get (.there (.there .here)) := by

  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolWhile.source_agrees
#print axioms concrete
#print axioms iteration
#print axioms stages
#print axioms conditionEffects
#print axioms repeated
#print axioms rawProjection
end Solidity.Yul.Checks.LocalBoolWhile
