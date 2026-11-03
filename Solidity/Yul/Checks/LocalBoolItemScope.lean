import Solidity.Yul.LocalBoolItemScope
import Solidity.Yul.Checks.LocalBoolItems

namespace Solidity.Yul.Checks.LocalBoolItemScope
namespace Fixture
export Solidity.Yul.Checks.LocalBoolItems.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolItems (initial proof rawProof three rawTwo)
def body : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block Solidity.Yul.Checks.LocalBoolItems.program
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨body⟩
def closed : LocalState Fixture.env Fixture.ctx.tys :=
  (initial.1.set .here (.clean (.bool true)),initial.2)
def cleanInitial : LocalState Fixture.env Fixture.ctx.tys :=
  LocalState.ofClean (Fixture.initial.clean,Fixture.initial.world)
def dirtyTemps : LocalState Fixture.env Solidity.Yul.Checks.LocalBoolItems.C2 :=
  ((.scalar (LocalOperations.boolShape Fixture.env) (word 2),
    (.scalar (LocalOperations.boolShape Fixture.env) (word 257),cleanInitial.1)),cleanInitial.2)
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolItemScope.source_agrees Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
    Solidity.Yul.Checks.LocalBoolItems.C3 Solidity.Yul.Checks.LocalBoolItems.program proof
    glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world



theorem effects : Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalBoolItemScope.proof 8 Solidity.Yul.Checks.LocalBoolItemScope.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolItemScope.three ∧
 Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalBoolItemScope.proof 9 Solidity.Yul.Checks.LocalBoolItemScope.initial = .normal Solidity.Yul.Checks.LocalBoolItemScope.closed ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItemScope.closed.1 .here).clean? = some (Solidity.Source.Val.bool true) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItemScope.closed.1 (.there (.there .here))).scalar? = some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawCopy : Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalBoolItemScope.rawProof 6 Solidity.Yul.Checks.LocalBoolItemScope.initial = .normal Solidity.Yul.Checks.LocalBoolItemScope.initial ∧
 Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolItemScope.Fixture.ctx.tys (Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalBoolItemScope.rawProof 6 Solidity.Yul.Checks.LocalBoolItemScope.initial) = none := by
  exact ⟨rfl,rfl⟩

theorem discardDirty : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolItemScope.Fixture.ctx.tys (.normal Solidity.Yul.Checks.LocalBoolItemScope.dirtyTemps) = none ∧
 Solidity.Yul.LocalBoolItemScope.close Solidity.Yul.Checks.LocalBoolItemScope.rawProof (.normal Solidity.Yul.Checks.LocalBoolItemScope.dirtyTemps) = .normal Solidity.Yul.Checks.LocalBoolItemScope.cleanInitial ∧
 Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolItemScope.Fixture.ctx.tys (Solidity.Yul.LocalBoolItemScope.close Solidity.Yul.Checks.LocalBoolItemScope.rawProof (.normal Solidity.Yul.Checks.LocalBoolItemScope.dirtyTemps)) =
 some (.ok (.normal Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.clean),(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItemScope.Fixture.env,Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.world)) := by
  exact ⟨rfl,rfl,rfl⟩

theorem sourceOutcomes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalBoolItemScope.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalBoolItemScope.Fixture.env)),
 (Solidity.Source.execS glob frame 8 nps ph Solidity.Yul.Checks.LocalBoolItemScope.body Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItemScope.Fixture.env,Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItemScope.Fixture.env,Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.world)) ∧
 (Solidity.Source.execS glob frame 9 nps ph Solidity.Yul.Checks.LocalBoolItemScope.body Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItemScope.Fixture.env,Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.world) =
 (.ok (.normal (Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.clean.set .here (.bool true))),
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItemScope.Fixture.env,Solidity.Yul.Checks.LocalBoolItemScope.Fixture.initial.world)) := by
  intro glob frame nps ph; exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolItemScope.length_mono
#print axioms Solidity.Yul.LocalBoolItemScope.value_inverse
#print axioms Solidity.Yul.LocalBoolItemScope.drop_clean
#print axioms Solidity.Yul.LocalBoolItemScope.suffix
#print axioms Solidity.Yul.LocalBoolItemScope.values_inverse
#print axioms Solidity.Yul.LocalBoolItemScope.cast_clean
#print axioms Solidity.Yul.LocalBoolItemScope.source_restore
#print axioms Solidity.Yul.LocalBoolItemScope.restore_project
#print axioms Solidity.Yul.LocalBoolItemScope.source_agrees
#print axioms concrete
#print axioms effects
#print axioms rawCopy
#print axioms discardDirty
#print axioms sourceOutcomes

end Solidity.Yul.Checks.LocalBoolItemScope
