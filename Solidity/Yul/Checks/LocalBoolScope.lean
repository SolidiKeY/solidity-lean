import Solidity.Yul.LocalBoolScope
import Solidity.Yul.Checks.LocalBoolInitialization

namespace Solidity.Yul.Checks.LocalBoolScope
namespace Fixture
export Solidity.Yul.Checks.LocalBoolInitialization.Fixture (ctx env initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolInitialization (initial assigned readProof partialProof skipProof)
def body : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt Solidity.Yul.Checks.LocalBoolInitialization.declaration .nil)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨body⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolScope.source_agrees Fixture.env Fixture.ctx.tys
    Solidity.Yul.Checks.LocalBoolInitialization.partialExpr partialProof
    glob frame fuel nps ph [] false ⟨false,false⟩ Fixture.initial.clean Fixture.initial.world



theorem effects : Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.partialProof 5 Solidity.Yul.Checks.LocalBoolScope.initial = (.error .timeout,Solidity.Yul.Checks.LocalBoolScope.initial) ∧
 Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.partialProof 6 Solidity.Yul.Checks.LocalBoolScope.initial = (.error .timeout,Solidity.Yul.Checks.LocalBoolScope.assigned true) ∧
 Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.partialProof 7 Solidity.Yul.Checks.LocalBoolScope.initial = (.ok (),Solidity.Yul.Checks.LocalBoolScope.assigned true) ∧
 Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.skipProof 6 Solidity.Yul.Checks.LocalBoolScope.initial = (.ok (),Solidity.Yul.Checks.LocalBoolScope.assigned false) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawCopy : Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.readProof 4 Solidity.Yul.Checks.LocalBoolScope.initial = (.ok (),Solidity.Yul.Checks.LocalBoolScope.initial) ∧
 Solidity.Yul.LocalBoolScope.project (Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.readProof 4 Solidity.Yul.Checks.LocalBoolScope.initial) = none ∧
 (Solidity.Yul.LocalValues.get (Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.readProof 4 Solidity.Yul.Checks.LocalBoolScope.initial).2.1 .here).scalar? = some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get (Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.partialProof 7 Solidity.Yul.Checks.LocalBoolScope.initial).2.1 (.there (.there .here))).scalar? = some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem notRollback : (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolScope.initial.1 .here).scalar? = some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get (Solidity.Yul.LocalBoolScope.run Solidity.Yul.Checks.LocalBoolScope.partialProof 6 Solidity.Yul.Checks.LocalBoolScope.initial).2.1 .here).clean? =
 some (Solidity.Source.Val.bool true) := by
  exact ⟨rfl,rfl⟩

theorem sourceOutcomes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalBoolScope.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalBoolScope.Fixture.env)),
 (Solidity.Source.execS glob frame 6 nps ph Solidity.Yul.Checks.LocalBoolScope.body Solidity.Yul.Checks.LocalBoolScope.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolScope.Fixture.env,Solidity.Yul.Checks.LocalBoolScope.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolScope.Fixture.env,Solidity.Yul.Checks.LocalBoolScope.Fixture.initial.world)) ∧
 (Solidity.Source.execS glob frame 7 nps ph Solidity.Yul.Checks.LocalBoolScope.body Solidity.Yul.Checks.LocalBoolScope.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolScope.Fixture.env,Solidity.Yul.Checks.LocalBoolScope.Fixture.initial.world) =
 (.ok (.normal (Solidity.Yul.Checks.LocalBoolScope.Fixture.initial.clean.set .here (.bool true))),
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolScope.Fixture.env,Solidity.Yul.Checks.LocalBoolScope.Fixture.initial.world)) := by
  intro glob frame nps ph; exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolScope.source_agrees
#print axioms concrete
#print axioms effects
#print axioms rawCopy
#print axioms notRollback
#print axioms sourceOutcomes

end Solidity.Yul.Checks.LocalBoolScope
