import Solidity.Yul.LocalBoolDoDivergence
import Solidity.Yul.Checks.LocalBoolDoWhile

namespace Solidity.Yul.Checks.LocalBoolDoDivergence
namespace Fixture
export Solidity.Yul.Checks.LocalBoolDoWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolDoWhile (proof items initial assigned no readProof)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .doWhile (.block items) (.bool true)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def bodyWitness : Nonempty (LocalBoolItems.Supported Fixture.env [] false ⟨true,false⟩ items) := ⟨proof⟩
def rawConcrete (fuel : Nat) (next : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalBoolDoDivergence.no_normal Fixture.env [] false false Fixture.ctx.tys
    (.bool :: Fixture.ctx.tys) items proof fuel initial next
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env))
    (next : Solidity.Source.Locals Fixture.env.layout Fixture.ctx.tys)
    (world : Solidity.Source.St Fixture.env) :=
  Solidity.Yul.LocalBoolDoDivergence.source_no_normal Fixture.env [] false false false
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) items proof glob frame fuel nps ph
    (Fixture.initial.clean.set .here (.bool true)) next Fixture.initial.world world

theorem controls : Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoDivergence.no Solidity.Yul.Checks.LocalBoolDoDivergence.proof 7 Solidity.Yul.Checks.LocalBoolDoDivergence.initial = .normal (Solidity.Yul.Checks.LocalBoolDoDivergence.assigned false) ∧
Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolDoDivergence.readProof Solidity.Yul.Checks.LocalBoolDoDivergence.proof 7 Solidity.Yul.Checks.LocalBoolDoDivergence.initial = .normal (Solidity.Yul.Checks.LocalBoolDoDivergence.assigned false) := by

  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolDoDivergence.no_normal
#print axioms Solidity.Yul.LocalBoolDoDivergence.source_no_normal
#print axioms rawConcrete
#print axioms concrete
#print axioms controls
end Solidity.Yul.Checks.LocalBoolDoDivergence
