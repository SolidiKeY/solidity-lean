import Solidity.Yul.LocalBoolDivergence
import Solidity.Yul.Checks.LocalBoolWhile

namespace Solidity.Yul.Checks.LocalBoolDivergence
namespace Fixture
export Solidity.Yul.Checks.LocalBoolWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolWhile (proof items initial assigned yes no readProof)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .whileLoop (.bool true) (.block items)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def bodyWitness : Nonempty (LocalBoolItems.Supported Fixture.env [] false ⟨true,false⟩ items) := ⟨proof⟩
def rawConcrete (fuel : Nat) (next : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalBoolDivergence.no_normal Fixture.env [] false false Fixture.ctx.tys
    (.bool :: Fixture.ctx.tys) items proof fuel initial next
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env))
    (next : Solidity.Source.Locals Fixture.env.layout Fixture.ctx.tys)
    (world : Solidity.Source.St Fixture.env) :=
  Solidity.Yul.LocalBoolDivergence.source_no_normal Fixture.env [] false false false
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) items proof glob frame fuel nps ph
    (Fixture.initial.clean.set .here (.bool true)) next Fixture.initial.world world

theorem controls : Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolDivergence.no Solidity.Yul.Checks.LocalBoolDivergence.proof 2 Solidity.Yul.Checks.LocalBoolDivergence.initial = .normal Solidity.Yul.Checks.LocalBoolDivergence.initial ∧
Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolDivergence.readProof Solidity.Yul.Checks.LocalBoolDivergence.proof 7 Solidity.Yul.Checks.LocalBoolDivergence.initial = .normal (Solidity.Yul.Checks.LocalBoolDivergence.assigned false) := by

  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolDivergence.no_normal
#print axioms Solidity.Yul.LocalBoolDivergence.source_no_normal
#print axioms rawConcrete
#print axioms concrete
#print axioms controls
end Solidity.Yul.Checks.LocalBoolDivergence
