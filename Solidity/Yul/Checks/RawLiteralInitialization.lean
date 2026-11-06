import Solidity.Yul.RawLiteralInitialization
import Solidity.Yul.Checks.RawLocalDeclaration

namespace Solidity.Yul.Checks.RawLiteralInitialization
namespace Fixture
export Solidity.Yul.Checks.RawLocalDeclaration (initial)
export Solidity.Yul.Checks.RawLocalDeclaration.Fixture (ctx env dirty flag small)
end Fixture

def afterTrue : Solidity.Yul.RawLocalDeclaration.Snapshot Fixture.env (.bool :: Fixture.ctx.tys) :=
  ⟨.cons (.bool true) Fixture.initial.clean,(.clean (.bool true),Fixture.initial.values),Fixture.initial.world⟩
def afterFalse : Solidity.Yul.RawLocalDeclaration.Snapshot Fixture.env (.bool :: Fixture.ctx.tys) :=
  ⟨.cons (.bool false) Fixture.initial.clean,(.clean (.bool false),Fixture.initial.values),Fixture.initial.world⟩
def declaration : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) := .declInit (.bool true) (by rfl)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys)) := ⟨declaration⟩
def concrete (value : Bool) (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawLiteralInitialization.correct Fixture.env Fixture.ctx.tys value
    [] false ⟨false,false⟩ glob frame fuel nps ph Fixture.initial



theorem outcomes :
  Solidity.Yul.RawLiteralInitialization.run true 0 Solidity.Yul.Checks.RawLiteralInitialization.Fixture.initial = .halted .timeout Solidity.Yul.Checks.RawLiteralInitialization.Fixture.initial ∧
Solidity.Yul.RawLiteralInitialization.run true 1 Solidity.Yul.Checks.RawLiteralInitialization.Fixture.initial = .halted .timeout Solidity.Yul.Checks.RawLiteralInitialization.Fixture.initial ∧
Solidity.Yul.RawLiteralInitialization.run true 2 Solidity.Yul.Checks.RawLiteralInitialization.Fixture.initial = .normal Solidity.Yul.Checks.RawLiteralInitialization.afterTrue ∧
Solidity.Yul.RawLiteralInitialization.run false 2 Solidity.Yul.Checks.RawLiteralInitialization.Fixture.initial = .normal Solidity.Yul.Checks.RawLiteralInitialization.afterFalse := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem values :
  ((Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawLiteralInitialization.afterTrue.values .here).clean?).map
 Solidity.Source.Val.key = some (some 1) ∧
 ((Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawLiteralInitialization.afterFalse.values .here).clean?).map
 Solidity.Source.Val.key = some (some 0) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawLiteralInitialization.afterTrue.values (.there .here)).scalar? =
 some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawLiteralInitialization.afterTrue.values (.there (.there (.there .here)))).scalar? =
 some (Solidity.Yul.word 257) := by
  decide +kernel

theorem nondefault :
  ∀ (env : Solidity.Source.Env),
 Solidity.Source.Val.default env.layout .bool ≠ some (Solidity.Source.Val.bool true) := by
  intro env bad; cases bad

#print axioms Solidity.Yul.RawLiteralInitialization.correct
#print axioms concrete
#print axioms outcomes
#print axioms values
#print axioms nondefault

end Solidity.Yul.Checks.RawLiteralInitialization
