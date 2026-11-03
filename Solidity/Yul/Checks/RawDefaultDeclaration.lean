import Solidity.Yul.RawDefaultDeclaration
import Solidity.Yul.Checks.RawLocalDeclaration

namespace Solidity.Yul.Checks.RawDefaultDeclaration
namespace Fixture
export Solidity.Yul.Checks.RawLocalDeclaration (initial)
export Solidity.Yul.Checks.RawLocalDeclaration.Fixture (ctx env dirty flag small)
end Fixture

def u8 := Solidity.Yul.RawDefaultDeclaration.intDefault Fixture.env Solidity.Source.IntTy.u8
def u256 := Solidity.Yul.RawDefaultDeclaration.intDefault Fixture.env Solidity.Source.IntTy.u256
def after8 : Solidity.Yul.RawLocalDeclaration.Snapshot Fixture.env
    (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ⟨.cons u8.value Fixture.initial.clean,(.clean u8.value,Fixture.initial.values),Fixture.initial.world⟩
def after256 : Solidity.Yul.RawLocalDeclaration.Snapshot Fixture.env
    (.int Solidity.Source.IntTy.u256 :: Fixture.ctx.tys) :=
  ⟨.cons u256.value Fixture.initial.clean,(.clean u256.value,Fixture.initial.values),Fixture.initial.world⟩
def declaration : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) := .declVar _
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys)) := ⟨declaration⟩
def concrete8 (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawDefaultDeclaration.int_correct Fixture.env Fixture.ctx.tys Solidity.Source.IntTy.u8
    [] false ⟨false,false⟩ glob frame fuel nps ph Fixture.initial
def concrete256 (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawDefaultDeclaration.int_correct Fixture.env Fixture.ctx.tys Solidity.Source.IntTy.u256
    [] false ⟨false,false⟩ glob frame fuel nps ph Fixture.initial

theorem outcomes : Solidity.Yul.RawDefaultDeclaration.run Solidity.Yul.Checks.RawDefaultDeclaration.u8 0 Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.initial = .halted .timeout Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.initial ∧
Solidity.Yul.RawDefaultDeclaration.run Solidity.Yul.Checks.RawDefaultDeclaration.u8 1 Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.initial = .halted .timeout Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.initial ∧
Solidity.Yul.RawDefaultDeclaration.run Solidity.Yul.Checks.RawDefaultDeclaration.u8 2 Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.initial = .normal Solidity.Yul.Checks.RawDefaultDeclaration.after8 ∧
Solidity.Yul.RawDefaultDeclaration.run Solidity.Yul.Checks.RawDefaultDeclaration.u256 2 Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.initial = .normal Solidity.Yul.Checks.RawDefaultDeclaration.after256 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem values : ((Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawDefaultDeclaration.after8.values .here).clean?).map Solidity.Source.Val.key =
 some (some 0) ∧
 ((Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawDefaultDeclaration.after256.values .here).clean?).map Solidity.Source.Val.key =
 some (some 0) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawDefaultDeclaration.after8.values (.there .here)).scalar? =
 some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawDefaultDeclaration.after256.values (.there (.there (.there .here)))).scalar? =
 some (Solidity.Yul.word 257) := by
  decide

theorem lookup : (Solidity.Yul.RawDefaultDeclaration.check Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.env (.int Solidity.Source.IntTy.u8)).isSome = true ∧
 (Solidity.Yul.RawDefaultDeclaration.check Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.env (.int Solidity.Source.IntTy.u256)).isSome = true ∧
 (Solidity.Yul.RawDefaultDeclaration.check Solidity.Yul.Checks.RawDefaultDeclaration.Fixture.env (.bytes .memory)).isNone = true := by
  decide

#print axioms Solidity.Yul.RawDefaultDeclaration.correct
#print axioms Solidity.Yul.RawDefaultDeclaration.int_default
#print axioms Solidity.Yul.RawDefaultDeclaration.int_correct
#print axioms concrete8
#print axioms concrete256
#print axioms outcomes
#print axioms values
#print axioms lookup

end Solidity.Yul.Checks.RawDefaultDeclaration
