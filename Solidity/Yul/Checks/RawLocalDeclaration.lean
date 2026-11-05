import Solidity.Yul.RawLocalDeclaration
import Solidity.Yul.Checks.RawSourceVoidReturn

namespace Solidity.Yul.Checks.RawLocalDeclaration
namespace Fixture
export Solidity.Yul.Checks.RawSourceVoidReturn (dirty)
export Solidity.Yul.Checks.RawSourceVoidReturn.Old (ctx env flag small)
end Fixture

def initial := Solidity.Yul.RawLocalDeclaration.Snapshot.ofFrame Fixture.dirty
def after : Solidity.Yul.RawLocalDeclaration.Snapshot Fixture.env (.bool :: Fixture.ctx.tys) :=
  ⟨.cons (.bool false) initial.clean,(.clean (.bool false),initial.values),initial.world⟩
def declaration : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) := .declVar .bool
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys)) := ⟨declaration⟩

def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawLocalDeclaration.correct Fixture.env Fixture.ctx.tys [] false
    ⟨false,false⟩ glob frame fuel nps ph initial

def normal (result : Solidity.Yul.RawLocalDeclaration.BoolResult Fixture.env Fixture.ctx.tys) : Bool :=
  Solidity.Yul.RawLocalDeclaration.BoolResult.casesOn (motive := fun _ => Bool) result
    (fun _ => true) (fun _ _ => false)

theorem horizons : Solidity.Yul.Checks.RawLocalDeclaration.normal (Solidity.Yul.RawLocalDeclaration.run 0 Solidity.Yul.Checks.RawLocalDeclaration.initial) = false ∧
Solidity.Yul.Checks.RawLocalDeclaration.normal (Solidity.Yul.RawLocalDeclaration.run 1 Solidity.Yul.Checks.RawLocalDeclaration.initial) = false ∧
Solidity.Yul.Checks.RawLocalDeclaration.normal (Solidity.Yul.RawLocalDeclaration.run 2 Solidity.Yul.Checks.RawLocalDeclaration.initial) = true := by
  decide

theorem values : ((Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawLocalDeclaration.after.values .here).clean?).map
 Solidity.Source.Val.key = some (some 0) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawLocalDeclaration.after.values (.there .here)).scalar? =
 some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.RawLocalDeclaration.after.values (.there (.there (.there .here)))).scalar? =
 some (Solidity.Yul.word 257) ∧
 (Solidity.Yul.LocalValues.clean? (.bool :: Solidity.Yul.Checks.RawLocalDeclaration.Fixture.ctx.tys)
 Solidity.Yul.Checks.RawLocalDeclaration.after.values).isNone = true := by
  decide

theorem result : Solidity.Yul.RawLocalDeclaration.run 0 Solidity.Yul.Checks.RawLocalDeclaration.initial =
 .halted .timeout Solidity.Yul.Checks.RawLocalDeclaration.initial ∧
 Solidity.Yul.RawLocalDeclaration.run 1 Solidity.Yul.Checks.RawLocalDeclaration.initial =
 .halted .timeout Solidity.Yul.Checks.RawLocalDeclaration.initial ∧
 Solidity.Yul.RawLocalDeclaration.run 2 Solidity.Yul.Checks.RawLocalDeclaration.initial =
 .normal Solidity.Yul.Checks.RawLocalDeclaration.after := by
  exact ⟨rfl,rfl,rfl⟩

theorem prefix_preserved : Solidity.Yul.Checks.RawLocalDeclaration.after.values.2 =
 Solidity.Yul.Checks.RawLocalDeclaration.initial.values ∧
 Solidity.Yul.Checks.RawLocalDeclaration.after.world =
 Solidity.Yul.Checks.RawLocalDeclaration.initial.world := by
  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.RawLocalDeclaration.correct
#print axioms concrete
#print axioms horizons
#print axioms values
#print axioms result
#print axioms prefix_preserved

end Solidity.Yul.Checks.RawLocalDeclaration
