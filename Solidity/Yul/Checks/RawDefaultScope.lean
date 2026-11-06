import Solidity.Yul.RawDefaultScope
import Solidity.Yul.Checks.RawDefaultDeclaration

namespace Solidity.Yul.Checks.RawDefaultScope
namespace Fixture
export Solidity.Yul.Checks.RawDefaultDeclaration (u8 u256)
export Solidity.Yul.Checks.RawDefaultDeclaration.Fixture (ctx env initial dirty flag small)
end Fixture

def body8 : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt (.declVar (.int Solidity.Source.IntTy.u8)) .nil)
def body256 : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt (.declVar (.int Solidity.Source.IntTy.u256)) .nil)
def adapter8 : RawSourceAdapter.Adapter Fixture.ctx [] false false body8 :=
  Solidity.Yul.RawDefaultScope.intAdapter Solidity.Source.IntTy.u8
def adapter256 : RawSourceAdapter.Adapter Fixture.ctx [] false false body256 :=
  Solidity.Yul.RawDefaultScope.intAdapter Solidity.Source.IntTy.u256
def witness : Nonempty (RawSourceAdapter.Adapter Fixture.ctx [] false false body8) := ⟨adapter8⟩

def concrete8 (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawDefaultScope.int_correct Fixture.env Fixture.ctx.tys Solidity.Source.IntTy.u8
    [] false ⟨true,false⟩ glob frame fuel nps ph Fixture.initial
def concrete256 (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawDefaultScope.int_correct Fixture.env Fixture.ctx.tys Solidity.Source.IntTy.u256
    [] false ⟨true,false⟩ glob frame fuel nps ph Fixture.initial
def mixedItems : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .stmt body8 (.stmt body256 .nil)
def mixed : RawSourceAdapter.Adapter Fixture.ctx [] false false (.block mixedItems) :=
  RawSourceAdapter.block (RawSourceAdapter.cons adapter8
    (RawSourceAdapter.cons adapter256 RawSourceAdapter.nil))
def cleanFrame : RawFrame.State Fixture.ctx := RawFrame.ofClean Fixture.dirty.clean Fixture.dirty.world
def mixedSource (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  mixed.correct glob frame fuel nps ph cleanFrame
    (RawCoherent.coherent_ofClean Fixture.dirty.clean Fixture.dirty.world)

theorem timeouts : Solidity.Yul.RawDefaultScope.run Solidity.Yul.Checks.RawDefaultScope.Fixture.u8 0 Solidity.Yul.Checks.RawDefaultScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawDefaultScope.Fixture.initial) ∧
Solidity.Yul.RawDefaultScope.run Solidity.Yul.Checks.RawDefaultScope.Fixture.u8 1 Solidity.Yul.Checks.RawDefaultScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawDefaultScope.Fixture.initial) ∧
Solidity.Yul.RawDefaultScope.run Solidity.Yul.Checks.RawDefaultScope.Fixture.u8 2 Solidity.Yul.Checks.RawDefaultScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawDefaultScope.Fixture.initial) ∧
Solidity.Yul.RawDefaultScope.run Solidity.Yul.Checks.RawDefaultScope.Fixture.u8 3 Solidity.Yul.Checks.RawDefaultScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawDefaultScope.Fixture.initial) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem restored : Solidity.Yul.RawDefaultScope.run Solidity.Yul.Checks.RawDefaultScope.Fixture.u8 4 Solidity.Yul.Checks.RawDefaultScope.Fixture.initial =
 (.ok (.normal Solidity.Yul.Checks.RawDefaultScope.Fixture.initial.clean),Solidity.Yul.Checks.RawDefaultScope.Fixture.initial) ∧
Solidity.Yul.RawDefaultScope.run Solidity.Yul.Checks.RawDefaultScope.Fixture.u256 4 Solidity.Yul.Checks.RawDefaultScope.Fixture.initial =
 (.ok (.normal Solidity.Yul.Checks.RawDefaultScope.Fixture.initial.clean),Solidity.Yul.Checks.RawDefaultScope.Fixture.initial) ∧
Solidity.Yul.Checks.RawDefaultScope.adapter8.run 4 Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawDefaultScope.adapter256.run 4 Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem combination : Solidity.Yul.Checks.RawDefaultScope.mixed.run 6 Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty = (.error .timeout,Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawDefaultScope.mixed.run 7 Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty) := by
  exact ⟨rfl,rfl⟩

theorem values : (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDefaultScope.mixed.run 7
 Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty).2
 Solidity.Yul.Checks.RawDefaultScope.Fixture.flag).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawDefaultScope.mixed.run 7
 Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty).2
 Solidity.Yul.Checks.RawDefaultScope.Fixture.small).val = 257 ∧
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawDefaultScope.mixed.run 7
 Solidity.Yul.Checks.RawDefaultScope.Fixture.dirty).2 = false := by
  decide

#print axioms Solidity.Yul.RawDefaultScope.correct
#print axioms Solidity.Yul.RawDefaultScope.frame_correct
#print axioms Solidity.Yul.RawDefaultScope.int_correct
#print axioms Solidity.Yul.RawDefaultScope.adapter
#print axioms Solidity.Yul.RawDefaultScope.intAdapter
#print axioms concrete8
#print axioms concrete256
#print axioms mixedSource
#print axioms timeouts
#print axioms restored
#print axioms combination
#print axioms values

end Solidity.Yul.Checks.RawDefaultScope
