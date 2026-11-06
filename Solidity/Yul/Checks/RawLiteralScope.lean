import Solidity.Yul.RawLiteralScope
import Solidity.Yul.Checks.RawDefaultScope

namespace Solidity.Yul.Checks.RawLiteralScope
namespace Fixture
export Solidity.Yul.Checks.RawDefaultScope.Fixture (ctx env initial dirty flag small)
end Fixture

def bodyTrue : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt (.declInit (τ := .bool) (.bool true) (by rfl)) .nil)
def bodyFalse : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt (.declInit (τ := .bool) (.bool false) (by rfl)) .nil)
def adapterTrue : RawSourceAdapter.Adapter Fixture.ctx [] false false bodyTrue :=
  Solidity.Yul.RawLiteralScope.adapter true
def adapterFalse : RawSourceAdapter.Adapter Fixture.ctx [] false false bodyFalse :=
  Solidity.Yul.RawLiteralScope.adapter false
def witness : Nonempty (RawSourceAdapter.Adapter Fixture.ctx [] false false bodyTrue) := ⟨adapterTrue⟩

def concrete (value : Bool) (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawLiteralScope.correct Fixture.env Fixture.ctx.tys value
    [] false ⟨true,false⟩ glob frame fuel nps ph Fixture.initial
def mixedItems : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .stmt bodyTrue (.stmt Solidity.Yul.Checks.RawDefaultScope.body8 .nil)
def mixed : RawSourceAdapter.Adapter Fixture.ctx [] false false (.block mixedItems) :=
  RawSourceAdapter.block (RawSourceAdapter.cons adapterTrue
    (RawSourceAdapter.cons Solidity.Yul.Checks.RawDefaultScope.adapter8 RawSourceAdapter.nil))
def cleanFrame : RawFrame.State Fixture.ctx := RawFrame.ofClean Fixture.dirty.clean Fixture.dirty.world
def mixedSource (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  mixed.correct glob frame fuel nps ph cleanFrame
    (RawCoherent.coherent_ofClean Fixture.dirty.clean Fixture.dirty.world)




theorem timeouts :  Solidity.Yul.RawLiteralScope.run true 0 Solidity.Yul.Checks.RawLiteralScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLiteralScope.Fixture.initial) ∧
Solidity.Yul.RawLiteralScope.run true 1 Solidity.Yul.Checks.RawLiteralScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLiteralScope.Fixture.initial) ∧
Solidity.Yul.RawLiteralScope.run true 2 Solidity.Yul.Checks.RawLiteralScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLiteralScope.Fixture.initial) ∧
Solidity.Yul.RawLiteralScope.run true 3 Solidity.Yul.Checks.RawLiteralScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLiteralScope.Fixture.initial) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem restored :  Solidity.Yul.RawLiteralScope.run true 4 Solidity.Yul.Checks.RawLiteralScope.Fixture.initial =
 (.ok (.normal Solidity.Yul.Checks.RawLiteralScope.Fixture.initial.clean),Solidity.Yul.Checks.RawLiteralScope.Fixture.initial) ∧
Solidity.Yul.RawLiteralScope.run false 4 Solidity.Yul.Checks.RawLiteralScope.Fixture.initial =
 (.ok (.normal Solidity.Yul.Checks.RawLiteralScope.Fixture.initial.clean),Solidity.Yul.Checks.RawLiteralScope.Fixture.initial) ∧
Solidity.Yul.Checks.RawLiteralScope.adapterTrue.run 4 Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawLiteralScope.adapterFalse.run 4 Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem combination :  Solidity.Yul.Checks.RawLiteralScope.mixed.run 6 Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty = (.error .timeout,Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawLiteralScope.mixed.run 7 Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty) := by
  exact ⟨rfl,rfl⟩

theorem values :  (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawLiteralScope.mixed.run 7
 Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty).2
 Solidity.Yul.Checks.RawLiteralScope.Fixture.flag).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawLiteralScope.mixed.run 7
 Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty).2
 Solidity.Yul.Checks.RawLiteralScope.Fixture.small).val = 257 ∧
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawLiteralScope.mixed.run 7
 Solidity.Yul.Checks.RawLiteralScope.Fixture.dirty).2 = false := by
  decide

#print axioms Solidity.Yul.RawLiteralScope.correct
#print axioms Solidity.Yul.RawLiteralScope.frame_correct
#print axioms Solidity.Yul.RawLiteralScope.adapter
#print axioms concrete
#print axioms mixedSource
#print axioms timeouts
#print axioms restored
#print axioms combination
#print axioms values

end Solidity.Yul.Checks.RawLiteralScope
