import Solidity.Yul.RawLocalScope
import Solidity.Yul.Checks.RawLocalDeclaration

namespace Solidity.Yul.Checks.RawLocalScope
namespace Fixture
export Solidity.Yul.Checks.RawLocalDeclaration (initial)
export Solidity.Yul.Checks.RawLocalDeclaration.Fixture (ctx env dirty flag small)
end Fixture

def body : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩
    Fixture.ctx.tys Fixture.ctx.tys := .block (.stmt (.declVar .bool) .nil)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨body⟩
def actualAdapter : RawSourceAdapter.Adapter Fixture.ctx [] false false body :=
  Solidity.Yul.RawLocalScope.adapter

def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawLocalScope.frame_correct Fixture.ctx [] false false glob frame fuel nps ph Fixture.dirty

def normal (result : Solidity.Source.R
    (Solidity.Source.Out Fixture.env.layout Fixture.ctx.tys Fixture.ctx.tys) ×
    Solidity.Yul.RawLocalDeclaration.Snapshot Fixture.env Fixture.ctx.tys) : Bool :=
  match result.1 with
  | .ok (.normal _) => true
  | _ => false

def combinedItems : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩
    Fixture.ctx.tys Fixture.ctx.tys := .stmt body (.stmt body .nil)
def combined : RawSourceAdapter.Adapter Fixture.ctx [] false false (.block combinedItems) :=
  RawSourceAdapter.block (RawSourceAdapter.cons actualAdapter
    (RawSourceAdapter.cons actualAdapter RawSourceAdapter.nil))
def cleanFrame : RawFrame.State Fixture.ctx :=
  RawFrame.ofClean Fixture.dirty.clean Fixture.dirty.world
def combinedSource (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  combined.correct glob frame fuel nps ph cleanFrame
    (RawCoherent.coherent_ofClean Fixture.dirty.clean Fixture.dirty.world)

theorem horizons : Solidity.Yul.Checks.RawLocalScope.normal (Solidity.Yul.RawLocalScope.run 0 Solidity.Yul.Checks.RawLocalScope.Fixture.initial) = false ∧
Solidity.Yul.Checks.RawLocalScope.normal (Solidity.Yul.RawLocalScope.run 1 Solidity.Yul.Checks.RawLocalScope.Fixture.initial) = false ∧
Solidity.Yul.Checks.RawLocalScope.normal (Solidity.Yul.RawLocalScope.run 2 Solidity.Yul.Checks.RawLocalScope.Fixture.initial) = false ∧
Solidity.Yul.Checks.RawLocalScope.normal (Solidity.Yul.RawLocalScope.run 3 Solidity.Yul.Checks.RawLocalScope.Fixture.initial) = false ∧
Solidity.Yul.Checks.RawLocalScope.normal (Solidity.Yul.RawLocalScope.run 4 Solidity.Yul.Checks.RawLocalScope.Fixture.initial) = true := by
  decide

theorem values : (Solidity.Yul.RawFrame.view
 (Solidity.Yul.RawLocalScope.frameRun 4 Solidity.Yul.Checks.RawLocalScope.Fixture.dirty).2
 Solidity.Yul.Checks.RawLocalScope.Fixture.flag).val = 2 ∧
 (Solidity.Yul.RawFrame.view
 (Solidity.Yul.RawLocalScope.frameRun 4 Solidity.Yul.Checks.RawLocalScope.Fixture.dirty).2
 Solidity.Yul.Checks.RawLocalScope.Fixture.small).val = 257 ∧
 Solidity.Yul.RawCoherent.coherent
 (Solidity.Yul.RawLocalScope.frameRun 4 Solidity.Yul.Checks.RawLocalScope.Fixture.dirty).2 = false := by
  decide

theorem restored : Solidity.Yul.RawLocalScope.run 3 Solidity.Yul.Checks.RawLocalScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLocalScope.Fixture.initial) ∧
 Solidity.Yul.RawLocalScope.run 4 Solidity.Yul.Checks.RawLocalScope.Fixture.initial =
 (.ok (.normal Solidity.Yul.Checks.RawLocalScope.Fixture.initial.clean),
  Solidity.Yul.Checks.RawLocalScope.Fixture.initial) ∧
 Solidity.Yul.RawLocalScope.frameRun 4 Solidity.Yul.Checks.RawLocalScope.Fixture.dirty =
 (.ok .normal,Solidity.Yul.Checks.RawLocalScope.Fixture.dirty) ∧
 Solidity.Yul.Checks.RawLocalScope.actualAdapter.run 4 Solidity.Yul.Checks.RawLocalScope.Fixture.dirty =
 (.ok .normal,Solidity.Yul.Checks.RawLocalScope.Fixture.dirty) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem combination : Solidity.Yul.Checks.RawLocalScope.combined.run 6 Solidity.Yul.Checks.RawLocalScope.Fixture.dirty =
 (.error .timeout,Solidity.Yul.Checks.RawLocalScope.Fixture.dirty) ∧
 Solidity.Yul.Checks.RawLocalScope.combined.run 7 Solidity.Yul.Checks.RawLocalScope.Fixture.dirty =
 (.ok .normal,Solidity.Yul.Checks.RawLocalScope.Fixture.dirty) := by
  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.RawLocalScope.restore_cons
#print axioms Solidity.Yul.RawLocalScope.correct
#print axioms Solidity.Yul.RawLocalScope.frame_correct
#print axioms concrete
#print axioms combinedSource
#print axioms horizons
#print axioms values
#print axioms restored
#print axioms combination

theorem low_timeouts : Solidity.Yul.RawLocalScope.run 0 Solidity.Yul.Checks.RawLocalScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLocalScope.Fixture.initial) ∧
Solidity.Yul.RawLocalScope.run 1 Solidity.Yul.Checks.RawLocalScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLocalScope.Fixture.initial) ∧
Solidity.Yul.RawLocalScope.run 2 Solidity.Yul.Checks.RawLocalScope.Fixture.initial =
 (.error .timeout,Solidity.Yul.Checks.RawLocalScope.Fixture.initial) := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms low_timeouts
#print axioms Solidity.Yul.RawLocalScope.adapter

end Solidity.Yul.Checks.RawLocalScope
