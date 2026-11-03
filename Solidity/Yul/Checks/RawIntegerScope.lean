import Solidity.Yul.RawIntegerScope
import Solidity.Yul.Checks.RawIntegerInitialization
import Solidity.Yul.Checks.RawLiteralScope

namespace Solidity.Yul.Checks.RawIntegerScope
namespace Fixture
export Solidity.Yul.Checks.RawIntegerInitialization (ranges)
export Solidity.Yul.Checks.RawIntegerInitialization.Fixture (ctx env initial dirty flag small signed8)
end Fixture

def body8 : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt (.declInit (τ := .int Solidity.Source.IntTy.u8) (.const (Solidity.Source.Q.ofInt 255))
    (RawIntegerInitialization.admissible Fixture.env _ _ Fixture.ranges.1)) .nil)
def bodySigned : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt (.declInit (τ := .int Fixture.signed8) (.const (Solidity.Source.Q.ofInt (-128)))
    (RawIntegerInitialization.admissible Fixture.env _ _ Fixture.ranges.2.1)) .nil)
def bodyWide : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.stmt (.declInit (τ := .int Solidity.Source.IntTy.u256) (.const (Solidity.Source.Q.ofInt (2^256-1)))
    (RawIntegerInitialization.admissible Fixture.env _ _ Fixture.ranges.2.2)) .nil)
def adapter8 : RawSourceAdapter.Adapter Fixture.ctx [] false false body8 :=
  RawIntegerScope.adapter _ _ Fixture.ranges.1
def adapterSigned : RawSourceAdapter.Adapter Fixture.ctx [] false false bodySigned :=
  RawIntegerScope.adapter _ _ Fixture.ranges.2.1
def adapterWide : RawSourceAdapter.Adapter Fixture.ctx [] false false bodyWide :=
  RawIntegerScope.adapter _ _ Fixture.ranges.2.2
def witness : Nonempty (RawSourceAdapter.Adapter Fixture.ctx [] false false body8) := ⟨adapter8⟩
def concrete (ty : Solidity.Source.IntTy) (value : Int) (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
    (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  RawIntegerScope.correct Fixture.env Fixture.ctx.tys ty value inRange
    [] false ⟨true,false⟩ glob frame fuel nps ph Fixture.initial
def mixedItems : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .stmt body8 (.stmt bodySigned .nil)
def mixed : RawSourceAdapter.Adapter Fixture.ctx [] false false (.block mixedItems) :=
  RawSourceAdapter.block (RawSourceAdapter.cons adapter8
    (RawSourceAdapter.cons adapterSigned RawSourceAdapter.nil))
def literalItems : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .stmt bodySigned (.stmt Solidity.Yul.Checks.RawLiteralScope.bodyTrue .nil)
def literalMixed : RawSourceAdapter.Adapter Fixture.ctx [] false false (.block literalItems) :=
  RawSourceAdapter.block (RawSourceAdapter.cons adapterSigned
    (RawSourceAdapter.cons Solidity.Yul.Checks.RawLiteralScope.adapterTrue RawSourceAdapter.nil))
def emptyAdapter : RawSourceAdapter.Adapter Fixture.ctx [] false false (.block .nil) :=
  RawSourceAdapter.block RawSourceAdapter.nil
def cleanFrame : RawFrame.State Fixture.ctx := RawFrame.ofClean Fixture.dirty.clean Fixture.dirty.world
def mixedSource (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  mixed.correct glob frame fuel nps ph cleanFrame
    (RawCoherent.coherent_ofClean Fixture.dirty.clean Fixture.dirty.world)
def literalSource (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  literalMixed.correct glob frame fuel nps ph cleanFrame
    (RawCoherent.coherent_ofClean Fixture.dirty.clean Fixture.dirty.world)



theorem timeouts : Solidity.Yul.RawIntegerScope.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerScope.Fixture.ranges.1 0 Solidity.Yul.Checks.RawIntegerScope.Fixture.initial = (.error .timeout,Solidity.Yul.Checks.RawIntegerScope.Fixture.initial) ∧
Solidity.Yul.RawIntegerScope.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerScope.Fixture.ranges.1 1 Solidity.Yul.Checks.RawIntegerScope.Fixture.initial = (.error .timeout,Solidity.Yul.Checks.RawIntegerScope.Fixture.initial) ∧
Solidity.Yul.RawIntegerScope.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerScope.Fixture.ranges.1 2 Solidity.Yul.Checks.RawIntegerScope.Fixture.initial = (.error .timeout,Solidity.Yul.Checks.RawIntegerScope.Fixture.initial) ∧
Solidity.Yul.RawIntegerScope.run Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawIntegerScope.Fixture.ranges.1 3 Solidity.Yul.Checks.RawIntegerScope.Fixture.initial = (.error .timeout,Solidity.Yul.Checks.RawIntegerScope.Fixture.initial) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem restored : Solidity.Yul.Checks.RawIntegerScope.adapter8.run 4 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawIntegerScope.adapterSigned.run 4 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawIntegerScope.adapterWide.run 4 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) := by
  exact ⟨rfl,rfl,rfl⟩

theorem combinations : Solidity.Yul.Checks.RawIntegerScope.mixed.run 6 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.error .timeout,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawIntegerScope.mixed.run 7 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawIntegerScope.literalMixed.run 6 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.error .timeout,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) ∧
Solidity.Yul.Checks.RawIntegerScope.literalMixed.run 7 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem values : (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawIntegerScope.mixed.run 7 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty).2 Solidity.Yul.Checks.RawIntegerScope.Fixture.flag).val = 2 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawIntegerScope.literalMixed.run 7 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty).2 Solidity.Yul.Checks.RawIntegerScope.Fixture.small).val = 257 ∧
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawIntegerScope.mixed.run 7 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty).2 = false := by
  decide

theorem notEmpty : Solidity.Yul.Checks.RawIntegerScope.emptyAdapter.run 2 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.ok .normal,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) ∧
 Solidity.Yul.Checks.RawIntegerScope.adapter8.run 2 Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty = (.error .timeout,Solidity.Yul.Checks.RawIntegerScope.Fixture.dirty) := by
  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.RawIntegerScope.correct
#print axioms Solidity.Yul.RawIntegerScope.frame_correct
#print axioms Solidity.Yul.RawIntegerScope.adapter
#print axioms concrete
#print axioms mixedSource
#print axioms literalSource
#print axioms timeouts
#print axioms restored
#print axioms combinations
#print axioms values
#print axioms notEmpty

end Solidity.Yul.Checks.RawIntegerScope
