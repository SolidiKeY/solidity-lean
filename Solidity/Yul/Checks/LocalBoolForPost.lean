import Solidity.Yul.LocalBoolForPost
import Solidity.Yul.Checks.LocalBoolFor

namespace Solidity.Yul.Checks.LocalBoolForPost
namespace Fixture
export Solidity.Yul.Checks.LocalBoolFor.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolFor (LoopCtx BodyCtx initial assigned yes no test entered bodyEntered)
export Solidity.Yul.Checks.LocalBoolInitialization (partialProof)
def post : LocalBoolControl.Supported Fixture.env LoopCtx
    (.assign (.local .here) (.bool false)) := .assign .here (.base (.literal false))
def postFalse : LocalBoolControl.Supported Fixture.env LoopCtx (.bool false) := .base (.literal false)
def badPost : Solidity.Source.RExpr Fixture.env LoopCtx .bool :=
  .binary .or (.assign (.local .here) (.bool false))
    (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.bool false)))))))
def failing : LocalBoolControl.Supported Fixture.env LoopCtx badPost :=
  .or (.assign .here (.base (.literal false)))
    (.not (.not (.not (.not (.not (.not (.base (.literal false))))))))
def items : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ LoopCtx BodyCtx :=
  .stmt (.declInit (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local (.there (.there .here))) (.local .here))) .nil)
def proof : LocalBoolItems.Supported Fixture.env [] false ⟨true,false⟩ items :=
  .declaration (.base (.local .here))
    (.expression (.assign (.there (.there .here)) (.base (.local .here))) .nil)
def repeatBody : LocalState Fixture.env BodyCtx :=
  ((.clean (.bool true),(.clean (.bool true),(assigned true).1)),(assigned true).2)
def postFailed : LocalState Fixture.env LoopCtx :=
  ((.clean (.bool false),(assigned true).1),(assigned true).2)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .forLoop (.declInit (.bool true) (by rfl)) (.some (.local .here))
    (.some (.assign (.local .here) (.bool false))) (.block items)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolForPost.source_agrees Fixture.env [] false false false Fixture.ctx.tys BodyCtx
    (.bool true) yes (.local .here) test (.assign (.local .here) (.bool false)) post
    items proof glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

theorem stages : Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.yes Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.post Solidity.Yul.Checks.LocalBoolForPost.proof 3 Solidity.Yul.Checks.LocalBoolForPost.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForPost.entered ∧
Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.yes Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.post Solidity.Yul.Checks.LocalBoolForPost.proof 6 Solidity.Yul.Checks.LocalBoolForPost.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForPost.bodyEntered ∧
Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.yes Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.post Solidity.Yul.Checks.LocalBoolForPost.proof 8 Solidity.Yul.Checks.LocalBoolForPost.initial = .normal (Solidity.Yul.Checks.LocalBoolForPost.assigned true) := by

  exact ⟨rfl,rfl,rfl⟩

theorem postEffects : Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.yes Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.failing Solidity.Yul.Checks.LocalBoolForPost.proof 8 Solidity.Yul.Checks.LocalBoolForPost.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForPost.postFailed ∧
Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.no Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.failing Solidity.Yul.Checks.LocalBoolForPost.proof 3 Solidity.Yul.Checks.LocalBoolForPost.initial = .normal Solidity.Yul.Checks.LocalBoolForPost.initial := by

  exact ⟨rfl,rfl⟩

theorem postDiscard : Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.yes Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.postFalse Solidity.Yul.Checks.LocalBoolForPost.proof 8 Solidity.Yul.Checks.LocalBoolForPost.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolForPost.repeatBody := by

  rfl

theorem initializerEffects : Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.partialProof Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.post Solidity.Yul.Checks.LocalBoolForPost.proof 5 Solidity.Yul.Checks.LocalBoolForPost.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPost.assigned true) := by

  rfl

theorem rawProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolForPost.Fixture.ctx.tys (Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPost.yes Solidity.Yul.Checks.LocalBoolForPost.test Solidity.Yul.Checks.LocalBoolForPost.post Solidity.Yul.Checks.LocalBoolForPost.proof 8 Solidity.Yul.Checks.LocalBoolForPost.initial) = none := by

  rfl

#print axioms Solidity.Yul.LocalBoolPostIter.source_agrees
#print axioms Solidity.Yul.LocalBoolForPost.source_agrees
#print axioms concrete
#print axioms stages
#print axioms postEffects
#print axioms postDiscard
#print axioms initializerEffects
#print axioms rawProjection
end Solidity.Yul.Checks.LocalBoolForPost
