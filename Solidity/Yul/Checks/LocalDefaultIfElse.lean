import Solidity.Yul.LocalDefaultIfElse
import Solidity.Yul.Checks.LocalDefaultItems

namespace Solidity.Yul.Checks.LocalDefaultIfElse
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultItems.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalDefaultItems (initial assigned)
abbrev YesOut := Solidity.Source.STy.bool :: .int Solidity.Source.IntTy.u256 ::
  .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys
abbrev NoOut := Solidity.Source.STy.bool :: Fixture.ctx.tys
def yesItems := Solidity.Yul.Checks.LocalDefaultItems.items
def yes := Solidity.Yul.Checks.LocalDefaultItems.proof
def noItems : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys NoOut :=
  .stmt (.declVar .bool)
    (.stmt (.expr (.assign (.local (.there .here)) (.bool true))) .nil)
def no : LocalDefaultItems.Supported Fixture.env [] false ⟨false,false⟩ noItems :=
  .declaration Solidity.Yul.Checks.LocalDefaultBinding.zeroBool
    (.body (.expression (.assign (.there .here) (.base (.literal true))) .nil))
def yesTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool true) := .base (.literal true)
def noTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool false) := .base (.literal false)
def readTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.local .here) := .base (.local .here)
def assigningTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys
    (.assign (.local .here) (.bool false)) := .assign .here (.base (.literal false))
def noEntered : LocalState Fixture.env NoOut :=
  ((.clean (.bool false),initial.1),initial.2)
def statement (condition : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool) :
    Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .ifElse condition (.block yesItems) (.block noItems)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement (.bool true)⟩
def concrete (choose : Bool) (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultIfElse.source_agrees Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys YesOut NoOut (.bool choose) (.base (.literal choose))
    yesItems yes noItems no glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

theorem yesCompletion : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultIfElse.yesTest Solidity.Yul.Checks.LocalDefaultIfElse.yes Solidity.Yul.Checks.LocalDefaultIfElse.no 9 Solidity.Yul.Checks.LocalDefaultIfElse.initial = .normal (Solidity.Yul.Checks.LocalDefaultIfElse.assigned false) := by

  rfl

theorem noCompletion : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultIfElse.noTest Solidity.Yul.Checks.LocalDefaultIfElse.yes Solidity.Yul.Checks.LocalDefaultIfElse.no 7 Solidity.Yul.Checks.LocalDefaultIfElse.initial = .normal (Solidity.Yul.Checks.LocalDefaultIfElse.assigned true) := by

  rfl

theorem yesTimeout : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultIfElse.yesTest Solidity.Yul.Checks.LocalDefaultIfElse.yes Solidity.Yul.Checks.LocalDefaultIfElse.no 8 Solidity.Yul.Checks.LocalDefaultIfElse.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState := by

  rfl

theorem noTimeout : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultIfElse.noTest Solidity.Yul.Checks.LocalDefaultIfElse.yes Solidity.Yul.Checks.LocalDefaultIfElse.no 6 Solidity.Yul.Checks.LocalDefaultIfElse.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultIfElse.noEntered := by

  rfl

theorem conditionEffect : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultIfElse.assigningTest Solidity.Yul.Checks.LocalDefaultIfElse.yes Solidity.Yul.Checks.LocalDefaultIfElse.no 3 Solidity.Yul.Checks.LocalDefaultIfElse.initial = .halted .timeout (Solidity.Yul.Checks.LocalDefaultIfElse.assigned false) := by

  rfl

theorem rawSelection : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultIfElse.readTest Solidity.Yul.Checks.LocalDefaultIfElse.yes Solidity.Yul.Checks.LocalDefaultIfElse.no 9 Solidity.Yul.Checks.LocalDefaultIfElse.initial = .normal (Solidity.Yul.Checks.LocalDefaultIfElse.assigned false) := by

  rfl

theorem dirtyProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.ctx.tys (Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultIfElse.yesTest Solidity.Yul.Checks.LocalDefaultIfElse.yes Solidity.Yul.Checks.LocalDefaultIfElse.no 9 Solidity.Yul.Checks.LocalDefaultIfElse.initial) = none := by

  rfl

theorem sourceYes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env)),
 (Solidity.Source.execS glob frame 9 nps ph (Solidity.Yul.Checks.LocalDefaultIfElse.statement (.bool true))
   (Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env,Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.clean.set .here (.bool false))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env,Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceNo : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env)),
 (Solidity.Source.execS glob frame 7 nps ph (Solidity.Yul.Checks.LocalDefaultIfElse.statement (.bool false))
   (Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env,Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.clean.set .here (.bool true))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env,Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env)),
 (Solidity.Source.execS glob frame 8 nps ph (Solidity.Yul.Checks.LocalDefaultIfElse.statement (.bool true))
   (Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env,Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.env,Solidity.Yul.Checks.LocalDefaultIfElse.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

def assignmentConcrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultIfElse.source_agrees Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys YesOut NoOut (.assign (.local .here) (.bool false)) assigningTest
    yesItems yes noItems no glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

def concreteWorld (fuel : Nat) (world : Solidity.Source.St Fixture.env) :=
  Solidity.Yul.LocalDefaultIfElse.world Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys YesOut NoOut (.local .here) readTest yesItems yes noItems no
    fuel (initial.1,world)

#print axioms Solidity.Yul.LocalDefaultIfElse.source_agrees
#print axioms Solidity.Yul.LocalDefaultIfElse.world
#print axioms concrete
#print axioms assignmentConcrete
#print axioms concreteWorld
#print axioms yesCompletion
#print axioms noCompletion
#print axioms yesTimeout
#print axioms noTimeout
#print axioms conditionEffect
#print axioms rawSelection
#print axioms dirtyProjection
#print axioms sourceYes
#print axioms sourceNo
#print axioms sourceTimeout
end Solidity.Yul.Checks.LocalDefaultIfElse
