import Solidity.Yul.LocalDefaultDoWhile
import Solidity.Yul.Checks.LocalDefaultWhile

namespace Solidity.Yul.Checks.LocalDefaultDoWhile
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalDefaultWhile
  (initial assigned zero8 zero256 items proof Out readTest stopTest)
def assigningTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys
    (.assign (.local .here) (.bool true)) := .assign .here (.base (.literal true))
def afterGuardBodyState : LocalState Fixture.env Out :=
  ((.clean (.bool false),(.clean zero256.value,(.clean zero8.value,(assigned true).1))),
    (assigned true).2)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .doWhile (.block items) (.local .here)
def stopStatement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .doWhile (.block items) (.bool false)
def whileStopStatement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .whileLoop (.bool false) (.block items)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultDoWhile.source_agrees Fixture.env [] false false false Fixture.ctx.tys Out
    (.local .here) readTest items proof glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world
def concreteWorld (fuel : Nat) (state : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalDefaultDoWhile.world Fixture.env [] false false Fixture.ctx.tys Out
    (.local .here) readTest items proof fuel state
def constantNever (fuel : Nat) (state next : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalDefaultDoWhile.no_normal Fixture.env [] false false Fixture.ctx.tys Out
    items proof fuel state next
def constantSourceNever (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env))
    (locals next : Solidity.Source.Locals Fixture.env.layout Fixture.ctx.tys)
    (world finalWorld : Solidity.Source.St Fixture.env) :=
  Solidity.Yul.LocalDefaultDoWhile.source_no_normal Fixture.env [] false false false Fixture.ctx.tys Out
    items proof glob frame fuel nps ph locals next world finalWorld

theorem bodyFirst : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultDoWhile.stopTest Solidity.Yul.Checks.LocalDefaultDoWhile.proof 2 Solidity.Yul.Checks.LocalDefaultDoWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultDoWhile.initial := by

  rfl

theorem firstTimeout : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultDoWhile.readTest Solidity.Yul.Checks.LocalDefaultDoWhile.proof 5 Solidity.Yul.Checks.LocalDefaultDoWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.firstState := by

  rfl

theorem bodyTimeout : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultDoWhile.readTest Solidity.Yul.Checks.LocalDefaultDoWhile.proof 8 Solidity.Yul.Checks.LocalDefaultDoWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState := by

  rfl

theorem completion : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultDoWhile.readTest Solidity.Yul.Checks.LocalDefaultDoWhile.proof 9 Solidity.Yul.Checks.LocalDefaultDoWhile.initial = .normal (Solidity.Yul.Checks.LocalDefaultDoWhile.assigned false) := by

  rfl

theorem falseGuardExecutes : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultDoWhile.stopTest Solidity.Yul.Checks.LocalDefaultDoWhile.proof 9 Solidity.Yul.Checks.LocalDefaultDoWhile.initial = .normal (Solidity.Yul.Checks.LocalDefaultDoWhile.assigned false) := by

  rfl

theorem postGuardEffect : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultDoWhile.assigningTest Solidity.Yul.Checks.LocalDefaultDoWhile.proof 9 Solidity.Yul.Checks.LocalDefaultDoWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultDoWhile.afterGuardBodyState := by

  rfl

theorem dirtyProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.ctx.tys (Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultDoWhile.readTest Solidity.Yul.Checks.LocalDefaultDoWhile.proof 9 Solidity.Yul.Checks.LocalDefaultDoWhile.initial) = none := by

  rfl

theorem sourceCompletion : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env)),
 (Solidity.Source.execS glob frame 9 nps ph Solidity.Yul.Checks.LocalDefaultDoWhile.statement
   (Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.clean.set .here (.bool false))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env)),
 (Solidity.Source.execS glob frame 8 nps ph Solidity.Yul.Checks.LocalDefaultDoWhile.statement
   (Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceFalseGuard : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env)),
 (Solidity.Source.execS glob frame 9 nps ph Solidity.Yul.Checks.LocalDefaultDoWhile.stopStatement
   (Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.clean.set .here (.bool false))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceWhileFalse : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env)),
 (Solidity.Source.execS glob frame 9 nps ph Solidity.Yul.Checks.LocalDefaultDoWhile.whileStopStatement
   (Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.clean.set .here (.bool true))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

#print axioms Solidity.Yul.LocalDefaultDoWhile.source_agrees
#print axioms Solidity.Yul.LocalDefaultDoWhile.world
#print axioms Solidity.Yul.LocalDefaultDoWhile.no_normal
#print axioms Solidity.Yul.LocalDefaultDoWhile.source_no_normal
#print axioms concrete
#print axioms concreteWorld
#print axioms constantNever
#print axioms constantSourceNever
#print axioms bodyFirst
#print axioms firstTimeout
#print axioms bodyTimeout
#print axioms completion
#print axioms falseGuardExecutes
#print axioms postGuardEffect
#print axioms dirtyProjection
#print axioms sourceCompletion
#print axioms sourceTimeout
#print axioms sourceFalseGuard
#print axioms sourceWhileFalse
end Solidity.Yul.Checks.LocalDefaultDoWhile
