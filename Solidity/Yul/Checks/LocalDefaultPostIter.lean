import Solidity.Yul.LocalDefaultPostIter
import Solidity.Yul.Checks.LocalDefaultDoWhile

namespace Solidity.Yul.Checks.LocalDefaultPostIter
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultDoWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalDefaultDoWhile
  (initial assigned zero8 zero256 items proof Out readTest stopTest)
def postFalse : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool false) := .base (.literal false)
def postTrue : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool true) := .base (.literal true)
def guardTrue : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool true) := .base (.literal true)
def postSetTrueExpr : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool :=
  .assign (.local .here) (.bool true)
def postSetTrue : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys postSetTrueExpr :=
  .assign .here (.base (.literal true))
def postFaultExpr : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool :=
  .binary .and postSetTrueExpr (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.local .here)))))))))
def postFault : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys postFaultExpr :=
  .and postSetTrue (.not (.not (.not (.not (.not (.not (.not (.not (.base (.local .here))))))))))
def afterFalsePostBody : LocalState Fixture.env Out :=
  ((.clean (.bool true),(.clean zero256.value,(.clean zero8.value,(assigned false).1))),
    (assigned false).2)
def afterPostWriteBody := Solidity.Yul.Checks.LocalDefaultDoWhile.afterGuardBodyState
def body : Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block items
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨true,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨body⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultPostIter.source_agrees Fixture.env [] false false Fixture.ctx.tys Out
    (.local .here) readTest (.bool false) postFalse items proof glob frame fuel nps ph
    Fixture.initial.clean Fixture.initial.world
def concreteWorld (fuel : Nat) (state : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalDefaultPostIter.world Fixture.env [] false false Fixture.ctx.tys Out
    (.local .here) readTest postFaultExpr postFault items proof fuel state
def constantNever (fuel : Nat) (state next : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalDefaultPostIter.no_normal Fixture.env [] false false Fixture.ctx.tys Out
    (.bool false) postFalse items proof fuel state next
def constantSourceNever (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env))
    (locals next : Solidity.Source.Locals Fixture.env.layout Fixture.ctx.tys)
    (world finalWorld : Solidity.Source.St Fixture.env) :=
  Solidity.Yul.LocalDefaultPostIter.source_no_normal Fixture.env [] false false Fixture.ctx.tys Out
    (.bool false) postFalse items proof glob frame fuel nps ph locals next world finalWorld

theorem guardStops : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.stopTest Solidity.Yul.Checks.LocalDefaultPostIter.postFault Solidity.Yul.Checks.LocalDefaultPostIter.proof 2 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .normal Solidity.Yul.Checks.LocalDefaultPostIter.initial := by

  rfl

theorem bodyTimeout : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postFalse Solidity.Yul.Checks.LocalDefaultPostIter.proof 8 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState := by

  rfl

theorem falsePostCompletion : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postFalse Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .normal (Solidity.Yul.Checks.LocalDefaultPostIter.assigned false) := by

  rfl

theorem truePostCompletion : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .normal (Solidity.Yul.Checks.LocalDefaultPostIter.assigned false) := by

  rfl

theorem falsePostIgnored : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.guardTrue Solidity.Yul.Checks.LocalDefaultPostIter.postFalse Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultPostIter.afterFalsePostBody := by

  rfl

theorem postWriteRetained : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postSetTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultPostIter.afterPostWriteBody := by

  rfl

theorem postHaltRetained : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postFault Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostIter.assigned true) := by

  rfl

theorem dirtyProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.ctx.tys (Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultPostIter.postTrue Solidity.Yul.Checks.LocalDefaultPostIter.proof 9 Solidity.Yul.Checks.LocalDefaultPostIter.initial) = none := by

  rfl

theorem sourceFalsePost : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env)),
 (Solidity.Source.forIter glob frame 9 nps ph (.some (.local .here)) (.some (.bool false)) Solidity.Yul.Checks.LocalDefaultPostIter.body
   (Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.clean.set .here (.bool false))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceTruePost : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env)),
 (Solidity.Source.forIter glob frame 9 nps ph (.some (.local .here)) (.some (.bool true)) Solidity.Yul.Checks.LocalDefaultPostIter.body
   (Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.clean.set .here (.bool false))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceFalsePostIgnored : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env)),
 (Solidity.Source.forIter glob frame 9 nps ph (.some (.bool true)) (.some (.bool false)) Solidity.Yul.Checks.LocalDefaultPostIter.body
   (Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourcePostHalt : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env)),
 (Solidity.Source.forIter glob frame 9 nps ph (.some (.local .here)) (.some Solidity.Yul.Checks.LocalDefaultPostIter.postFaultExpr) Solidity.Yul.Checks.LocalDefaultPostIter.body
   (Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.env,Solidity.Yul.Checks.LocalDefaultPostIter.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

#print axioms Solidity.Yul.LocalDefaultPostIter.source_agrees
#print axioms Solidity.Yul.LocalDefaultPostIter.world
#print axioms Solidity.Yul.LocalDefaultPostIter.no_normal
#print axioms Solidity.Yul.LocalDefaultPostIter.source_no_normal
#print axioms concrete
#print axioms concreteWorld
#print axioms constantNever
#print axioms constantSourceNever
#print axioms guardStops
#print axioms bodyTimeout
#print axioms falsePostCompletion
#print axioms truePostCompletion
#print axioms falsePostIgnored
#print axioms postWriteRetained
#print axioms postHaltRetained
#print axioms dirtyProjection
#print axioms sourceFalsePost
#print axioms sourceTruePost
#print axioms sourceFalsePostIgnored
#print axioms sourcePostHalt
end Solidity.Yul.Checks.LocalDefaultPostIter
