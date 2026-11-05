import Solidity.Yul.LocalDefaultWhile
import Solidity.Yul.Checks.LocalDefaultItems

namespace Solidity.Yul.Checks.LocalDefaultWhile
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultItems.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalDefaultItems (initial assigned zero8 zero256)
def items : Solidity.Source.RItems Fixture.env [] false ⟨true,false⟩ Fixture.ctx.tys
    (.bool :: .int Solidity.Source.IntTy.u256 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  .stmt (.declVar (.int Solidity.Source.IntTy.u8))
    (.stmt (.declVar (.int Solidity.Source.IntTy.u256))
      (.stmt (.declInit (.unary .not (.local (.there (.there .here)))) (by rfl))
        (.stmt (.expr (.assign (.local (.there (.there (.there .here)))) (.local .here))) .nil)))

def proof : LocalDefaultItems.Supported Fixture.env [] false ⟨true,false⟩ items :=
  .declaration zero8 (.declaration zero256
    (.body (.declaration (.not (.base (.local (.there (.there .here)))))
      (.expression (.assign (.there (.there (.there .here))) (.base (.local .here))) .nil))))


abbrev Out := Solidity.Source.STy.bool :: .int Solidity.Source.IntTy.u256 ::
  .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys
def readTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.local .here) := .base (.local .here)
def stopTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys (.bool false) := .base (.literal false)
def assigningTest : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys
    (.assign (.local .here) (.bool false)) := .assign .here (.base (.literal false))
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .whileLoop (.local .here) (.block items)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultWhile.source_agrees Fixture.env [] false false false Fixture.ctx.tys Out
    (.local .here) readTest items proof glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world
def concreteWorld (fuel : Nat) (state : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalDefaultWhile.world Fixture.env [] false false Fixture.ctx.tys Out
    (.local .here) readTest items proof fuel state
def constantNever (fuel : Nat) (state next : LocalState Fixture.env Fixture.ctx.tys) :=
  Solidity.Yul.LocalDefaultWhile.no_normal Fixture.env [] false false Fixture.ctx.tys Out
    items proof fuel state next
def constantSourceNever (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env))
    (locals next : Solidity.Source.Locals Fixture.env.layout Fixture.ctx.tys)
    (world finalWorld : Solidity.Source.St Fixture.env) :=
  Solidity.Yul.LocalDefaultWhile.source_no_normal Fixture.env [] false false false Fixture.ctx.tys Out
    items proof glob frame fuel nps ph locals next world finalWorld


theorem guardTimeout : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultWhile.readTest Solidity.Yul.Checks.LocalDefaultWhile.proof 1 Solidity.Yul.Checks.LocalDefaultWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultWhile.initial := by

  rfl

theorem firstTimeout : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultWhile.readTest Solidity.Yul.Checks.LocalDefaultWhile.proof 5 Solidity.Yul.Checks.LocalDefaultWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.firstState := by

  rfl

theorem bodyTimeout : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultWhile.readTest Solidity.Yul.Checks.LocalDefaultWhile.proof 8 Solidity.Yul.Checks.LocalDefaultWhile.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState := by

  rfl

theorem completion : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultWhile.readTest Solidity.Yul.Checks.LocalDefaultWhile.proof 9 Solidity.Yul.Checks.LocalDefaultWhile.initial = .normal (Solidity.Yul.Checks.LocalDefaultWhile.assigned false) := by

  rfl

theorem stopUnchanged : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultWhile.stopTest Solidity.Yul.Checks.LocalDefaultWhile.proof 2 Solidity.Yul.Checks.LocalDefaultWhile.initial = .normal Solidity.Yul.Checks.LocalDefaultWhile.initial := by

  rfl

theorem guardAssignment : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultWhile.assigningTest Solidity.Yul.Checks.LocalDefaultWhile.proof 3 Solidity.Yul.Checks.LocalDefaultWhile.initial = .normal (Solidity.Yul.Checks.LocalDefaultWhile.assigned false) := by

  rfl

theorem dirtyProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultWhile.Fixture.ctx.tys (Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultWhile.readTest Solidity.Yul.Checks.LocalDefaultWhile.proof 9 Solidity.Yul.Checks.LocalDefaultWhile.initial) = none := by

  rfl

theorem sourceCompletion : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env)),
 (Solidity.Source.execS glob frame 9 nps ph Solidity.Yul.Checks.LocalDefaultWhile.statement
   (Solidity.Yul.Checks.LocalDefaultWhile.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultWhile.Fixture.initial.world) = (.ok (.normal (Solidity.Yul.Checks.LocalDefaultWhile.Fixture.initial.clean.set .here (.bool false))), (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultWhile.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

theorem sourceTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env)),
 (Solidity.Source.execS glob frame 8 nps ph Solidity.Yul.Checks.LocalDefaultWhile.statement
   (Solidity.Yul.Checks.LocalDefaultWhile.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultWhile.Fixture.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultWhile.Fixture.env,Solidity.Yul.Checks.LocalDefaultWhile.Fixture.initial.world)) := by

  intro glob frame nps ph
  rfl

#print axioms Solidity.Yul.LocalDefaultWhile.source_agrees
#print axioms Solidity.Yul.LocalDefaultWhile.world
#print axioms Solidity.Yul.LocalDefaultWhile.no_normal
#print axioms Solidity.Yul.LocalDefaultWhile.source_no_normal
#print axioms concrete
#print axioms concreteWorld
#print axioms constantNever
#print axioms constantSourceNever
#print axioms guardTimeout
#print axioms firstTimeout
#print axioms bodyTimeout
#print axioms completion
#print axioms stopUnchanged
#print axioms guardAssignment
#print axioms dirtyProjection
#print axioms sourceCompletion
#print axioms sourceTimeout
end Solidity.Yul.Checks.LocalDefaultWhile
