import Solidity.Yul.LocalDefaultItems
import Solidity.Yul.Checks.LocalDefaultBinding

namespace Solidity.Yul.Checks.LocalDefaultItems
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultBinding.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalDefaultBinding (initial assigned zero8 zero256)

def items : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
    (.bool :: .int Solidity.Source.IntTy.u256 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  .stmt (.declVar (.int Solidity.Source.IntTy.u8))
    (.stmt (.declVar (.int Solidity.Source.IntTy.u256))
      (.stmt (.declInit (.unary .not (.local (.there (.there .here)))) (by rfl))
        (.stmt (.expr (.assign (.local (.there (.there (.there .here)))) (.local .here))) .nil)))

def proof : LocalDefaultItems.Supported Fixture.env [] false ⟨false,false⟩ items :=
  .declaration zero8 (.declaration zero256
    (.body (.declaration (.not (.base (.local (.there (.there .here)))))
      (.expression (.assign (.there (.there (.there .here))) (.base (.local .here))) .nil))))

def firstState : LocalState Fixture.env (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ((.clean zero8.value,initial.1),initial.2)
def secondState : LocalState Fixture.env
    (.int Solidity.Source.IntTy.u256 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ((.clean zero256.value,firstState.1),firstState.2)
def bodyState : LocalState Fixture.env
    (.bool :: .int Solidity.Source.IntTy.u256 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ((.clean (.bool false),secondState.1),secondState.2)
def finalState : LocalState Fixture.env
    (.bool :: .int Solidity.Source.IntTy.u256 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ((.clean (.bool false),(.clean zero256.value,(.clean zero8.value,(assigned false).1))),
    (assigned false).2)

def witness : Nonempty (LocalDefaultItems.Supported Fixture.env [] false ⟨false,false⟩ items) :=
  ⟨proof⟩

def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultItems.source_agrees Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys _ items proof glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world


theorem controls : Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 2 Solidity.Yul.Checks.LocalDefaultItems.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.initial ∧
Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 3 Solidity.Yul.Checks.LocalDefaultItems.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.firstState ∧
Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 4 Solidity.Yul.Checks.LocalDefaultItems.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.secondState ∧
Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 6 Solidity.Yul.Checks.LocalDefaultItems.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState ∧
Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 7 Solidity.Yul.Checks.LocalDefaultItems.initial = .normal Solidity.Yul.Checks.LocalDefaultItems.finalState ∧
Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultItems.Fixture.ctx.tys
 (Solidity.Yul.LocalDefaultItems.run Solidity.Yul.Checks.LocalDefaultItems.proof 7 Solidity.Yul.Checks.LocalDefaultItems.initial) = none := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceControls : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultItems.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultItems.Fixture.env)),
 (Solidity.Source.execItems glob frame 6 nps ph Solidity.Yul.Checks.LocalDefaultItems.items
   (Solidity.Yul.Checks.LocalDefaultItems.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultItems.Fixture.env,Solidity.Yul.Checks.LocalDefaultItems.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultItems.Fixture.env,Solidity.Yul.Checks.LocalDefaultItems.Fixture.initial.world)) ∧
 (Solidity.Source.execItems glob frame 7 nps ph Solidity.Yul.Checks.LocalDefaultItems.items
   (Solidity.Yul.Checks.LocalDefaultItems.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultItems.Fixture.env,Solidity.Yul.Checks.LocalDefaultItems.Fixture.initial.world) =
 (.ok (.normal (.cons (.bool false) (.cons Solidity.Yul.Checks.LocalDefaultItems.zero256.value (.cons Solidity.Yul.Checks.LocalDefaultItems.zero8.value
   (Solidity.Yul.Checks.LocalDefaultItems.Fixture.initial.clean.set .here (.bool false)))))),
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultItems.Fixture.env,Solidity.Yul.Checks.LocalDefaultItems.Fixture.initial.world)) := by
  intro glob frame nps ph
  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalDefaultItems.source_agrees
#print axioms concrete
#print axioms controls
#print axioms sourceControls
end Solidity.Yul.Checks.LocalDefaultItems
