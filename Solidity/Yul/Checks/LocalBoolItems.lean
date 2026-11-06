import Solidity.Yul.LocalBoolItems
import Solidity.Yul.Checks.LocalBoolBinding

namespace Solidity.Yul.Checks.LocalBoolItems
namespace Fixture
export Solidity.Yul.Checks.LocalBoolBinding.Fixture (ctx env initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolBinding (initial)
abbrev C1 := Solidity.Source.STy.bool :: Fixture.ctx.tys
abbrev C2 := Solidity.Source.STy.bool :: C1
abbrev C3 := Solidity.Source.STy.bool :: C2
def program : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys C3 :=
  .stmt (.declInit (τ := .bool) (.bool true) (by rfl))
   (.stmt (.declInit (τ := .bool) (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local (.there (.there .here))) (.local .here)))
     (.stmt (.declInit (τ := .bool) (.unary .not (.local .here)) (by rfl))
      (.stmt (.expr (.assign (.local (.there .here)) (.local .here))) .nil))))
def proof : Solidity.Yul.LocalBoolItems.Supported Fixture.env [] false ⟨false,false⟩ program :=
  .declaration (.base (.literal true)) (.declaration (.base (.local .here)) (.expression (.assign (.there (.there .here)) (.base (.local .here))) (.declaration (.not (.base (.local .here))) (.expression (.assign (.there .here) (.base (.local .here))) (.nil)))))
def witness : Nonempty (Solidity.Yul.LocalBoolItems.Supported Fixture.env [] false ⟨false,false⟩ program) := ⟨proof⟩
def one : LocalState Fixture.env C1 := ((.clean (.bool true),initial.1),initial.2)
def two : LocalState Fixture.env C2 := ((.clean (.bool true),one.1),one.2)
def twoChanged : LocalState Fixture.env C2 :=
  (two.1.set (.there (.there .here)) (.clean (.bool true)),two.2)
def three : LocalState Fixture.env C3 := ((.clean (.bool false),twoChanged.1),twoChanged.2)
def finalState : LocalState Fixture.env C3 :=
  (three.1.set (.there .here) (.clean (.bool false)),three.2)
def rawProgram : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys C2 :=
  .stmt (.declInit (τ := .bool) (.local .here) (by rfl))
    (.stmt (.declInit (τ := .bool) (.local .here) (by rfl)) (.stmt (.expr (.local .here)) .nil))
def rawProof : Solidity.Yul.LocalBoolItems.Supported Fixture.env [] false ⟨false,false⟩ rawProgram :=
  .declaration (.base (.local .here))
    (.declaration (.base (.local .here)) (.expression (.base (.local .here)) .nil))
def rawOne : LocalState Fixture.env C1 := ((initial.1.get .here,initial.1),initial.2)
def rawTwo : LocalState Fixture.env C2 := ((rawOne.1.get .here,rawOne.1),rawOne.2)
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolItems.source_agrees Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys C3 program proof
    glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world



theorem stages : Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.proof 2 Solidity.Yul.Checks.LocalBoolItems.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolItems.initial ∧
Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.proof 3 Solidity.Yul.Checks.LocalBoolItems.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolItems.one ∧
Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.proof 5 Solidity.Yul.Checks.LocalBoolItems.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolItems.two ∧
Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.proof 6 Solidity.Yul.Checks.LocalBoolItems.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolItems.twoChanged ∧
Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.proof 7 Solidity.Yul.Checks.LocalBoolItems.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolItems.three ∧
Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.proof 8 Solidity.Yul.Checks.LocalBoolItems.initial = .normal Solidity.Yul.Checks.LocalBoolItems.finalState := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem values : (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItems.finalState.1 .here).clean? = some (Solidity.Source.Val.bool false) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItems.finalState.1 (.there .here)).clean? = some (Solidity.Source.Val.bool false) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItems.finalState.1 (.there (.there (.there .here)))).clean? = some (Solidity.Source.Val.bool true) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItems.finalState.1 (.there (.there (.there (.there (.there .here)))))).scalar? =
 some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawCopy : Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItems.rawProof 5 Solidity.Yul.Checks.LocalBoolItems.initial = .normal Solidity.Yul.Checks.LocalBoolItems.rawTwo ∧
 Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolItems.Fixture.ctx.tys (.normal Solidity.Yul.Checks.LocalBoolItems.rawTwo) = none ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItems.rawTwo.1 .here).scalar? = some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolItems.rawTwo.1 (.there (.there (.there (.there .here))))).scalar? =
 some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem sourceOutcomes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalBoolItems.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalBoolItems.Fixture.env)),
 (Solidity.Source.execItems glob frame 7 nps ph Solidity.Yul.Checks.LocalBoolItems.program Solidity.Yul.Checks.LocalBoolItems.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItems.Fixture.env,Solidity.Yul.Checks.LocalBoolItems.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItems.Fixture.env,Solidity.Yul.Checks.LocalBoolItems.Fixture.initial.world)) ∧
 (Solidity.Source.execItems glob frame 8 nps ph Solidity.Yul.Checks.LocalBoolItems.program Solidity.Yul.Checks.LocalBoolItems.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItems.Fixture.env,Solidity.Yul.Checks.LocalBoolItems.Fixture.initial.world) =
 (.ok (.normal (Solidity.Source.Locals.cons (.bool false)
   (Solidity.Source.Locals.cons (.bool false) (Solidity.Source.Locals.cons (.bool true)
      (Solidity.Yul.Checks.LocalBoolItems.Fixture.initial.clean.set .here (.bool true)))))),
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItems.Fixture.env,Solidity.Yul.Checks.LocalBoolItems.Fixture.initial.world)) := by
  intro glob frame nps ph; exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolItems.project_up
#print axioms Solidity.Yul.LocalBoolItems.lift_up_run
#print axioms Solidity.Yul.LocalBoolItems.source_agrees
#print axioms concrete
#print axioms stages
#print axioms values
#print axioms rawCopy
#print axioms sourceOutcomes

end Solidity.Yul.Checks.LocalBoolItems
