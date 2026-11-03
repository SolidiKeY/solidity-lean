import Solidity.Yul.LocalBoolBinding
import Solidity.Yul.Checks.LocalBoolInitialization

namespace Solidity.Yul.Checks.LocalBoolBinding
namespace Fixture
export Solidity.Yul.Checks.LocalBoolInitialization.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolInitialization (initial readProof partialProof)
def init : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool := .bool true
def first : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys init := .base (.literal true)
def body : Solidity.Source.RExpr Fixture.env (.bool :: Fixture.ctx.tys) .bool :=
  .binary .and (.assign (.local (.there .here)) (.local .here))
    (.unary .not (.unary .not (.bool false)))
def second : LocalBoolControl.Supported Fixture.env (.bool :: Fixture.ctx.tys) body :=
  .and (.assign (.there .here) (.base (.local .here))) (.not (.not (.base (.literal false))))
def readNew : LocalBoolControl.Supported Fixture.env (.bool :: Fixture.ctx.tys) (.local .here) :=
  .base (.local .here)
def writeNew : LocalBoolControl.Supported Fixture.env (.bool :: Fixture.ctx.tys)
    (.assign (.local .here) (.bool false)) := .assign .here (.base (.literal false))
def extended : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  ((.clean (.bool true),initial.1),initial.2)
def changed : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  (extended.1.set (.there .here) (.clean (.bool true)),extended.2)
def rawExtended : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  ((initial.1.get .here,initial.1),initial.2)
def newChanged : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  (extended.1.set .here (.clean (.bool false)),extended.2)
def program : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) :=
  .stmt (.declInit init (by rfl)) (.stmt (.expr body) .nil)
def witness : Nonempty (Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys)) := ⟨program⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolBinding.source_agrees Fixture.env Fixture.ctx.tys init body first second
    glob frame fuel nps ph [] false ⟨false,false⟩ Fixture.initial.clean Fixture.initial.world



theorem stages : Solidity.Yul.LocalBoolBinding.run Solidity.Yul.Checks.LocalBoolBinding.first Solidity.Yul.Checks.LocalBoolBinding.second 1 Solidity.Yul.Checks.LocalBoolBinding.initial = .initialHalt .timeout Solidity.Yul.Checks.LocalBoolBinding.initial ∧
 Solidity.Yul.LocalBoolBinding.run Solidity.Yul.Checks.LocalBoolBinding.first Solidity.Yul.Checks.LocalBoolBinding.second 3 Solidity.Yul.Checks.LocalBoolBinding.initial = .bodyHalt .timeout Solidity.Yul.Checks.LocalBoolBinding.extended ∧
 Solidity.Yul.LocalBoolBinding.run Solidity.Yul.Checks.LocalBoolBinding.first Solidity.Yul.Checks.LocalBoolBinding.second 6 Solidity.Yul.Checks.LocalBoolBinding.initial = .bodyHalt .timeout Solidity.Yul.Checks.LocalBoolBinding.changed ∧
 Solidity.Yul.LocalBoolBinding.run Solidity.Yul.Checks.LocalBoolBinding.first Solidity.Yul.Checks.LocalBoolBinding.second 7 Solidity.Yul.Checks.LocalBoolBinding.initial = .normal Solidity.Yul.Checks.LocalBoolBinding.changed := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem initializerFailure : Solidity.Yul.LocalBoolBinding.run Solidity.Yul.Checks.LocalBoolBinding.partialProof Solidity.Yul.Checks.LocalBoolBinding.second 5 Solidity.Yul.Checks.LocalBoolBinding.initial =
 .initialHalt .timeout (Solidity.Yul.Checks.LocalBoolInitialization.assigned true) := by
  rfl

theorem binding : (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolBinding.changed.1 .here).clean? = some (Solidity.Source.Val.bool true) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolBinding.changed.1 (.there .here)).clean? = some (Solidity.Source.Val.bool true) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolBinding.changed.1 (.there (.there (.there .here)))).scalar? = some (Solidity.Yul.word 257) ∧
 Solidity.Yul.LocalBoolBinding.run Solidity.Yul.Checks.LocalBoolBinding.first Solidity.Yul.Checks.LocalBoolBinding.writeNew 5 Solidity.Yul.Checks.LocalBoolBinding.initial = .normal Solidity.Yul.Checks.LocalBoolBinding.newChanged := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawCopy : Solidity.Yul.LocalBoolBinding.run Solidity.Yul.Checks.LocalBoolBinding.readProof Solidity.Yul.Checks.LocalBoolBinding.readNew 4 Solidity.Yul.Checks.LocalBoolBinding.initial = .normal Solidity.Yul.Checks.LocalBoolBinding.rawExtended ∧
 Solidity.Yul.LocalBoolBinding.project (.normal Solidity.Yul.Checks.LocalBoolBinding.rawExtended) = none ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolBinding.rawExtended.1 .here).scalar? = some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolBinding.rawExtended.1 (.there (.there (.there .here)))).scalar? = some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem sourceOutcomes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalBoolBinding.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalBoolBinding.Fixture.env)),
 (Solidity.Source.execItems glob frame 6 nps ph Solidity.Yul.Checks.LocalBoolBinding.program Solidity.Yul.Checks.LocalBoolBinding.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolBinding.Fixture.env,Solidity.Yul.Checks.LocalBoolBinding.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolBinding.Fixture.env,Solidity.Yul.Checks.LocalBoolBinding.Fixture.initial.world)) ∧
 (Solidity.Source.execItems glob frame 7 nps ph Solidity.Yul.Checks.LocalBoolBinding.program Solidity.Yul.Checks.LocalBoolBinding.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolBinding.Fixture.env,Solidity.Yul.Checks.LocalBoolBinding.Fixture.initial.world) =
 (.ok (.normal (Solidity.Source.Locals.cons (.bool true)
  (Solidity.Yul.Checks.LocalBoolBinding.Fixture.initial.clean.set .here (.bool true)))),
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolBinding.Fixture.env,Solidity.Yul.Checks.LocalBoolBinding.Fixture.initial.world)) := by
  intro glob frame nps ph; exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolBinding.tail_source_agrees
#print axioms Solidity.Yul.LocalBoolBinding.source_agrees
#print axioms concrete
#print axioms stages
#print axioms initializerFailure
#print axioms binding
#print axioms rawCopy
#print axioms sourceOutcomes

end Solidity.Yul.Checks.LocalBoolBinding
