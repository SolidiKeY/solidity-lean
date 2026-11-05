import Solidity.Yul.LocalBoolInitialization
import Solidity.Yul.Checks.RawLocalDeclaration

namespace Solidity.Yul.Checks.LocalBoolInitialization
namespace Fixture
export Solidity.Yul.Checks.RawLocalDeclaration (initial)
export Solidity.Yul.Checks.RawLocalDeclaration.Fixture (ctx env)
end Fixture
def initial : LocalState Fixture.env Fixture.ctx.tys := (Fixture.initial.values,Fixture.initial.world)
def readExpr : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool := .local .here
def readProof : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys readExpr := .base (.local .here)
def partialExpr : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool :=
  .binary .and (.assign (.local .here) (.bool true)) (.unary .not (.unary .not (.bool false)))
def partialProof : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys partialExpr :=
  .and (.assign .here (.base (.literal true))) (.not (.not (.base (.literal false))))
def skipExpr : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool :=
  .binary .and (.assign (.local .here) (.bool false)) (.unary .not (.unary .not (.bool false)))
def skipProof : LocalBoolControl.Supported Fixture.env Fixture.ctx.tys skipExpr :=
  .and (.assign .here (.base (.literal false))) (.not (.not (.base (.literal false))))
def declaration : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) := .declInit partialExpr (by rfl)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys)) := ⟨declaration⟩
def assigned (flag : Bool) : LocalState Fixture.env Fixture.ctx.tys :=
  (initial.1.set .here (.clean (.bool flag)),initial.2)
def extended (flag : Bool) : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  ((.clean (.bool false),(assigned flag).1),(assigned flag).2)
def copied : LocalState Fixture.env (.bool :: Fixture.ctx.tys) :=
  ((initial.1.get .here,initial.1),initial.2)
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolInitialization.source_agrees Fixture.env Fixture.ctx.tys partialExpr partialProof
    glob frame fuel nps ph [] false ⟨false,false⟩ Fixture.initial.clean Fixture.initial.world



theorem partial_effects : Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolInitialization.partialProof 4 Solidity.Yul.Checks.LocalBoolInitialization.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolInitialization.assigned true) ∧
 Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolInitialization.partialProof 5 Solidity.Yul.Checks.LocalBoolInitialization.initial = .normal (Solidity.Yul.Checks.LocalBoolInitialization.extended true) ∧
 (Solidity.Yul.Checks.LocalBoolInitialization.assigned true).1.get (.here) = Solidity.Yul.LocalValue.clean (Solidity.Source.Val.bool true) ∧
 (Solidity.Yul.LocalValues.get (Solidity.Yul.Checks.LocalBoolInitialization.assigned true).1 (.there (.there .here))).scalar? = some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawCopy : Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolInitialization.readProof 2 Solidity.Yul.Checks.LocalBoolInitialization.initial = .normal Solidity.Yul.Checks.LocalBoolInitialization.copied ∧
 Solidity.Yul.LocalBoolInitialization.project (.normal Solidity.Yul.Checks.LocalBoolInitialization.copied) = none ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolInitialization.copied.1 .here).scalar? = some (Solidity.Yul.word 2) ∧
 (Solidity.Yul.LocalValues.get Solidity.Yul.Checks.LocalBoolInitialization.copied.1 (.there (.there (.there .here)))).scalar? = some (Solidity.Yul.word 257) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem shortCircuit : Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolInitialization.skipProof 4 Solidity.Yul.Checks.LocalBoolInitialization.initial = .normal (Solidity.Yul.Checks.LocalBoolInitialization.extended false) ∧
 Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolInitialization.partialProof 4 Solidity.Yul.Checks.LocalBoolInitialization.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolInitialization.assigned true) := by
  exact ⟨rfl,rfl⟩

theorem zero : Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolInitialization.partialProof 0 Solidity.Yul.Checks.LocalBoolInitialization.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolInitialization.initial ∧
 Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolInitialization.partialProof 1 Solidity.Yul.Checks.LocalBoolInitialization.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolInitialization.initial := by
  exact ⟨rfl,rfl⟩



theorem sourceOutcomes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalBoolInitialization.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalBoolInitialization.Fixture.env)),
 (Solidity.Source.execS glob frame 4 nps ph Solidity.Yul.Checks.LocalBoolInitialization.declaration Solidity.Yul.Checks.LocalBoolInitialization.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolInitialization.Fixture.env,Solidity.Yul.Checks.LocalBoolInitialization.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolInitialization.Fixture.env,Solidity.Yul.Checks.LocalBoolInitialization.Fixture.initial.world)) ∧
 (Solidity.Source.execS glob frame 5 nps ph Solidity.Yul.Checks.LocalBoolInitialization.declaration Solidity.Yul.Checks.LocalBoolInitialization.Fixture.initial.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolInitialization.Fixture.env,Solidity.Yul.Checks.LocalBoolInitialization.Fixture.initial.world) =
 (.ok (.normal (Solidity.Source.Locals.cons (.bool false)
   (Solidity.Yul.Checks.LocalBoolInitialization.Fixture.initial.clean.set .here (.bool true)))),
   (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolInitialization.Fixture.env,Solidity.Yul.Checks.LocalBoolInitialization.Fixture.initial.world)) := by
  intro glob frame nps ph; exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolInitialization.source_agrees
#print axioms concrete
#print axioms partial_effects
#print axioms rawCopy
#print axioms shortCircuit
#print axioms zero
#print axioms sourceOutcomes

end Solidity.Yul.Checks.LocalBoolInitialization
