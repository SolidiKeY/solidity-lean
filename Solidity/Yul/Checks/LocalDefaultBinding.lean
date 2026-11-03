import Solidity.Yul.LocalDefaultBinding
import Solidity.Yul.Checks.LocalBoolWhile

namespace Solidity.Yul.Checks.LocalDefaultBinding
namespace Fixture
export Solidity.Yul.Checks.LocalBoolWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolWhile (initial assigned)

theorem boolDefault : ∀ (env : Solidity.Source.Env), Solidity.Source.Val.default env.layout .bool = some (Solidity.Source.Val.bool false) := by

  intro env
  rfl
def zeroBool : RawDefaultDeclaration.Default Fixture.env .bool := ⟨.bool false,boolDefault Fixture.env⟩
def zero8 := RawDefaultDeclaration.intDefault Fixture.env Solidity.Source.IntTy.u8
def zero256 := RawDefaultDeclaration.intDefault Fixture.env Solidity.Source.IntTy.u256
def items (ty : Solidity.Source.STy) :
    Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ (ty :: Fixture.ctx.tys)
      (.bool :: ty :: Fixture.ctx.tys) :=
  .stmt (.declInit (.unary .not (.local (.there .here))) (by rfl))
    (.stmt (.expr (.assign (.local (.there (.there .here))) (.local .here))) .nil)
def proof (ty : Solidity.Source.STy) :
    LocalBoolItems.Supported Fixture.env [] false ⟨false,false⟩ (items ty) :=
  .declaration (.not (.base (.local (.there .here))))
    (.expression (.assign (.there (.there .here)) (.base (.local .here))) .nil)
def entered {ty} (value : RawDefaultDeclaration.Default Fixture.env ty) :
    LocalState Fixture.env (ty :: Fixture.ctx.tys) :=
  ((.clean value.value,initial.1),initial.2)
def bodyEntered {ty} (value : RawDefaultDeclaration.Default Fixture.env ty) :
    LocalState Fixture.env (.bool :: ty :: Fixture.ctx.tys) :=
  ((.clean (.bool false),(entered value).1),(entered value).2)
def finalState {ty} (value : RawDefaultDeclaration.Default Fixture.env ty) :
    LocalState Fixture.env (.bool :: ty :: Fixture.ctx.tys) :=
  ((.clean (.bool false),(.clean value.value,(assigned false).1)),(assigned false).2)
def program (ty : Solidity.Source.STy) :
    Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
      (.bool :: ty :: Fixture.ctx.tys) := .stmt (.declVar ty) (items ty)
def witness : Nonempty (Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
    (.bool :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys)) := ⟨program _⟩
def concreteInt (ty : Solidity.Source.IntTy) (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultBinding.source_agrees Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys
    (.bool :: .int ty :: Fixture.ctx.tys) (.int ty) (RawDefaultDeclaration.intDefault Fixture.env ty)
    (items (.int ty)) (proof (.int ty)) glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

theorem stages : Solidity.Yul.LocalDefaultBinding.run Solidity.Yul.Checks.LocalDefaultBinding.zero8 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8)) 2 Solidity.Yul.Checks.LocalDefaultBinding.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultBinding.initial ∧
Solidity.Yul.LocalDefaultBinding.run Solidity.Yul.Checks.LocalDefaultBinding.zero8 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8)) 3 Solidity.Yul.Checks.LocalDefaultBinding.initial = .halted .timeout (Solidity.Yul.Checks.LocalDefaultBinding.entered Solidity.Yul.Checks.LocalDefaultBinding.zero8) ∧
Solidity.Yul.LocalDefaultBinding.run Solidity.Yul.Checks.LocalDefaultBinding.zero8 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8)) 5 Solidity.Yul.Checks.LocalDefaultBinding.initial = .halted .timeout (Solidity.Yul.Checks.LocalDefaultBinding.bodyEntered Solidity.Yul.Checks.LocalDefaultBinding.zero8) := by

  exact ⟨rfl,rfl,rfl⟩

theorem completion : Solidity.Yul.LocalDefaultBinding.run Solidity.Yul.Checks.LocalDefaultBinding.zero8 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8)) 6 Solidity.Yul.Checks.LocalDefaultBinding.initial = .normal (Solidity.Yul.Checks.LocalDefaultBinding.finalState Solidity.Yul.Checks.LocalDefaultBinding.zero8) ∧
Solidity.Yul.LocalDefaultBinding.run Solidity.Yul.Checks.LocalDefaultBinding.zero256 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u256)) 6 Solidity.Yul.Checks.LocalDefaultBinding.initial = .normal (Solidity.Yul.Checks.LocalDefaultBinding.finalState Solidity.Yul.Checks.LocalDefaultBinding.zero256) ∧
Solidity.Yul.LocalDefaultBinding.run Solidity.Yul.Checks.LocalDefaultBinding.zeroBool (Solidity.Yul.Checks.LocalDefaultBinding.proof .bool) 6 Solidity.Yul.Checks.LocalDefaultBinding.initial = .normal (Solidity.Yul.Checks.LocalDefaultBinding.finalState Solidity.Yul.Checks.LocalDefaultBinding.zeroBool) := by

  exact ⟨rfl,rfl,rfl⟩

theorem refusal : Solidity.Yul.RawDefaultDeclaration.check Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env (.bytes .memory) = none := by

  rfl

theorem dirtyProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultBinding.Fixture.ctx.tys (Solidity.Yul.LocalDefaultBinding.run Solidity.Yul.Checks.LocalDefaultBinding.zero8 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8)) 6 Solidity.Yul.Checks.LocalDefaultBinding.initial) = none := by

  rfl

theorem sourceControls : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env)),
 (Solidity.Source.execItems glob frame 5 nps ph (Solidity.Yul.Checks.LocalDefaultBinding.program (.int Solidity.Source.IntTy.u8))
   (Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world)) ∧
 (Solidity.Source.execItems glob frame 6 nps ph (Solidity.Yul.Checks.LocalDefaultBinding.program (.int Solidity.Source.IntTy.u8))
   (Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world) =
 (.ok (.normal (.cons (.bool false) (.cons Solidity.Yul.Checks.LocalDefaultBinding.zero8.value
   (Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.clean.set .here (.bool false))))),
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world)) := by

  intro glob frame nps ph
  exact ⟨rfl,rfl⟩

theorem values : ((Solidity.Yul.LocalValues.get (Solidity.Yul.Checks.LocalDefaultBinding.finalState Solidity.Yul.Checks.LocalDefaultBinding.zero8).1 (.there .here)).clean?).map Solidity.Source.Val.key = some (some 0) ∧
(Solidity.Yul.LocalValues.get (Solidity.Yul.Checks.LocalDefaultBinding.finalState Solidity.Yul.Checks.LocalDefaultBinding.zero8).1 (.there (.there (.there (.there .here))))).scalar? = some (Solidity.Yul.word 257) := by

  decide

#print axioms Solidity.Yul.LocalDefaultBinding.source_agrees
#print axioms boolDefault
#print axioms concreteInt
#print axioms stages
#print axioms completion
#print axioms refusal
#print axioms dirtyProjection
#print axioms sourceControls
#print axioms values

theorem restoration : Solidity.Yul.LocalDefaultBinding.restore
 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8))
 (Solidity.Yul.Checks.LocalDefaultBinding.finalState Solidity.Yul.Checks.LocalDefaultBinding.zero8) =
 Solidity.Yul.Checks.LocalDefaultBinding.assigned false ∧
 Solidity.Yul.LocalDefaultBinding.restore
 (Solidity.Yul.Checks.LocalDefaultBinding.proof .bool)
 (Solidity.Yul.Checks.LocalDefaultBinding.finalState Solidity.Yul.Checks.LocalDefaultBinding.zeroBool) =
 Solidity.Yul.Checks.LocalDefaultBinding.assigned false := by
  exact ⟨rfl,rfl⟩

theorem blockControls : Solidity.Yul.LocalDefaultBinding.blockRun
 Solidity.Yul.Checks.LocalDefaultBinding.zero8
 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8))
 7 Solidity.Yul.Checks.LocalDefaultBinding.initial =
 .normal (Solidity.Yul.Checks.LocalDefaultBinding.assigned false) ∧
 Solidity.Yul.LocalDefaultBinding.blockRun
 Solidity.Yul.Checks.LocalDefaultBinding.zero8
 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8))
 6 Solidity.Yul.Checks.LocalDefaultBinding.initial =
 .halted .timeout (Solidity.Yul.Checks.LocalDefaultBinding.bodyEntered Solidity.Yul.Checks.LocalDefaultBinding.zero8) ∧
 Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultBinding.Fixture.ctx.tys
 (Solidity.Yul.LocalDefaultBinding.blockRun Solidity.Yul.Checks.LocalDefaultBinding.zero8
 (Solidity.Yul.Checks.LocalDefaultBinding.proof (.int Solidity.Source.IntTy.u8))
 7 Solidity.Yul.Checks.LocalDefaultBinding.initial) = none := by
  exact ⟨rfl,rfl,rfl⟩

theorem sourceBlockControls : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env)),
 (Solidity.Source.execS glob frame 6 nps ph (.block (Solidity.Yul.Checks.LocalDefaultBinding.program (.int Solidity.Source.IntTy.u8)))
   (Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world)) ∧
 (Solidity.Source.execS glob frame 7 nps ph (.block (Solidity.Yul.Checks.LocalDefaultBinding.program (.int Solidity.Source.IntTy.u8)))
   (Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world) =
 (.ok (.normal (Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.clean.set .here (.bool false))),
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultBinding.Fixture.env,Solidity.Yul.Checks.LocalDefaultBinding.Fixture.initial.world)) := by
  intro glob frame nps ph
  exact ⟨rfl,rfl⟩

def concreteBlockInt (ty : Solidity.Source.IntTy) (glob : Solidity.Source.Glob Fixture.env)
    (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultBinding.block_source_agrees Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: .int ty :: Fixture.ctx.tys) (.int ty)
    (items (.int ty)) (proof (.int ty)) (RawDefaultDeclaration.intDefault Fixture.env ty)
    glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

#print axioms Solidity.Yul.LocalDefaultBinding.suffix
#print axioms Solidity.Yul.LocalDefaultBinding.source_restore
#print axioms Solidity.Yul.LocalDefaultBinding.restore_project
#print axioms Solidity.Yul.LocalDefaultBinding.block_source_agrees
#print axioms restoration
#print axioms blockControls
#print axioms sourceBlockControls
#print axioms concreteBlockInt
end Solidity.Yul.Checks.LocalDefaultBinding
