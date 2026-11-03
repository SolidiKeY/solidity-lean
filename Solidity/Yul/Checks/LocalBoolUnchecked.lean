import Solidity.Yul.LocalBoolUnchecked
import Solidity.Yul.Checks.LocalBoolWhile

namespace Solidity.Yul.Checks.LocalBoolUnchecked
namespace Fixture
export Solidity.Yul.Checks.LocalBoolWhile.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalBoolWhile (initial assigned)
abbrev Middle := Solidity.Source.STy.bool :: .bool :: Fixture.ctx.tys
abbrev Out := Solidity.Source.STy.bool :: Fixture.ctx.tys
def inner : Solidity.Source.RItems Fixture.env [] false ⟨false,true⟩ Fixture.ctx.tys Middle :=
  .stmt (.declInit (.bool true) (by rfl)) (.stmt (.declInit (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local (.there (.there .here))) (.local .here))) .nil))
def inside : LocalBoolItems.Supported Fixture.env [] false ⟨false,true⟩ inner :=
  .declaration (.base (.literal true)) (.declaration (.base (.local .here))
    (.expression (.assign (.there (.there .here)) (.base (.local .here))) .nil))
def rest : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Out :=
  .stmt (.declInit
    (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.local .here)))))) (by rfl))
    (.stmt (.expr (.assign (.local (.there .here)) (.local .here))) .nil)
def tail : LocalBoolItems.Supported Fixture.env [] false ⟨false,false⟩ rest :=
  .declaration (.not (.not (.not (.not (.not (.base (.local .here)))))))
    (.expression (.assign (.there .here) (.base (.local .here))) .nil)
def innerEntered : LocalState Fixture.env Middle :=
  ((.clean (.bool true),(.clean (.bool true),initial.1)),initial.2)
def finalState : LocalState Fixture.env Out :=
  ((.clean (.bool false),(assigned false).1),(assigned false).2)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.unchecked inner rest)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩
def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalBoolUnchecked.block_source_agrees Fixture.env [] false false Fixture.ctx.tys
    Middle Out inner inside rest tail glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

theorem stages : Solidity.Yul.LocalBoolUnchecked.run Solidity.Yul.Checks.LocalBoolUnchecked.inside Solidity.Yul.Checks.LocalBoolUnchecked.tail 3 Solidity.Yul.Checks.LocalBoolUnchecked.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolUnchecked.initial ∧
Solidity.Yul.LocalBoolUnchecked.run Solidity.Yul.Checks.LocalBoolUnchecked.inside Solidity.Yul.Checks.LocalBoolUnchecked.tail 5 Solidity.Yul.Checks.LocalBoolUnchecked.initial = .halted .timeout Solidity.Yul.Checks.LocalBoolUnchecked.innerEntered ∧
Solidity.Yul.LocalBoolUnchecked.run Solidity.Yul.Checks.LocalBoolUnchecked.inside Solidity.Yul.Checks.LocalBoolUnchecked.tail 7 Solidity.Yul.Checks.LocalBoolUnchecked.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolUnchecked.assigned true) := by

  exact ⟨rfl,rfl,rfl⟩

theorem completion : Solidity.Yul.LocalBoolUnchecked.run Solidity.Yul.Checks.LocalBoolUnchecked.inside Solidity.Yul.Checks.LocalBoolUnchecked.tail 9 Solidity.Yul.Checks.LocalBoolUnchecked.initial = .normal Solidity.Yul.Checks.LocalBoolUnchecked.finalState ∧
Solidity.Yul.LocalBoolUnchecked.blockRun Solidity.Yul.Checks.LocalBoolUnchecked.inside Solidity.Yul.Checks.LocalBoolUnchecked.tail 10 Solidity.Yul.Checks.LocalBoolUnchecked.initial = .normal (Solidity.Yul.Checks.LocalBoolUnchecked.assigned false) ∧
Solidity.Yul.LocalBoolUnchecked.blockRun Solidity.Yul.Checks.LocalBoolUnchecked.inside Solidity.Yul.Checks.LocalBoolUnchecked.tail 8 Solidity.Yul.Checks.LocalBoolUnchecked.initial = .halted .timeout (Solidity.Yul.Checks.LocalBoolUnchecked.assigned true) := by

  exact ⟨rfl,rfl,rfl⟩

theorem dirtyProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.ctx.tys (Solidity.Yul.LocalBoolUnchecked.blockRun Solidity.Yul.Checks.LocalBoolUnchecked.inside Solidity.Yul.Checks.LocalBoolUnchecked.tail 10 Solidity.Yul.Checks.LocalBoolUnchecked.initial) = none := by

  rfl

theorem sourceControls : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.env)),
 (Solidity.Source.execS glob frame 8 nps ph Solidity.Yul.Checks.LocalBoolUnchecked.statement
   (Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.env,Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.env,Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.initial.world)) ∧
 (Solidity.Source.execS glob frame 10 nps ph Solidity.Yul.Checks.LocalBoolUnchecked.statement
   (Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.env,Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.initial.world) =
 (.ok (.normal (Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.initial.clean.set .here (.bool false))),
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.env,Solidity.Yul.Checks.LocalBoolUnchecked.Fixture.initial.world)) := by

  intro glob frame nps ph
  exact ⟨rfl,rfl⟩

#print axioms Solidity.Yul.LocalBoolUnchecked.source_agrees
#print axioms Solidity.Yul.LocalBoolUnchecked.block_source_agrees
#print axioms concrete
#print axioms stages
#print axioms completion
#print axioms dirtyProjection
#print axioms sourceControls
end Solidity.Yul.Checks.LocalBoolUnchecked
