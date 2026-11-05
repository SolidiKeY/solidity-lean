import Solidity.Yul.LocalDefaultUnchecked
import Solidity.Yul.Checks.LocalDefaultItems

namespace Solidity.Yul.Checks.LocalDefaultUnchecked
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultItems.Fixture (env ctx initial)
end Fixture
export Solidity.Yul.Checks.LocalDefaultItems (initial assigned zero8 zero256)
def inner : Solidity.Source.RItems Fixture.env [] false ⟨false,true⟩ Fixture.ctx.tys
    (.bool :: .int Solidity.Source.IntTy.u256 :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  .stmt (.declVar (.int Solidity.Source.IntTy.u8))
    (.stmt (.declVar (.int Solidity.Source.IntTy.u256))
      (.stmt (.declInit (.unary .not (.local (.there (.there .here)))) (by rfl))
        (.stmt (.expr (.assign (.local (.there (.there (.there .here)))) (.local .here))) .nil)))

def inside : LocalDefaultItems.Supported Fixture.env [] false ⟨false,true⟩ inner :=
  .declaration zero8 (.declaration zero256
    (.body (.declaration (.not (.base (.local (.there (.there .here)))))
      (.expression (.assign (.there (.there (.there .here))) (.base (.local .here))) .nil))))


abbrev Middle := Solidity.Source.STy.bool :: .int Solidity.Source.IntTy.u256 ::
  .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys
abbrev Out := Solidity.Source.STy.bool :: .int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys
def rest : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Out :=
  .stmt (.declVar (.int Solidity.Source.IntTy.u8))
    (.stmt (.declInit
      (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.local (.there .here)))))))
      (by rfl))
      (.stmt (.expr (.assign (.local (.there (.there .here))) (.local .here))) .nil))
def tail : LocalDefaultItems.Supported Fixture.env [] false ⟨false,false⟩ rest :=
  .declaration zero8 (.body
    (.declaration (.not (.not (.not (.not (.not (.base (.local (.there .here))))))))
      (.expression (.assign (.there (.there .here)) (.base (.local .here))) .nil)))
def tailEntered : LocalState Fixture.env (.int Solidity.Source.IntTy.u8 :: Fixture.ctx.tys) :=
  ((.clean zero8.value,(assigned false).1),(assigned false).2)
def finalState : LocalState Fixture.env Out :=
  ((.clean (.bool true),(.clean zero8.value,(assigned true).1)),(assigned true).2)
def statement : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .block (.unchecked inner rest)
def witness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys Fixture.ctx.tys) := ⟨statement⟩


theorem innerTimeout : Solidity.Yul.LocalDefaultUnchecked.run Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 7 Solidity.Yul.Checks.LocalDefaultUnchecked.initial =
 .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState := by
  rfl

theorem tailTimeout : Solidity.Yul.LocalDefaultUnchecked.run Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 8 Solidity.Yul.Checks.LocalDefaultUnchecked.initial =
 .halted .timeout Solidity.Yul.Checks.LocalDefaultUnchecked.tailEntered := by
  rfl

theorem completion : Solidity.Yul.LocalDefaultUnchecked.run Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 10 Solidity.Yul.Checks.LocalDefaultUnchecked.initial =
 .normal Solidity.Yul.Checks.LocalDefaultUnchecked.finalState := by
  rfl

theorem blockCompletion : Solidity.Yul.LocalDefaultUnchecked.blockRun Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 11 Solidity.Yul.Checks.LocalDefaultUnchecked.initial =
 .normal (Solidity.Yul.Checks.LocalDefaultUnchecked.assigned true) := by
  rfl

theorem blockTimeout : Solidity.Yul.LocalDefaultUnchecked.blockRun Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 9 Solidity.Yul.Checks.LocalDefaultUnchecked.initial =
 .halted .timeout Solidity.Yul.Checks.LocalDefaultUnchecked.tailEntered := by
  rfl

theorem dirtyProjection : Solidity.Yul.LocalBoolItems.project Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.ctx.tys
 (Solidity.Yul.LocalDefaultUnchecked.blockRun Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 11 Solidity.Yul.Checks.LocalDefaultUnchecked.initial) = none := by
  rfl

theorem sourceControls : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env)),
 (Solidity.Source.execS glob frame 10 nps ph Solidity.Yul.Checks.LocalDefaultUnchecked.statement
   (Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env,Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env,Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.world)) ∧
 (Solidity.Source.execS glob frame 11 nps ph Solidity.Yul.Checks.LocalDefaultUnchecked.statement
   (Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env,Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.world) =
 (.ok (.normal (Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.clean.set .here (.bool true))),
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env,Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.world)) := by
  intro glob frame nps ph
  exact ⟨rfl,rfl⟩

theorem innerSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env)),
 (Solidity.Source.execItems glob {frame with checked := false} 7 nps ph Solidity.Yul.Checks.LocalDefaultUnchecked.inner
   (Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.clean.set .here (.bool true))).run
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env,Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.world) =
 (.ok (.normal (.cons (.bool false) (.cons Solidity.Yul.Checks.LocalDefaultUnchecked.zero256.value (.cons Solidity.Yul.Checks.LocalDefaultUnchecked.zero8.value
   (Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.clean.set .here (.bool false)))))),
 (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.env,Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture.initial.world)) := by
  intro glob frame nps ph
  rfl

def concrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.LocalDefaultUnchecked.block_source_agrees Fixture.env [] false false Fixture.ctx.tys
    Middle Out inner inside rest tail glob frame fuel nps ph Fixture.initial.clean Fixture.initial.world

#print axioms Solidity.Yul.LocalDefaultUnchecked.source_agrees
#print axioms Solidity.Yul.LocalDefaultUnchecked.block_source_agrees
#print axioms concrete
#print axioms innerTimeout
#print axioms tailTimeout
#print axioms completion
#print axioms blockCompletion
#print axioms blockTimeout
#print axioms dirtyProjection
#print axioms sourceControls
#print axioms innerSource
end Solidity.Yul.Checks.LocalDefaultUnchecked
