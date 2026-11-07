import Solidity.Yul.LocalItemWorld
import Solidity.Yul.Checks.LocalDefaultUnchecked

namespace Solidity.Yul.Checks.LocalItemWorld
namespace Fixture
export Solidity.Yul.Checks.LocalDefaultUnchecked.Fixture (env ctx initial)
end Fixture

def rawState (world : Solidity.Source.St Fixture.env) : LocalState Fixture.env Fixture.ctx.tys :=
  (Solidity.Yul.Checks.LocalDefaultUnchecked.initial.1,world)

def witness := Solidity.Yul.Checks.LocalDefaultUnchecked.witness


theorem allWorlds : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalItemWorld.Fixture.env) (fuel : Nat),
 Solidity.Yul.LocalItemWorld.world
 (Solidity.Yul.LocalDefaultUnchecked.blockRun Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail fuel (Solidity.Yul.Checks.LocalItemWorld.rawState world)) = world := by

  intro world fuel
  exact Solidity.Yul.LocalItemWorld.unchecked_block Solidity.Yul.Checks.LocalItemWorld.Fixture.env [] false false
    Solidity.Yul.Checks.LocalItemWorld.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultUnchecked.Middle Solidity.Yul.Checks.LocalDefaultUnchecked.Out Solidity.Yul.Checks.LocalDefaultUnchecked.inner Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.rest Solidity.Yul.Checks.LocalDefaultUnchecked.tail
    fuel (Solidity.Yul.Checks.LocalItemWorld.rawState world)

theorem successfulLocalEffect : Solidity.Yul.LocalDefaultUnchecked.blockRun Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 11 Solidity.Yul.Checks.LocalDefaultUnchecked.initial =
 .normal (Solidity.Yul.Checks.LocalDefaultUnchecked.assigned true) ∧
 (Solidity.Yul.Checks.LocalDefaultUnchecked.initial.1.get .here).clean? = none ∧
 ((Solidity.Yul.Checks.LocalDefaultUnchecked.assigned true).1.get .here).clean? = some (Solidity.Source.Val.bool true) ∧
 Solidity.Yul.LocalValues.clean? Solidity.Yul.Checks.LocalItemWorld.Fixture.ctx.tys (Solidity.Yul.Checks.LocalDefaultUnchecked.assigned true).1 = none := by

  exact ⟨Solidity.Yul.Checks.LocalDefaultUnchecked.blockCompletion,rfl,rfl,rfl⟩

theorem partialLocalEffect : Solidity.Yul.LocalDefaultUnchecked.run Solidity.Yul.Checks.LocalDefaultUnchecked.inside Solidity.Yul.Checks.LocalDefaultUnchecked.tail 8 Solidity.Yul.Checks.LocalDefaultUnchecked.initial =
 .halted .timeout Solidity.Yul.Checks.LocalDefaultUnchecked.tailEntered ∧
 (Solidity.Yul.Checks.LocalDefaultUnchecked.tailEntered.1.2.get .here).clean? = some (Solidity.Source.Val.bool false) ∧
 Solidity.Yul.LocalValues.clean? (Solidity.Source.STy.int Solidity.Source.IntTy.u8 :: Solidity.Yul.Checks.LocalItemWorld.Fixture.ctx.tys)
 Solidity.Yul.Checks.LocalDefaultUnchecked.tailEntered.1 = none := by

  exact ⟨Solidity.Yul.Checks.LocalDefaultUnchecked.tailTimeout,rfl,rfl⟩

#print axioms Solidity.Yul.LocalItemWorld.bool_run
#print axioms Solidity.Yul.LocalItemWorld.default_run
#print axioms Solidity.Yul.LocalItemWorld.close_world
#print axioms Solidity.Yul.LocalItemWorld.default_block
#print axioms Solidity.Yul.LocalItemWorld.unchecked_run
#print axioms Solidity.Yul.LocalItemWorld.unchecked_block
#print axioms Solidity.Yul.LocalItemWorld.observe_unchecked_block
#print axioms allWorlds
#print axioms successfulLocalEffect
#print axioms partialLocalEffect
end Solidity.Yul.Checks.LocalItemWorld
