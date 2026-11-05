import Solidity.Yul.Views.DynamicStoreControls

namespace Solidity.Yul.Views.Controls

theorem dyn_non_header_not_selected : dynComputed.header? (dynName "marker") = none := by decide

theorem dyn_wrong_member_is_not_cell : dynEnv.cellTy ⟨dynName "xs",[.field 0]⟩ = .tuple [] := rfl

def dynCollisionFixed : Roadmap.Evm.Fixed where
  keccak _ := 1000
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

theorem dyn_collision_not_disjoint :
    ¬Hash.RegionsDisjoint (2^256) 8 (fixedLayoutHash dynCollisionFixed) dynRoots dynPreimages := by decide

def dynHighFixed : Roadmap.Evm.Fixed where
  keccak _ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

/-- Physical modular arithmetic is retained; it is not a fabricated Yul
refusal when the separate nonwrapping/separation premise is unavailable. -/
theorem dyn_modular_wrap_retained : (dynX.element dynHighFixed account 1).slot = 0 := by decide

def dynAliasState : Source.EMState dynEnv [dynArray,dynArray] :=
  ⟨.cons dynX.reference (.cons dynX.reference .nil),dynWrittenState.2⟩

theorem dyn_actual_alias_lengths :
    (Source.lengthOf (E := dynEnv) packedStepFrame (dynAliasState.1.get .here)).run dynAliasState = (.ok 2,dynAliasState) ∧
    (Source.lengthOf (E := dynEnv) packedStepFrame (dynAliasState.1.get (.there .here))).run dynAliasState = (.ok 2,dynAliasState) := ⟨rfl,rfl⟩

theorem dyn_actual_alias_element :
    (do
      let loc ← Source.indexLoc (E := dynEnv) packedStepFrame (dynAliasState.1.get (.there .here)) 1
      Source.readLoc packedStepFrame loc).run dynAliasState =
        (.ok (.int (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (by decide)),dynAliasState) := rfl

def dynShrink := (Source.writeLen (E := dynEnv) packedStepFrame (dynPath "xs") 0).run dynWrittenState

theorem dyn_shrink_preserves_typed_data : dynShrink.1 = .ok () ∧
    (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run dynShrink.2 = (.ok 0,dynShrink.2) ∧
    (dynShrink.2.2.ex.world.accounts account).storage.read ⟨dynName "xs",[.index 1]⟩ =
      some (.int (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (by decide)) := ⟨rfl,rfl,rfl⟩

def dynRegrow := (Source.writeLen (E := dynEnv) packedStepFrame (dynPath "xs") 2).run dynShrink.2

theorem dyn_regrow_preserves_typed_data : dynRegrow.1 = .ok () ∧
    (Source.indexLoc (E := dynEnv) packedStepFrame dynX.reference 1).run dynRegrow.2 =
      (.ok (.stor ⟨dynName "xs",[.index 1]⟩),dynRegrow.2) ∧
    (dynRegrow.2.2.ex.world.accounts account).storage.read ⟨dynName "xs",[.index 1]⟩ =
      some (.int (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (by decide)) := ⟨rfl,rfl,rfl⟩

end Solidity.Yul.Views.Controls
