import Solidity.Yul.Views.DynamicStoreControls

namespace Solidity.Yul.Views.Controls

theorem dyn_unwritten_zero_view : finiteView (dynRegistry account)
    (dynStorageState.2.ex.world.accounts account).storage (fun _ => 0) :=
  (finiteViewBool_iff _ _ _).mp (by decide)

/-- Pure canonical preparation is the identity of the WHOLE original store,
including none. The ordinary Source.writeLen control separately writes Some0. -/
theorem dyn_pure_zero_keeps_unwritten : finiteWriteback (dynRegistry account) (fun _ => 0)
    (dynStorageState.2.ex.world.accounts account).storage = some (dynStorageState.2.ex.world.accounts account).storage :=
  finiteWriteback_unchanged _ _ _ dyn_unwritten_zero_view

def dynExplicitZero := (dynStorageState.2.ex.world.accounts account).storage.write (dynPath "xs") (.int 0 (by decide))

theorem dyn_explicit_zero_view : finiteView (dynRegistry account) dynExplicitZero (fun _ => 0) :=
  (finiteViewBool_iff _ _ _).mp (by decide)

theorem dyn_pure_zero_keeps_explicit : finiteWriteback (dynRegistry account) (fun _ => 0) dynExplicitZero = some dynExplicitZero :=
  finiteWriteback_unchanged _ _ _ dyn_explicit_zero_view

theorem dyn_admin_states_distinct : (dynStorageState.2.ex.world.accounts account).storage.cell (dynPath "xs") = none ∧
    dynExplicitZero.cell (dynPath "xs") = some (.int 0 (by decide)) := ⟨rfl,rfl⟩

end Solidity.Yul.Views.Controls
