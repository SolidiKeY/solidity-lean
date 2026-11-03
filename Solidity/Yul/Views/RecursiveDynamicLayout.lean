import Solidity.Yul.Views.RecursiveDynamicPack
import Solidity.Yul.Views.RecursiveStorageChecked

namespace Solidity.Yul.Views.Controls

theorem rcOrigin_ready : (prepareActiveOrigin rcEnv "RC").toOption.isSome := by decide
def rcOrigin := (prepareActiveOrigin rcEnv "RC").toOption.get rcOrigin_ready
theorem rcOrigin_computed : prepareActiveOrigin rcEnv "RC" = .ok rcOrigin := except_computed_value _ rcOrigin_ready

/-- Data are actual composed leaf outputs, not an assumed layout/inverse law.
The packed field is PROVED by rcDeclarations_packed above. This shares computed
subresults instead of repeatedly normalizing the entire tree in each control. -/
def rcLayout : RecursiveComputedStorage rcDeclarations "RC" account where
  origin := rcOrigin
  ordered := by decide
  sourceDistinct := by
    intro scope member
    change scope ∈ ["RC"] at member
    have same := List.mem_singleton.mp member
    subst scope
    decide
  distinct := by decide
  registrations := rcRootOut.1
  endByte := rcRootOut.2
  packed := by
    change rcDeclarations.pack account 0 = .ok (rcRootOut.1,rcRootOut.2)
    exact rcDeclarations_packed

theorem rc_prepared : prepareRecursiveComputedStorage rcDeclarations "RC" account = .ok rcLayout :=
  rcLayout.prepare_eq rcOrigin_computed

theorem rc_ready : (prepareRecursiveComputedStorage rcDeclarations "RC" account).toOption.isSome := by
  rw [rc_prepared]
  rfl

end Solidity.Yul.Views.Controls
