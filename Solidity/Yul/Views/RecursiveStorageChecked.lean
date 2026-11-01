import Solidity.Yul.Views.RecursiveComputedStorage

namespace Solidity.Yul.Views

/-- Completeness of the actual checked preparation against its concrete input
computation equations. No inverse/read/safety/output-view law is assumed. -/
theorem RecursiveComputedStorage.prepare_eq {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (originComputed : prepareActiveOrigin E active = .ok r.origin) :
    prepareRecursiveComputedStorage d active a = .ok r := by
  cases r with
  | mk origin ordered scopes distinct cs stop packed =>
    unfold prepareRecursiveComputedStorage
    rw [originComputed]
    dsimp only [Bind.bind,Except.bind]
    rw [dif_pos scopes,dif_pos distinct,dif_pos ordered]
    split
    next reason failed =>
      have bad := packed
      rw [failed] at bad
      cases bad
    next out last computed =>
      have same := Except.ok.inj (computed.symm.trans packed)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      rfl

end Solidity.Yul.Views
