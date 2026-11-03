import Solidity.Yul.Views.ComputedLayout

namespace Solidity.Yul.Views

/-- Staged evaluation of the EXISTING checked builder. All premises are real
metadata checks and actual pack computation, not inverse/read/safety laws. -/
theorem prepareInherited_exact {E ds} (d : RootDeclarations E ds) (active : String)
    (tr : Bool) (a : Roadmap.Address) (origin : Roadmap.Word) (h : StorageHierarchy E active)
    (ready : prepareStorageHierarchy E active = .ok h)
    (sourceDistinct : ∀ scope ∈ h.order, (allScopeRootNames E (some scope)).Nodup)
    (distinct : (ds.map Prod.fst).Nodup)
    (ordered : ds.map Prod.fst = inheritedRootNames E h.order tr)
    (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (packed : d.pack a (origin.val*32) = .ok (cs,stop)) :
    prepareInheritedDeclarations d active tr a origin =
      .ok ⟨h,ordered,sourceDistinct,distinct,cs,stop,packed⟩ := by
  simp only [prepareInheritedDeclarations,ready,Bind.bind,Except.bind,
    dif_pos sourceDistinct,dif_pos distinct,dif_pos ordered]
  split
  · rename_i reason failed
    rw [failed] at packed
    cases packed
  · rename_i found last succeeded
    have same : (found,last) = (cs,stop) := Except.ok.inj (succeeded.symm.trans packed)
    cases same
    rfl

theorem prepareComputed_exact {E ds} (d : RootDeclarations E ds) (active : String) (tr : Bool) (a : Roadmap.Address)
    (origin : ActiveLayoutOrigin E active) (originReady : prepareActiveOrigin E active = .ok origin)
    (layout : CheckedInheritedDeclarations d active tr a (origin.forBank tr))
    (layoutReady : prepareInheritedDeclarations d active tr a (origin.forBank tr) = .ok layout) :
    prepareComputedLayout d active tr a = .ok ⟨origin,layout⟩ := by
  simp only [prepareComputedLayout,originReady,Bind.bind,Except.bind,
    layoutReady,Except.mapError]
  rfl

end Solidity.Yul.Views
