import Solidity.Yul.Views.RecursiveRootStorage
import Solidity.Yul.Views.ComputedStorage

namespace Solidity.Yul.Views

/-- Persistent ordinary declarations, with computed active origin. Dynamic
headers are not claimed as whole arrays; element ownership is separate. -/
structure RecursiveComputedStorage {E ds} (d : RecursiveRootDeclarations E ds) (active : String) (a : Roadmap.Address) where
  origin : ActiveLayoutOrigin E active
  ordered : ds.map Prod.fst = inheritedRootNames E origin.hierarchy.order false
  sourceDistinct : ∀ scope ∈ origin.hierarchy.order, (allScopeRootNames E (some scope)).Nodup
  distinct : (ds.map Prod.fst).Nodup
  registrations : List (ScalarPath E.layout (E.lay a))
  endByte : Nat
  packed : d.pack a (origin.persistent.val*32) = .ok (registrations,endByte)

def prepareRecursiveComputedStorage {E ds} (d : RecursiveRootDeclarations E ds) (active : String) (a : Roadmap.Address) :
    Except LayoutOriginError (RecursiveComputedStorage d active a) := do
  let origin ← prepareActiveOrigin E active
  if sourceDistinct : ∀ scope ∈ origin.hierarchy.order, (allScopeRootNames E (some scope)).Nodup then
    if distinct : (ds.map Prod.fst).Nodup then
      if ordered : ds.map Prod.fst = inheritedRootNames E origin.hierarchy.order false then
        match packed : d.pack a (origin.persistent.val*32) with
        | .error reason => .error (.declarations (.packing reason))
        | .ok (cs,stop) => .ok ⟨origin,ordered,sourceDistinct,distinct,cs,stop,packed⟩
      else .error (.declarations .metadataOrder)
    else .error (.declarations .duplicateRoots)
  else .error (.declarations .duplicateDeclarations)

theorem RecursiveComputedStorage.separated {E ds d active a} (r : @RecursiveComputedStorage E ds d active a) : finiteSeparated r.registrations :=
  (d.pack_spec r.distinct _ _ _ _ r.packed).2.2.1

theorem RecursiveComputedStorage.nonwrapping {E ds d active a} (r : @RecursiveComputedStorage E ds d active a) :
    r.origin.persistent.val*32 ≤ r.endByte ∧ r.endByte ≤ (2^256)*32 := by
  have spec := d.pack_spec r.distinct _ _ _ _ r.packed
  exact ⟨spec.1,spec.2.1 (Nat.mul_le_mul_right 32 (Nat.le_of_lt r.origin.persistent.isLt))⟩

theorem RecursiveComputedStorage.bank_agreement {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) : E.transientRoot c.path = false := by
  have rootMember := ((d.pack_spec r.distinct _ _ _ _ r.packed).2.2.2 c member).2.2
  rw [r.ordered] at rootMember
  obtain ⟨scope,inOrder,selected⟩ := List.mem_flatMap.mp rootMember
  exact ordinaryRootNames_bank (r.sourceDistinct scope inOrder) c.path.root selected


end Solidity.Yul.Views
