import Solidity.Yul.Views.StorageDeclarationHeaders
import Solidity.Yul.Views.StorageDeclarationTyping

namespace Solidity.Yul.Views

/-- Persistent ordinary declarations, with computed active origin. Dynamic
headers are not claimed as whole arrays; element ownership is separate. -/
structure ComputedStorage {E ds} (d : StorageDeclarations E ds) (active : String) (a : Roadmap.Address) where
  origin : ActiveLayoutOrigin E active
  ordered : ds.map Prod.fst = inheritedRootNames E origin.hierarchy.order false
  sourceDistinct : ∀ scope ∈ origin.hierarchy.order, (allScopeRootNames E (some scope)).Nodup
  distinct : (ds.map Prod.fst).Nodup
  registrations : List (ScalarPath E.layout (E.lay a))
  endByte : Nat
  packed : d.pack a (origin.persistent.val*32) = .ok (registrations,endByte)

def prepareComputedStorage {E ds} (d : StorageDeclarations E ds) (active : String) (a : Roadmap.Address) :
    Except LayoutOriginError (ComputedStorage d active a) := do
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

theorem ComputedStorage.separated {E ds d active a} (r : @ComputedStorage E ds d active a) : finiteSeparated r.registrations :=
  (d.pack_spec r.distinct _ _ _ _ r.packed).2.2.1

theorem ComputedStorage.coverage {E ds d active a} (r : @ComputedStorage E ds d active a) :
    r.registrations.map ScalarPath.path = d.paths := d.pack_paths _ _ _ _ r.packed

theorem ComputedStorage.nonwrapping {E ds d active a} (r : @ComputedStorage E ds d active a) :
    r.origin.persistent.val*32 ≤ r.endByte ∧ r.endByte ≤ (2^256)*32 := by
  have spec := d.pack_spec r.distinct _ _ _ _ r.packed
  exact ⟨spec.1,spec.2.1 (Nat.mul_le_mul_right 32 (Nat.le_of_lt r.origin.persistent.isLt))⟩

theorem ComputedStorage.bank_agreement {E ds d active a} (r : @ComputedStorage E ds d active a)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) : E.transientRoot c.path = false := by
  have rootMember := ((d.pack_spec r.distinct _ _ _ _ r.packed).2.2.2 c member).2.2
  rw [r.ordered] at rootMember
  obtain ⟨scope,inOrder,selected⟩ := List.mem_flatMap.mp rootMember
  exact ordinaryRootNames_bank (r.sourceDistinct scope inOrder) c.path.root selected

def ComputedStorage.headerTrace {E ds d active a} (r : @ComputedStorage E ds d active a) : List (Source.DeclName × Nat) :=
  d.headers (r.origin.persistent.val*32)

theorem ComputedStorage.header_present {E ds d active a} (r : @ComputedStorage E ds d active a)
    (root incoming) (member : (root,incoming) ∈ r.headerTrace) :
    ∃ h : DynamicHeader E root incoming, h.registration a ∈ r.registrations := d.headers_sound _ _ _ _ r.packed root incoming member

def ComputedStorage.storeWriteback {E ds d active a} (r : @ComputedStorage E ds d active a)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) := packedStoreWriteback r.registrations m s

theorem ComputedStorage.reencode {E ds d active a} (r : @ComputedStorage E ds d active a)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteEncode r.registrations out residual = some m :=
  packedStoreWriteback_reencode _ _ _ _ _ r.separated step

theorem ComputedStorage.unchanged {E ds d active a} (r : @ComputedStorage E ds d active a)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView) (view : finiteView r.registrations s m) :
    finiteWriteback r.registrations m s = some s := finiteWriteback_unchanged _ _ _ view

end Solidity.Yul.Views
