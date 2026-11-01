import Solidity.Yul.Views.FixedDeclarationExtent

namespace Solidity.Yul.Views

/-- Stores actual checked computation, not presumed layout/readback laws. -/
structure CheckedFixedDeclaration {E τ} (d : FixedDeclaration E τ) (root : Source.DeclName)
    (a : Roadmap.Address) (base : Roadmap.Word) where
  rootFound : E.rootTy root = some τ
  registrations : List (ScalarPath E.layout (E.lay a))
  endByte : Nat
  packed : d.pack ⟨root,[]⟩ a (base.val*32) = .ok (registrations,endByte)

def checkFixedDeclaration {E τ} (d : FixedDeclaration E τ) (root : Source.DeclName)
    (a : Roadmap.Address) (base : Roadmap.Word) : Except DeclarationPackingError (CheckedFixedDeclaration d root a base) :=
  if rootFound : E.rootTy root = some τ then
    match packed : d.pack ⟨root,[]⟩ a (base.val*32) with
    | .error reason => .error reason
    | .ok (cs,stop) => .ok ⟨rootFound,cs,stop,packed⟩
  else .error .missingRoot

theorem CheckedFixedDeclaration.separated {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base) :
    finiteSeparated r.registrations := (d.pack_good _ _ _ _ _ r.packed).2.2.1

theorem CheckedFixedDeclaration.extent {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base) :
    r.endByte = d.endByte (base.val*32) := d.pack_end _ _ _ _ _ r.packed

theorem CheckedFixedDeclaration.nonwrapping {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base) :
    base.val*32 ≤ r.endByte ∧ r.endByte ≤ (2^256)*32 := by
  have spec := d.pack_good _ _ _ _ _ r.packed
  exact ⟨spec.1,spec.2.1 (Nat.mul_le_mul_right 32 (Nat.le_of_lt base.isLt))⟩

theorem CheckedFixedDeclaration.coverage {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base) :
    r.registrations.map ScalarPath.path = d.paths ⟨root,[]⟩ := d.pack_paths _ _ _ _ _ r.packed

theorem CheckedFixedDeclaration.unique {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base) :
    (r.registrations.map ScalarPath.path).Nodup := by
  exact List.pairwise_map.mpr (r.separated.imp (fun h => h.1))

end Solidity.Yul.Views
