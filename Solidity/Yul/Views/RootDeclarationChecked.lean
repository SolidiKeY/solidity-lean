import Solidity.Yul.Views.RootDeclarationSpec

namespace Solidity.Yul.Views

theorem CheckedRootDeclarations.separated {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin) : finiteSeparated r.registrations :=
  (d.pack_spec r.distinct _ _ _ _ r.packed).2.2.1

theorem CheckedRootDeclarations.coverage {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin) :
    r.registrations.map ScalarPath.path = d.paths := d.pack_paths _ _ _ _ r.packed

theorem CheckedRootDeclarations.unique {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin) :
    (r.registrations.map ScalarPath.path).Nodup :=
  List.pairwise_map.mpr (r.separated.imp (fun h => h.1))

theorem CheckedRootDeclarations.extent {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin) : r.endByte = d.endByte (origin.val*32) :=
  d.pack_end _ _ _ _ r.packed

theorem CheckedRootDeclarations.nonwrapping {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin) :
    origin.val*32 ≤ r.endByte ∧ r.endByte ≤ (2^256)*32 := by
  have spec := d.pack_spec r.distinct _ _ _ _ r.packed
  exact ⟨spec.1,spec.2.1 (Nat.mul_le_mul_right 32 (Nat.le_of_lt origin.isLt))⟩

def CheckedRootDeclarations.registry {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin) (_ : Roadmap.Address) :
    List (ScalarPath E.layout (E.lay a)) := r.registrations

end Solidity.Yul.Views
