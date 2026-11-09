import Lean

namespace H62.MigrateYul.MetadataFixture
class Marker (α : Type) where
  value : Nat
instance (priority := 17) global17 : Marker Nat := ⟨17⟩
instance (priority := 63) global63 : Marker Bool := ⟨63⟩
private instance (priority := 11) private11 : Marker UInt64 := ⟨11⟩
namespace Scoped
scoped instance (priority := 41) scoped41 : Marker Int := ⟨41⟩
end Scoped
section
local instance (priority := 97) local97 : Marker String := ⟨97⟩
end
protected def protectedValue : Nat := 5
private def privateValue : Nat := 9
attribute [default_instance 7] global17
end H62.MigrateYul.MetadataFixture
