import Solidity.Yul.Views.IntDynamicRegions
import Solidity.Yul.Views.PackedDynamicCompatibility

namespace Solidity.Yul.Views

/-- Additive conversion retains the OLD unsigned premise in its original
interface. The new actual-declaration certificate does not assume unsigned. -/
def PackedDynamicHeader.asInteger {E root t cursor} (h : PackedDynamicHeader E root t cursor) : IntDynamicHeader E root t cursor :=
  ⟨h.declared,h.bounded⟩

theorem PackedDynamicHeader.asInteger_registration {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (a : Roadmap.Address) : h.asInteger.registration a = h.registration a := rfl

theorem PackedDynamicHeader.asInteger_element {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) : h.asInteger.element fixed a i = h.element fixed a i := rfl

theorem DynamicHeader.asInteger_full_element {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) :
    h.asPacked.asInteger.element fixed a i = h.element fixed a i :=
  (h.asPacked.asInteger_element fixed a i).trans (h.asPacked_element fixed a i)

end Solidity.Yul.Views
