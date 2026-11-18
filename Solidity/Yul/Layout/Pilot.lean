import Solidity.Yul.Layout.Laws
import Solidity.Yul.Layout.ScalarPilot

/-!
# The Scalar pilot of the one layout view

`pilot_correct` closes `Solidity.Goals.yulLayoutPilot` at `view`, with the laws
`view_laws` and the scalar correspondence `scalarPilot alloc`.
-/
namespace Solidity.Yul.Layout

/-- **The Scalar pilot** of the one layout view. -/
theorem pilot_correct : Solidity.Goals.yulLayoutPilot := ⟨view, view_laws, scalarPilot alloc⟩

end Solidity.Yul.Layout
