import Solidity.Backend.PrimitivePackets.SignedCheckedAdd.Agreement
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.PrimitivePackets.SignedCheckedAdd.Controls
open Source.SemanticsExamples (E0 G0 F0 s0)
abbrev Γ : Source.RCtx := [.int U,.int U]
def input (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) : Source.EMState E0 Γ :=
  (.cons (.int x hx) (.cons (.int y hy) .nil),s0)

theorem success (p : Roadmap.Pipeline) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (fits : U.lo ≤ x+y ∧ x+y ≤ U.hi) :
    (Source.evalE (G0 p) {F0 with checked := true} 3
      (.binary .add (.local .here) (.local (.there .here)))).run (input x y hx hy) =
      (.ok (.val (.int (x+y) fits)),input x y hx hy) := by
  first | rfl | exact source_success (G0 p) F0 0 _ _ _ x y hx hy rfl rfl fits

theorem failure (p : Roadmap.Pipeline) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (outside : ¬ (U.lo ≤ x+y ∧ x+y ≤ U.hi)) :
    (Source.evalE (G0 p) {F0 with checked := true} 3
      (.binary .add (.local .here) (.local (.there .here)))).run (input x y hx hy) =
      (.error (.revert (Source.panicData .arithmetic)),input x y hx hy) := by
  first | rfl | exact source_overflow (G0 p) F0 0 _ _ _ x y hx hy rfl rfl outside

def maximum (p : Roadmap.Pipeline) := success p U.hi 0 (by decide) (by decide) (by decide)
def minimum (p : Roadmap.Pipeline) := success p U.lo 0 (by decide) (by decide) (by decide)
def positiveOverflow (p : Roadmap.Pipeline) := failure p U.hi 1 (by decide) (by decide) (by decide)
def negativeOverflow (p : Roadmap.Pipeline) := failure p U.lo (-1) (by decide) (by decide) (by decide)
def mixedSigns (p : Roadmap.Pipeline) := success p (-7) 9 (by decide) (by decide) (by decide)

theorem panic_not_empty : Source.panicData .arithmetic ≠ [] := by decide
theorem exact_panic : Source.panicData .arithmetic =
    [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x11] := by decide
end Solidity.Backend.PrimitivePackets.SignedCheckedAdd.Controls
