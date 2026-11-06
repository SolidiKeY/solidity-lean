import Solidity.Lowering.V07.Conversions
import Solidity.Lowering.V07.SourceReads

namespace Solidity.Lowering.V07.Controls
open Solidity.Lowering.V07

def i8 : Source.IntTy := ⟨true, 8, by decide⟩

theorem unsigned_boundary :
    PrimTy.num? (integerValue Source.IntTy.u8 255 (by decide)) = some 255 := integer_observe _ _ _
theorem signed_boundary :
    PrimTy.num? (integerValue i8 (-128) (by decide)) = some (-128) := integer_observe _ _ _
theorem distinct_equal_width :
    integerValue Source.IntTy.u8 1 (by decide) ≠ integerValue Source.IntTy.u8 2 (by decide) := by
  intro h
  have := integer_injective Source.IntTy.u8 1 2 (by decide) (by decide) h
  omega

theorem narrowing_wrap : Source.IntTy.u8.wrap 256 = 0 := by decide
theorem signed_wrap : i8.wrap 128 = -128 := by decide
theorem wrong_narrowing : Source.IntTy.u8.wrap 256 ≠ 256 := by decide

theorem implicit_widening {D : Source.Layout} :
    Source.convVal (.int Source.IntTy.u256)
      (.int 255 (by decide) : Source.Val D (.int Source.IntTy.u8)) =
      .ok (.int 255 (by decide)) := implicit_integer_run _ _ (by decide) _ _

theorem explicit_narrowing {D : Source.Layout} :
    Source.convExplicitVal (.int Source.IntTy.u8)
      (.int 256 (by decide) : Source.Val D (.int Source.IntTy.u256)) =
      .ok (.int 0 (by decide)) := by
  exact explicit_integer_run _ _ _ _

end Solidity.Lowering.V07.Controls
