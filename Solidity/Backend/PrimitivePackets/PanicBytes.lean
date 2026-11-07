import Solidity.Source.Observe

/-! Shared Source arithmetic-panic observations. These concern the actual source
encoding; they state no selected-target payload property. -/
namespace Solidity.Backend.PrimitivePackets.PanicBytes

theorem exact_panic_bytes : Source.panicData .arithmetic =
    [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x11] := by
  decide

theorem panic_not_truncated : Source.panicData .arithmetic ≠
    [0x4e,0x48,0x7b,0x71,0x11] := by
  decide

theorem panic_not_empty : Source.panicData .arithmetic ≠ [] := by
  decide

#print axioms exact_panic_bytes
#print axioms panic_not_truncated
#print axioms panic_not_empty
end Solidity.Backend.PrimitivePackets.PanicBytes
