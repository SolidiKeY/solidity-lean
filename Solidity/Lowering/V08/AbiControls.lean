import Solidity.Lowering.V08.AbiObservations

/-! Kernel controls for exact reason and panic bytes using existing decoders. -/
namespace Solidity.Lowering.V08.AbiControls

/-- Embedded zero, high bytes and an unaligned reason survive the catch. -/
theorem reason_roundtrip : Semantics.decodeError
    (Source.errorData [0x00, 0xff, 0x80, 0x62]) = some [0x00, 0xff, 0x80, 0x62] := by decide +kernel

/-- A selector without its ABI head cannot decode as a reason. -/
theorem malformed_reason : Semantics.decodeError [0x08, 0xc3, 0x79, 0xa0, 0] = none := by decide +kernel

/-- The source panic's exact code is available to the intrinsic catch. -/
theorem panic_catch : (Semantics.decodePanic (Source.panicData .index)).map
    (fun word => word.1) = some (0x32 : Int) := by decide +kernel

/-- Panic catch cannot substitute the arithmetic code for an index failure. -/
theorem wrong_panic : (Semantics.decodePanic (Source.panicData .index)).map
    (fun word => word.1) ≠ some (0x11 : Int) := by decide +kernel

end Solidity.Lowering.V08.AbiControls
