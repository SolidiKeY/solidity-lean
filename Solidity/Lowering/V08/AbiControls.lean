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

/-- Published panic decoding ignores bytes after its first complete word. -/
theorem panic_trailing_binary : (Semantics.decodePanic
    (Source.panicData .index ++ [0,255,128])).map (fun word => word.1) =
      some (0x32 : Int) := by decide +kernel

/-- A truncated word is still not a panic payload. -/
theorem panic_short_word : Semantics.decodePanic ((Source.panicData .index).take 35) =
    none := by decide +kernel

/-- Sufficient length cannot compensate for a wrong selector. -/
theorem panic_wrong_selector : Semantics.decodePanic
    ([0,0,0,0] ++ (Source.panicData .index).drop 4 ++ [255]) = none := by decide +kernel

/-- Changing the code inside the word is observable despite ignored suffixes. -/
theorem panic_wrong_code_trailing : (Semantics.decodePanic
    (Source.panicData .index ++ [0,255,128])).map (fun word => word.1) ≠
      some (0x11 : Int) := by decide +kernel

#print axioms panic_trailing_binary
#print axioms panic_short_word
#print axioms panic_wrong_selector
#print axioms panic_wrong_code_trailing

end Solidity.Lowering.V08.AbiControls
