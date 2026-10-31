import Solidity.Backend.AbiWorld.ErrorLayout

/-! Kernel controls of the existing Error(string) codec, not calldata semantics. -/
namespace Solidity.Backend.AbiWorld.ErrorControls
open Semantics

/-- Empty, last-byte, aligned and first-next-word cases all decode exactly. -/
theorem boundary_roundtrips :
    decodeError (encodeError []) = some [] ∧
    decodeError (encodeError (List.replicate 31 0xa5)) = some (List.replicate 31 0xa5) ∧
    decodeError (encodeError (List.replicate 32 0x7f)) = some (List.replicate 32 0x7f) ∧
    decodeError (encodeError (List.replicate 33 0xff)) = some (List.replicate 33 0xff) := by decide +kernel

/-- Published catch decoding accepts absent padding; no canonicality is added. -/
theorem unpadded_accepted :
    decodeError (errorSelector ++ wordBytes 32 ++ wordBytes 1 ++ [0x42]) = some [0x42] := by decide +kernel

/-- The existing codec also accepts a head-overlapping zero offset. -/
theorem overlapping_head_accepted :
    decodeError (errorSelector ++ wordBytes 0) = some [] := by decide +kernel

/-- A declared byte absent from returndata refuses, rather than returning empty. -/
theorem truncated_payload_refused :
    decodeError (errorSelector ++ wordBytes 32 ++ wordBytes 1) = none := by decide +kernel

/-- A selector alone and a wrong selector do not decode as Error(string). -/
theorem malformed_headers_refused :
    decodeError errorSelector = none ∧ decodeError (encodePanic 1) = none := by decide +kernel

/-- The raw nested Error packet is data, and its outer decoding preserves it. -/
theorem nested_packet :
    decodeError (encodeError (encodeError [0x42])) = some (encodeError [0x42]) := by decide +kernel

/-- Padding without a length is ambiguous; callers must retain the length word. -/
theorem padding_without_length_negative :
    pad32 [0x42] = pad32 [0x42, 0] ∧ ([0x42] : List UInt8) ≠ [0x42, 0] := by decide +kernel

/-- A write in the first payload is observable and cannot be hidden by padding. -/
theorem changed_payload_negative :
    encodeError [0x42] ≠ encodeError [0x43] := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.ErrorControls.boundary_roundtrips' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms boundary_roundtrips
/-- info: 'Solidity.Backend.AbiWorld.ErrorControls.unpadded_accepted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms unpadded_accepted
/-- info: 'Solidity.Backend.AbiWorld.ErrorControls.nested_packet' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms nested_packet
end Solidity.Backend.AbiWorld.ErrorControls
