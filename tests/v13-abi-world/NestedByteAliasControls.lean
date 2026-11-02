import tests.«v13-abi-world».NestedByteFixtures

namespace Solidity.Backend.AbiWorld.NestedByteControls
open AbiEntry NestedByteReadback
open ByteSequenceReadback (input params values)

theorem aliases : cursor sharedOuter 10 (params (.array Element) false) = some 672 ∧
    EntryTransport.bodyObservation sharedOuter 10 (params (.array Element) false) AbiEntry.encodeArgs =
      some (encodeArgs (values (.array (sequence [[[],[0,255]],[[],[0,255]],[(List.range 33).map UInt8.ofNat]])))) ∧
    cursor sharedInner 10 (params (.array Element) false) = some 544 ∧
    EntryTransport.bodyObservation sharedInner 10 (params (.array Element) false) AbiEntry.encodeArgs =
      some (encodeArgs (values (.array (sequence [[],[[0,255],[0,255]],[(List.range 33).map UInt8.ofNat]])))) ∧
    EntryTransport.bodyObservation sharedInner 10 (params (.array Element) false) AbiEntry.encodeArgs ≠
      some (encodeArgs (values (.array xs))) := by decide +kernel



/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.aliases' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms aliases

end Solidity.Backend.AbiWorld.NestedByteControls
