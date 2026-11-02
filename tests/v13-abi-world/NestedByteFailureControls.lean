import tests.«v13-abi-world».NestedByteFixtures

namespace Solidity.Backend.AbiWorld.NestedByteControls
open AbiEntry NestedByteReadback
open ByteSequenceReadback (input params values)

theorem failures : err (entry wrongBase 10 (params (.array Element) false)) = 1 ∧
    err (entry badOffset 10 (params (.array Element) false)) = 1 ∧
    err (entry badCount 10 (params (.array Element) false)) = 2 ∧
    err (entry badInnerCount 10 (params (.array Element) false)) = 2 ∧
    cursor badInnerCount 10 (params (.array Element) true) = some 0 ∧
    EntryTransport.bodyObservation badInnerCount 10 (params (.array Element) true) AbiEntry.encodeArgs = none ∧
    err (entry shortCount 10 (params (.array Element) false)) = 1 ∧
    err (entry shortInnerCount 10 (params (.array Element) false)) = 1 ∧
    err (entry shortPayload 10 (params (.array Element) false)) = 1 ∧
    err (entry lastPanic 10 (params (.array Element) false)) = 2 ∧
    err (entry shortHeader 10 (params (.array Element) false)) = 1 := by decide +kernel



/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.failures' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms failures

end Solidity.Backend.AbiWorld.NestedByteControls
