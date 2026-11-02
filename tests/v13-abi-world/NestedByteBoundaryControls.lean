import tests.«v13-abi-world».NestedByteFixtures

namespace Solidity.Backend.AbiWorld.NestedByteControls
open AbiEntry NestedByteReadback
open ByteSequenceReadback (input params values)

theorem boundaries : cursor exactArray 10 (params (.array Element) false) = some 512 ∧
    err (entry overArray 10 (params (.array Element) false)) = 2 ∧
    cursor exactFixed 10 (params (.fixed Element 3) false) = some 480 ∧
    err (entry overFixed 10 (params (.fixed Element 3) false)) = 2 ∧
    cursor arrayI 10 (params (.array Element) false) 17 = some 529 ∧
    err (entry arrayI 9 (params (.array Element) false)) = 3 ∧
    err (entry shortOuter 0 (params (.array Element) false)) = 1 ∧
    err (entry shortCount 0 (params (.array Element) false)) = 3 ∧
    (verdict arrayI 0 (params (.array Element) true)).kind = "blocked: ABI decoder fuel exhausted" := by decide +kernel



/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.boundaries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms boundaries

end Solidity.Backend.AbiWorld.NestedByteControls
