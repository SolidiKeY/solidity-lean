import tests.«v13-abi-world».NestedByteFixtures

namespace Solidity.Backend.AbiWorld.NestedByteControls
open AbiEntry NestedByteReadback
open ByteSequenceReadback (input params values)

theorem fixture_boundaries : fixtures.map (fun bs => (verdict (fixtureInput bs) 10 (params (.array Element) false)).kind) =
    List.replicate 6 "run" ∧ fixtures.map (fun bs => cursor (fixtureInput bs) 10 (params (.array Element) false)) =
      [some 32,some 96,some 160,some 352,some 416,some 512] := by decide +kernel

theorem fixed_zero : err (entry emptyFixed 2 (params (.fixed Element 0) false)) = 1 ∧
    cursor emptyFixed 2 (params (.fixed Element 0) true) = some 0 ∧
    (verdict emptyFixed 2 (params (.fixed Element 0) true)).kind =
      "blocked: calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics" ∧
    (verdict emptyFixed 2 readonlyZero).kind = "run" ∧
    cursor paddedEmptyFixed 2 (params (.fixed Element 0) false) = some 0 := by decide +kernel



/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.fixture_boundaries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fixture_boundaries
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.fixed_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fixed_zero

end Solidity.Backend.AbiWorld.NestedByteControls
