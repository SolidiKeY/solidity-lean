import tests.«v13-abi-world».NestedByteFixtures

namespace Solidity.Backend.AbiWorld.NestedByteControls
open AbiEntry NestedByteReadback
open ByteSequenceReadback (input params values)

theorem layout : load arrayI.data 36 = 3 ∧ load arrayI.data 68 = 96 ∧ load arrayI.data 100 = 128 ∧
    load arrayI.data 132 = 320 ∧ load arrayI.data 164 = 0 ∧ load arrayI.data 196 = 2 ∧
    load arrayI.data 228 = 64 ∧ load arrayI.data 260 = 96 ∧ load arrayI.data 292 = 0 ∧
    load arrayI.data 324 = 2 ∧ load arrayI.data 388 = 1 ∧ load arrayI.data 420 = 32 ∧
    load arrayI.data 452 = 33 ∧ cursor arrayI 10 (params (.array Element) false) = some 512 ∧
    cursor arrayI 10 (params (.array Element) true) = some 0 ∧
    cursor fixedI 10 (params (.fixed Element 3) false) = some 480 ∧
    load mixedI.data 4 = 64 ∧ load mixedI.data 36 = AbiEntry.W - 1 ∧
    cursor mixedI 10 (NestedByteListReadback.params (.uint 256) false) = some 512 := by decide +kernel



/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.layout' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms layout

end Solidity.Backend.AbiWorld.NestedByteControls
