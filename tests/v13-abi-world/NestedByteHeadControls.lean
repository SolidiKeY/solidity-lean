import tests.«v13-abi-world».NestedByteFixtures

namespace Solidity.Backend.AbiWorld.NestedByteControls
open AbiEntry NestedByteReadback
open ByteSequenceReadback (params values)

def shortHeads : Input := ⟨arrayI.data.take 100,128⟩
def shortInnerHeads : Input := ⟨arrayI.data.take 260,128⟩
def beforeInnerHeads : Input := {shortInnerHeads with free := lim - 230}

theorem head_priority : err (entry shortHeads 10 (params (.array Element) false)) = 1 ∧
    err (entry shortInnerHeads 10 (params (.array Element) false)) = 1 ∧
    err (entry beforeInnerHeads 10 (params (.array Element) false)) = 2 ∧
    err (entry beforeInnerHeads 0 (params (.array Element) false)) = 3 := by decide +kernel

def remaining := sequence [[[],[0,255]],[(List.range 33).map UInt8.ofNat]]

/-- Actual nonzero original index/base/cursor fragment, not a claim about
compiled caller-frame provenance or a physical byte-memory machine. -/
theorem reached_fragment : mseq arrayI 7 Element 68 1 2 13 = .ok (remaining,365) := by
  have h := sequence_window remaining arrayI (arrayI.data.take 100) (arrayI.data.drop 164)
    (arrayI.data.take 196) suffix 68 1 128 13 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have cost : tailCost remaining = 352 := by
    rw [remaining,tail_sequence]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,innerCost,
      ByteSequenceControls.tail_sequence,List.length_cons,List.length_nil]
    decide +kernel
  simpa only [cost] using h

theorem empty_fixed_typed (lazy : Bool) : ∃ es,
    entry paddedEmptyFixed 2 (params (.fixed Element 0) lazy) = .ok es ∧
    bodyValues paddedEmptyFixed 2 (params (.fixed Element 0) lazy) es 0 = .ok (values (.fixed (sequence []))) := by
  obtain ⟨es,en,ep,body,run⟩ := fixed_roundtrip (sequence []) selector (List.replicate 32 0) 128 2 lazy
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨es,ep,body⟩


/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.head_priority' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms head_priority
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.reached_fragment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_fragment
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.empty_fixed_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_fixed_typed

end Solidity.Backend.AbiWorld.NestedByteControls
