import tests.«v13-abi-world».SiblingFixtures
namespace Solidity.Backend.AbiWorld.SiblingWindowControls
open AbiEntry RecursiveLayout RecursiveEntry SiblingReadback SiblingControls

def hp : List UInt8 := SiblingControls.sel ++ AbiEntry.wordBytes 128
def lead : List UInt8 := AbiEntry.Val.enc (.bytes [])
def shifted : Input := ⟨hp ++ (AbiEntry.assemble.go (Vals.parts SiblingControls.vs ++ Vals.parts hi) 160).1 ++ lead ++
  (AbiEntry.assemble.go (Vals.parts SiblingControls.vs ++ Vals.parts hi) 160).2 ++ SiblingControls.post,128⟩

theorem shifted_size : shifted.size = 678 := by
  rw [window_size ps qs SiblingControls.vs hi shifted hp lead SiblingControls.post 160 rfl,
    prefix_tail_length,show hi = later [[],(List.range 33).map UInt8.ofNat] from rfl,later_tail_length]
  simp only [hp,lead,SiblingControls.sel,SiblingControls.post,List.length_append,MixedPacket.word_length,
    ByteSequenceReadback.array_length,ByteSequenceControls.tail_sequence,
    measurements.1,measurements.2.1,List.length_cons,List.length_nil,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_replicate]
  decide +kernel

theorem shifted_typed : ∃ es, enter shifted 11 ps 32 17 = .ok (es,241) ∧
    bodyValues shifted 11 ps es 32 = .ok SiblingControls.vs := by
  apply window ps qs SiblingControls.vs hi shifted hp lead SiblingControls.post 32 160 17 11
  · decide +kernel
  · decide +kernel
  · rfl
  · decide +kernel
  · rw [shifted_size]; decide +kernel
  · decide +kernel
  · decide +kernel

theorem shifted_decoder : mmembers shifted 11 (ps.map Param.shape) 4 32 17 = .ok (SiblingControls.vs,305) := by
  apply members_window ps qs SiblingControls.vs hi shifted hp lead SiblingControls.post 32 160 17 11
  · decide +kernel
  · decide +kernel
  · rfl
  · decide +kernel
  · rw [shifted_size]; decide +kernel
  · decide +kernel
  · decide +kernel

/-- Test-only projection of actual typed entered references, no decoder. -/
def refs : {ps : List Param} → Entries ps → List (Option (Nat × Nat))
  | _, .nil => []
  | _, .cons (.val _) es => none :: refs es
  | _, .cons (.ref addr len) es => some (addr,len) :: refs es

def observedRefs (I : Input) (pos : Nat := 0) := (enter I 11 ps pos 17).toOption.map (fun r => refs r.1)
def bounded (ws : Vals (qs.map Param.shape)) : Input := {sample ws with free := lim-288}
def wrongBase : Input := RecursiveControls.altered (sample hi) 4 100
def badOffset : Input := RecursiveControls.altered (sample hi) 4 (lim+1)
def shortHead : Input := {(sample hi) with data := (sample hi).data.take 20}
def wrongQs : List Param := [{shape := .fixed RecursiveControls.U 2,loc := .memory}]
def wrongValues : Vals (wrongQs.map Param.shape) := .cons (.fixed RecursiveControls.pair) .nil
def wrongExtent : Input := input (ps ++ wrongQs)
  (BodyComposition.appendValues ps wrongQs SiblingControls.vs wrongValues) SiblingControls.sel SiblingControls.post 128

theorem wrong_extent_head : load (sample lo).data 4 = 96 ∧ load wrongExtent.data 4 = 128 := by decide +kernel

theorem prefix_before_tail : ∃ es, entry (bounded hi) 11 ps = .ok es ∧
    bodyValues (bounded hi) 11 ps es 0 = .ok SiblingControls.vs := by
  apply prefix_entry ps qs SiblingControls.vs hi SiblingControls.sel SiblingControls.post (lim-288) 11
  · decide +kernel
  · decide +kernel
  · change (sample hi).size ≤ lim
    rw [sizes.2]; decide +kernel
  · decide +kernel
  · decide +kernel

theorem failure_priority : DynamicListControls.err (entry shortHead 0 ps) = 1 ∧
    DynamicListControls.err (enter (sample lo) 0 ps 0 17) = 3 := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.SiblingWindowControls.shifted_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingWindowControls.shifted_size
/-- info: 'Solidity.Backend.AbiWorld.SiblingWindowControls.shifted_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingWindowControls.shifted_typed
/-- info: 'Solidity.Backend.AbiWorld.SiblingWindowControls.shifted_decoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingWindowControls.shifted_decoder
/-- info: 'Solidity.Backend.AbiWorld.SiblingWindowControls.wrong_extent_head' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingWindowControls.wrong_extent_head
/-- info: 'Solidity.Backend.AbiWorld.SiblingWindowControls.prefix_before_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingWindowControls.prefix_before_tail
/-- info: 'Solidity.Backend.AbiWorld.SiblingWindowControls.failure_priority' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingWindowControls.failure_priority
end Solidity.Backend.AbiWorld.SiblingWindowControls
