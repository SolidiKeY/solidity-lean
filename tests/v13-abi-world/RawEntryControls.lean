import Solidity.Backend.AbiWorld.RawEntryTransport
import tests.«v13-abi-world».SiblingWindowControls
import tests.«v13-abi-world».SiblingArrayControls
namespace Solidity.Backend.AbiWorld.RawEntryControls
open AbiEntry RecursiveEntry

/-- Arbitrary earlier byte values, arbitrary later array values, actual
indexed codec inputs and only original sufficient guards: no raw-result premise. -/
theorem generic (bs cs : List UInt8) (us zs : List (List UInt8)) (free a f : Nat)
    (sizeI : (input (SiblingControls.ps ++ SiblingControls.qs)
      (BodyComposition.appendValues SiblingControls.ps SiblingControls.qs
        (.cons (RecursiveControls.row bs) (.cons (.bytes cs) .nil)) (SiblingControls.later us))
      SiblingControls.sel SiblingControls.post free).size ≤ lim)
    (sizeJ : (input (SiblingControls.ps ++ SiblingControls.qs)
      (BodyComposition.appendValues SiblingControls.ps SiblingControls.qs
        (.cons (RecursiveControls.row bs) (.cons (.bytes cs) .nil)) (SiblingControls.later zs))
      SiblingControls.sel SiblingControls.post free).size ≤ lim)
    (room : free + (a + LocationPeak.peak SiblingControls.ps (.cons (RecursiveControls.row bs) (.cons (.bytes cs) .nil))) ≤ lim)
    (fuel : parameterNeed (.cons (RecursiveControls.row bs) (.cons (.bytes cs) .nil)) ≤ f) :
    enter (input (SiblingControls.ps ++ SiblingControls.qs)
      (BodyComposition.appendValues SiblingControls.ps SiblingControls.qs
        (.cons (RecursiveControls.row bs) (.cons (.bytes cs) .nil)) (SiblingControls.later us))
      SiblingControls.sel SiblingControls.post free) f SiblingControls.ps 0 a =
    enter (input (SiblingControls.ps ++ SiblingControls.qs)
      (BodyComposition.appendValues SiblingControls.ps SiblingControls.qs
        (.cons (RecursiveControls.row bs) (.cons (.bytes cs) .nil)) (SiblingControls.later zs))
      SiblingControls.sel SiblingControls.post free) f SiblingControls.ps 0 a := by
  exact RawEntryTransport.enter_equal _ _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) sizeI sizeJ room fuel

theorem raw_tuple : ∃ es,
    enter (SiblingControls.sample SiblingControls.lo) 11 SiblingControls.ps 0 17 = .ok (es,241) ∧
    enter (SiblingControls.sample SiblingControls.hi) 11 SiblingControls.ps 0 17 = .ok (es,241) ∧
    bodyValues (SiblingControls.sample SiblingControls.lo) 11 SiblingControls.ps es 0 = .ok SiblingControls.vs ∧
    bodyValues (SiblingControls.sample SiblingControls.hi) 11 SiblingControls.ps es 0 = .ok SiblingControls.vs := by
  apply RawEntryTransport.noninterference SiblingControls.ps SiblingControls.qs SiblingControls.vs
    SiblingControls.lo SiblingControls.hi SiblingControls.sel SiblingControls.post 128 17 11
  · decide +kernel
  · decide +kernel
  · change (SiblingControls.sample SiblingControls.lo).size ≤ lim
    rw [SiblingControls.sizes.1]; decide +kernel
  · change (SiblingControls.sample SiblingControls.hi).size ≤ lim
    rw [SiblingControls.sizes.2]; decide +kernel
  · decide +kernel
  · decide +kernel

def shiftedLo : Input := ⟨SiblingWindowControls.hp ++
  (AbiEntry.assemble.go (Vals.parts SiblingControls.vs ++ Vals.parts SiblingControls.lo) 160).1 ++ SiblingWindowControls.lead ++
  (AbiEntry.assemble.go (Vals.parts SiblingControls.vs ++ Vals.parts SiblingControls.lo) 160).2 ++ SiblingControls.post,128⟩

theorem shifted_size : shiftedLo.size = 486 := by
  rw [SiblingReadback.window_size SiblingControls.ps SiblingControls.qs SiblingControls.vs SiblingControls.lo shiftedLo
    SiblingWindowControls.hp SiblingWindowControls.lead SiblingControls.post 160 rfl,
    SiblingControls.prefix_tail_length,show SiblingControls.lo = SiblingControls.later [] from rfl,SiblingControls.later_tail_length]
  simp only [SiblingWindowControls.hp,SiblingWindowControls.lead,SiblingControls.sel,SiblingControls.post,List.length_append,
    MixedPacket.word_length,ByteSequenceReadback.array_length,ByteSequenceControls.tail_sequence,
    SiblingControls.measurements.1,SiblingControls.measurements.2.1,List.length_cons,List.length_nil,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_replicate]
  decide +kernel

theorem raw_shifted : ∃ es, enter shiftedLo 11 SiblingControls.ps 32 17 = .ok (es,241) ∧
    enter SiblingWindowControls.shifted 11 SiblingControls.ps 32 17 = .ok (es,241) ∧
    bodyValues shiftedLo 11 SiblingControls.ps es 32 = .ok SiblingControls.vs ∧
    bodyValues SiblingWindowControls.shifted 11 SiblingControls.ps es 32 = .ok SiblingControls.vs := by
  apply RawEntryTransport.sibling_window SiblingControls.ps SiblingControls.qs SiblingControls.vs
    SiblingControls.lo SiblingControls.hi shiftedLo SiblingWindowControls.shifted SiblingWindowControls.hp SiblingWindowControls.lead
    SiblingControls.post 32 160 17 11
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
  · decide +kernel
  · rw [shifted_size]; decide +kernel
  · rw [SiblingWindowControls.shifted_size]; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def arrayPs (loc : AbiEntry.Loc) : List Param := [{shape := .array RecursiveControls.Row,loc}]

theorem raw_array (loc : AbiEntry.Loc) :
    enter (input (arrayPs loc ++ SiblingControls.qs)
      (BodyComposition.appendValues (arrayPs loc) SiblingControls.qs SiblingArrayControls.vs SiblingControls.lo)
      SiblingControls.sel SiblingControls.post 128) 14 (arrayPs loc) 0 17 =
    enter (input (arrayPs loc ++ SiblingControls.qs)
      (BodyComposition.appendValues (arrayPs loc) SiblingControls.qs SiblingArrayControls.vs SiblingControls.hi)
      SiblingControls.sel SiblingControls.post 128) 14 (arrayPs loc) 0 17 := by
  apply RawEntryTransport.enter_equal (arrayPs loc) SiblingControls.qs SiblingArrayControls.vs
    SiblingControls.lo SiblingControls.hi SiblingControls.sel SiblingControls.post 128 17 14
  · decide +kernel
  · decide +kernel
  · change (SiblingArrayControls.sample SiblingControls.lo).size ≤ lim
    rw [SiblingArrayControls.sizes.1]; decide +kernel
  · change (SiblingArrayControls.sample SiblingControls.hi).size ≤ lim
    rw [SiblingArrayControls.sizes.2]; decide +kernel
  · cases loc <;> decide +kernel
  · cases loc <;> decide +kernel

/-- Actual compact entry has two real calldata references. Corrupt address
and length claims fail through cref itself, not a typed-value replacement. -/
def refPs : List Param := [{shape := .bytes,loc := .calldata},{shape := .bytes,loc := .calldata}]
def refVals : Vals (refPs.map Param.shape) := .cons (.bytes [0,255]) (.cons (.bytes []) .nil)
def refInput := input refPs refVals [9,0,0,1] (List.replicate 32 0) 128

theorem ref_data : refInput.data = [9,0,0,1] ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 128 ++
    AbiEntry.Val.enc (.bytes [0,255]) ++ AbiEntry.Val.enc (.bytes []) ++ List.replicate 32 0 := by
  change [9,0,0,1] ++ encodeArgs (.cons (.bytes [0,255]) (.cons (.bytes []) .nil)) ++ List.replicate 32 0 = _
  rw [EntryComposition.encoded_dynamic_pair _ _ rfl rfl]
  have len : (AbiEntry.Val.enc (.bytes [0,255])).length = 64 := by decide +kernel
  rw [len]
  simp only [List.append_assoc]

theorem ref_size : refInput.size = 196 := by
  rw [Input.size,ref_data]
  simp only [List.length_append,MixedPacket.word_length,BytesArrayReadback.byte_payload_length,List.length_cons,List.length_nil,List.length_replicate]
  decide +kernel

theorem load_field (pre post : List UInt8) (n p : Nat) (hn : n < W)
    (data : refInput.data = pre ++ AbiEntry.wordBytes n ++ post) (position : pre.length = p) :
    load refInput.data p = n := by
  have h := CanonicalReadback.load_word pre post n hn
  rw [position,← data] at h
  exact h

theorem reads : load refInput.data 4 = 64 ∧ load refInput.data 36 = 128 ∧
    load refInput.data 68 = 2 ∧ load refInput.data 132 = 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · apply load_field [9,0,0,1] (AbiEntry.wordBytes 128 ++ AbiEntry.Val.enc (.bytes [0,255]) ++ AbiEntry.Val.enc (.bytes []) ++ List.replicate 32 0) 64 4 (by decide +kernel)
    · rw [ref_data]; simp only [List.append_assoc]
    · rfl
  · apply load_field ([9,0,0,1] ++ AbiEntry.wordBytes 64) (AbiEntry.Val.enc (.bytes [0,255]) ++ AbiEntry.Val.enc (.bytes []) ++ List.replicate 32 0) 128 36 (by decide +kernel)
    · rw [ref_data]; simp only [List.append_assoc]
    · simp only [List.length_append,MixedPacket.word_length]; rfl
  · apply load_field ([9,0,0,1] ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 128)
      ([0,255] ++ List.replicate 30 0 ++ AbiEntry.Val.enc (.bytes []) ++ List.replicate 32 0) 2 68 (by decide +kernel)
    · rw [ref_data]
      change [9,0,0,1] ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 128 ++
        (AbiEntry.wordBytes 2 ++ [0,255] ++ List.replicate 30 0) ++ AbiEntry.Val.enc (.bytes []) ++ List.replicate 32 0 = _
      simp only [List.append_assoc]
    · simp only [List.length_append,MixedPacket.word_length]; rfl
  · apply load_field ([9,0,0,1] ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 128 ++ AbiEntry.Val.enc (.bytes [0,255])) (List.replicate 32 0) 0 132 (by decide +kernel)
    · rw [ref_data]
      change [9,0,0,1] ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 128 ++ AbiEntry.Val.enc (.bytes [0,255]) ++ AbiEntry.wordBytes 0 ++ List.replicate 32 0 = _
      simp only [List.append_assoc]
    · have len : (AbiEntry.Val.enc (.bytes [0,255])).length = 64 := by decide +kernel
      simp only [List.length_append,MixedPacket.word_length,len]; rfl

theorem ref0 : cref refInput .bytes 4 0 = .ok (100,2) := by
  apply ReferenceFields.bytes_run refInput 0 64 2 reads.1 reads.2.2.1 (by decide +kernel) (by decide +kernel)
  · rw [ref_size]; decide +kernel
  · rw [ref_size]; decide +kernel

theorem ref1 : cref refInput .bytes 4 32 = .ok (164,0) := by
  apply ReferenceFields.bytes_run refInput 32 128 0 reads.2.1 reads.2.2.2 (by decide +kernel) (by decide +kernel)
  · rw [ref_size]; decide +kernel
  · rw [ref_size]; decide +kernel

theorem corruption : cref refInput .bytes 4 0 = .ok (100,2) ∧
    cref refInput .bytes 4 32 = .ok (164,0) ∧
    cref refInput .bytes 4 0 ≠ .ok (101,2) ∧ cref refInput .bytes 4 0 ≠ .ok (100,3) := by
  refine ⟨ref0,ref1,?_,?_⟩
  · rw [ref0]
    intro h
    exact (by decide +kernel : (100,2) ≠ (101,2)) (Except.ok.inj h)
  · rw [ref0]
    intro h
    exact (by decide +kernel : (100,2) ≠ (100,3)) (Except.ok.inj h)

theorem actual_refs (f a : Nat) : enter refInput f refPs 0 a =
    .ok (.cons (.ref 100 2) (.cons (.ref 164 0) .nil),a) := by
  simp only [refPs,enter,Shape.headSize,Nat.zero_add,corruption.1,corruption.2.1,bind,Except.bind,pure,Except.pure]

/-- info: 'Solidity.Backend.AbiWorld.ReferenceFields.word_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.ReferenceFields.word_window
/-- info: 'Solidity.Backend.AbiWorld.ReferenceFields.bytes_run' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.ReferenceFields.bytes_run
/-- info: 'Solidity.Backend.AbiWorld.ReferenceFields.fields' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.ReferenceFields.fields
/-- info: 'Solidity.Backend.AbiWorld.ReferenceFields.length_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.ReferenceFields.length_header
/-- info: 'Solidity.Backend.AbiWorld.ReferenceFields.agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.ReferenceFields.agree
/-- info: 'Solidity.Backend.AbiWorld.RawEntryTransport.joint_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryTransport.joint_window
/-- info: 'Solidity.Backend.AbiWorld.RawEntryTransport.sibling_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryTransport.sibling_window
/-- info: 'Solidity.Backend.AbiWorld.RawEntryTransport.canonical_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryTransport.canonical_data
/-- info: 'Solidity.Backend.AbiWorld.RawEntryTransport.noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryTransport.noninterference
/-- info: 'Solidity.Backend.AbiWorld.RawEntryTransport.enter_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryTransport.enter_equal
/-- info: 'Solidity.Backend.AbiWorld.RawEntryTransport.entry_from_run' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryTransport.entry_from_run
/-- info: 'Solidity.Backend.AbiWorld.RawEntryTransport.entry_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryTransport.entry_equal
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.generic
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.raw_tuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.raw_tuple
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.shifted_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.shifted_size
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.raw_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.raw_shifted
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.raw_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.raw_array
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.ref_data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.ref_data
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.ref_size' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.ref_size
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.load_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.load_field
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.reads
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.ref0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.ref0
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.ref1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.ref1
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.corruption' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.corruption
/-- info: 'Solidity.Backend.AbiWorld.RawEntryControls.actual_refs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.RawEntryControls.actual_refs
end Solidity.Backend.AbiWorld.RawEntryControls
