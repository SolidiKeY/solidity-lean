import Solidity.Backend.AbiWorld.CanonicalReadback

/-! Canonical byte-string readback through the EXISTING indexed ABI codec and
actual decoder. Padding/word facts are reused; no new byte loader, allocator,
source admission rule, runtime encoder or native/world correspondence. -/
namespace Solidity.Backend.AbiWorld.BytesReadback
open AbiEntry CanonicalReadback

def values (bs : List UInt8) : Vals [.bytes] := .cons (.bytes bs) .nil

/-- Arbitrary existing byte observations are independent of earlier/later bytes. -/
theorem bytes_prefix (pre bs post : List UInt8) :
    bytesAt (pre ++ bs ++ post) pre.length bs.length = bs := by
  apply List.ext_getElem (by simp only [bytesAt,List.length_map,List.length_range])
  intro i hi hj
  simp only [bytesAt,List.getElem_map,List.getElem_range,byteAt,List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]
  rfl

theorem rounded_formula (n : Nat) : roundUp n = n + (32 - n % 32) % 32 := by
  simp only [roundUp]
  omega

theorem rounded_bounds (n : Nat) : n ≤ roundUp n ∧ roundUp n < n + 32 := by
  rw [rounded_formula]
  have h := Nat.mod_lt (32 - n % 32) (by decide : 0 < 32)
  omega

/-- The old pad32 facts describe EXACTLY the actual ABI roundUp length. -/
theorem padding_length (bs : List UInt8) : (Semantics.pad32 bs).length = roundUp bs.length := by
  rw [padded_length,rounded_formula]

/-- alloc rounds the requested bytes-object size again; it is already aligned. -/
theorem rounded_allocation (n : Nat) : roundUp (roundUp n + 32) = roundUp n + 32 :=
  roundUp_words ((n + 31) / 32)

def allocationBytes (bs : List UInt8) : Nat := roundUp bs.length + 32

theorem encoded (bs : List UInt8) : encodeArgs (values bs) =
    AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes bs.length ++ bs ++
      List.replicate (roundUp bs.length - bs.length) 0 := by
  simp only [values,encodeArgs,Vals.parts,Shape.dynamic,Val.enc,AbiEntry.assemble,List.foldl_cons,List.foldl_nil,
    ite_true,Nat.zero_add,AbiEntry.assemble.go,List.append_nil,List.append_assoc]

theorem encoded_padding (bs : List UInt8) : encodeArgs (values bs) =
    AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes bs.length ++ Semantics.pad32 bs := by
  rw [encoded]
  simp only [Semantics.pad32,rounded_formula,Nat.add_sub_cancel_left,List.append_assoc]

theorem encoded_length (bs : List UInt8) : (encodeArgs (values bs)).length = 64 + roundUp bs.length := by
  rw [encoded_padding]
  simp only [List.length_append,MixedPacket.word_length,padding_length]

theorem exact_payload (bs : List UInt8) : ((encodeArgs (values bs)).drop 64).take bs.length = bs := by
  rw [encoded_padding]
  rw [List.drop_left' (show (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes bs.length).length = 64 by
    simp only [List.length_append,MixedPacket.word_length])]
  exact padded_payload bs

theorem exact_zeros (bs : List UInt8) : (encodeArgs (values bs)).drop (64 + bs.length) =
    List.replicate (roundUp bs.length - bs.length) 0 := by
  rw [encoded]
  apply List.drop_left'
  simp only [List.length_append,MixedPacket.word_length]

/-- Actual bytes mdec with its real rounded allocation BEFORE payload bounds.
Arbitrary suffix permits canonical padding, dirty padding or no padding. -/
theorem mdec_bytes (bs : List UInt8) (I : Input) (pre post : List UInt8) (a f : Nat)
    (data : I.data = pre ++ AbiEntry.wordBytes bs.length ++ bs ++ post)
    (allocation : I.free + (a + allocationBytes bs) ≤ lim) (fuel : 1 ≤ f) :
    mdec I f .bytes pre.length a = .ok (.bytes bs,a + allocationBytes bs) := by
  have rounded := rounded_bounds bs.length
  have lenlim : bs.length ≤ lim := by unfold allocationBytes at allocation; omega
  have lenword : bs.length < AbiEntry.W := by
    have bound : lim < AbiEntry.W := by decide
    omega
  have read : load I.data pre.length = bs.length := by
    rw [data]
    simpa only [List.append_assoc] using load_word pre (bs ++ post) bs.length lenword
  have region : pre.length + 32 + bs.length ≤ I.size := by
    simp only [Input.size,data,List.length_append,MixedPacket.word_length]
    omega
  have payload : bytesAt I.data (pre.length + 32) bs.length = bs := by
    rw [data]
    simpa only [List.length_append,MixedPacket.word_length,List.append_assoc] using
      bytes_prefix (pre ++ AbiEntry.wordBytes bs.length) bs post
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  unfold allocationBytes at allocation
  simp only [mdec,read,if_pos (by omega : pre.length + 31 < I.size),
    if_neg (Nat.not_lt.mpr lenlim),alloc,rounded_allocation,
    if_pos allocation,if_neg (Nat.not_lt.mpr region),payload,allocationBytes]

def input (bs selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (values bs) ++ post,free⟩

def params (loc : AbiEntry.Loc) : List Param := [{shape := .bytes,loc}]

theorem input_size (bs selector post : List UInt8) (free : Nat) :
    (input bs selector post free).size = selector.length + 64 + roundUp bs.length + post.length := by
  simp only [input,Input.size,List.length_append,encoded_length]
  omega

theorem input_reads (bs selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) :
    load (input bs selector post free).data 4 = 32 ∧
    load (input bs selector post free).data 36 = bs.length := by
  have rounded := rounded_bounds bs.length
  have lenword : bs.length < AbiEntry.W := by
    have bound : lim < AbiEntry.W := by decide
    unfold allocationBytes at allocation
    omega
  constructor
  · have h := load_word selector (AbiEntry.wordBytes bs.length ++ bs ++
      List.replicate (roundUp bs.length - bs.length) 0 ++ post) 32 (by decide)
    simpa only [input,encoded,sel,List.append_assoc] using h
  · have h := load_word (selector ++ AbiEntry.wordBytes 32)
      (bs ++ List.replicate (roundUp bs.length - bs.length) 0 ++ post) bs.length lenword
    simpa only [input,encoded,sel,List.append_assoc,List.length_append,MixedPacket.word_length] using h

/-- Byte-string top decoding needs two ORIGINAL decoder steps, independent
of byte length. This is a sufficient fuel lemma, not a changed budget. -/
theorem melem_bytes (bs selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) (fuel : 2 ≤ f) :
    melem (input bs selector post free) f .bytes 4 4 0 = .ok (.bytes bs,allocationBytes bs) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := mdec_bytes bs (input bs selector post free) (selector ++ AbiEntry.wordBytes 32)
    (List.replicate (roundUp bs.length - bs.length) 0 ++ post) 0 g
    (by simp only [input,encoded,List.append_assoc])
    (by simpa only [input,Nat.zero_add] using allocation) (by omega)
  simp only [sel,List.length_append,MixedPacket.word_length,Nat.zero_add] at decoded
  have reads := input_reads bs selector post free sel allocation
  simp only [melem,Shape.dynamic,reads.1,if_neg (by decide : ¬ lim < 32)]
  exact decoded

theorem eager_bytes (bs selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) (fuel : 2 ≤ f) :
    eager (input bs selector post free) f .bytes 0 = .ok (.bytes bs) := by
  simp only [eager,Nat.add_zero,melem_bytes bs selector post free f sel allocation fuel]

/-- Exact actual memory entry and rounded allocation cursor. -/
theorem memory_entry (bs selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) (fuel : 2 ≤ f) :
    enter (input bs selector post free) f (params .memory) 0 0 =
      .ok (.cons (.val (.bytes bs)) .nil,allocationBytes bs) ∧
    entry (input bs selector post free) f (params .memory) = .ok (.cons (.val (.bytes bs)) .nil) := by
  have entered : enter (input bs selector post free) f (params .memory) 0 0 =
      .ok (.cons (.val (.bytes bs)) .nil,allocationBytes bs) := by
    simp only [params,enter,Nat.add_zero,melem_bytes bs selector post free f sel allocation fuel,
      bind,Except.bind,pure,Except.pure]
  refine ⟨entered,?_⟩
  have heads : ¬ (input bs selector post free).size < 4 + headsOf (params .memory) := by
    simp only [headsOf,params,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero,input_size,sel]
    omega
  simp only [entry,if_neg heads,entered]

theorem memory_verdict (bs selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) (fuel : 2 ≤ f) :
    verdict (input bs selector post free) f (params .memory) = .run (values bs) := by
  rw [verdict,(memory_entry bs selector post free f sel allocation fuel).2]
  simp only [params,bodyValues,bind,Except.bind,pure,Except.pure,values]

theorem calldata_reference (bs selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) :
    cref (input bs selector post free) .bytes 4 0 = .ok (68,bs.length) := by
  have reads := input_reads bs selector post free sel allocation
  have rounded := rounded_bounds bs.length
  have lenlim : bs.length ≤ lim := by unfold allocationBytes at allocation; omega
  have header : 36 + 31 < (input bs selector post free).size := by rw [input_size,sel]; omega
  have region : ¬ (input bs selector post free).size < 36 + 32 + bs.length := by rw [input_size,sel]; omega
  simp only [cref,Shape.dynamic,Nat.add_zero,reads.1,if_neg (by decide : ¬ lim < 32),
    if_pos header,reads.2,if_neg (Nat.not_lt.mpr lenlim),Shape.stride,Nat.mul_one,if_neg region,ite_true]

theorem calldata_entry (bs selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) :
    entry (input bs selector post free) f (params .calldata) = .ok (.cons (.ref 68 bs.length) .nil) := by
  apply EntryTransport.single_calldata_entry
  · simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero,input_size,sel]
    omega
  · exact calldata_reference bs selector post free sel allocation

theorem calldata_verdict (bs selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes bs ≤ lim) (fuel : 2 ≤ f) :
    verdict (input bs selector post free) f (params .calldata) = .run (values bs) := by
  rw [verdict,calldata_entry bs selector post free f sel allocation]
  simp only [params,bodyValues,eager_bytes bs selector post free f sel allocation fuel,
    bind,Except.bind,pure,Except.pure,values]

/-- Actual typed bytes entry/body readback, with the real size bound supporting
published eager/lazy agreement. No desired successful decoder is a premise. -/
theorem roundtrip (bs selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input bs selector post free).size ≤ lim)
    (allocation : free + allocationBytes bs ≤ lim) (fuel : 2 ≤ f) :
    verdict (input bs selector post free) f (params .memory) = .run (values bs) ∧
    verdict (input bs selector post free) f (params .calldata) = .run (values bs) ∧
    EntryTransport.bodyObservation (input bs selector post free) f (params .memory) encodeArgs =
      some (encodeArgs (values bs)) ∧
    EntryTransport.bodyObservation (input bs selector post free) f (params .calldata) encodeArgs =
      some (encodeArgs (values bs)) ∧
    cval (input bs selector post free) (f - 1) .bytes 68 bs.length = .ok (.bytes bs) := by
  have hm := memory_verdict bs selector post free f sel allocation fuel
  have hc := calldata_verdict bs selector post free f sel allocation fuel
  have he := eager_bytes bs selector post free f sel allocation fuel
  have lazyValue : cval (input bs selector post free) (f - 1) .bytes 68 bs.length = .ok (.bytes bs) := by
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    obtain ⟨addr,len,ref,read⟩ := eager_cref size he
    rw [calldata_reference bs selector post free sel allocation] at ref
    cases ref
    exact read
  exact ⟨hm,hc,by simp only [EntryTransport.bodyObservation,hm],by simp only [EntryTransport.bodyObservation,hc],lazyValue⟩

/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_size
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.input_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_reads
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.melem_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms melem_bytes
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.eager_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eager_bytes
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.memory_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_entry
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.memory_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_verdict
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.calldata_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_reference
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.calldata_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_entry
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.calldata_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_verdict
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.bytes_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_prefix
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.rounded_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rounded_formula
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.rounded_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rounded_bounds
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.padding_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padding_length
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.rounded_allocation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rounded_allocation
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.encoded_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_padding
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.encoded_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_length
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.exact_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_payload
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.exact_zeros' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms exact_zeros
/-- info: 'Solidity.Backend.AbiWorld.BytesReadback.mdec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_bytes
end Solidity.Backend.AbiWorld.BytesReadback
