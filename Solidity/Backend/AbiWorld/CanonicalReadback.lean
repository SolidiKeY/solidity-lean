import Solidity.Backend.AbiWorld.NestedUintPacket
import Solidity.Backend.AbiWorld.ErrorRoundtrip

/-! Scoped canonical readback through the EXISTING intrinsic byte loader and
ABI decoder. No replacement loader/codec, admission predicate, runtime encoder,
source/native agreement or profile restriction. -/
namespace Solidity.Backend.AbiWorld.CanonicalReadback
open AbiEntry
abbrev UInt := PrimTy.uint.Denote

theorem word_codec (n : Nat) : AbiEntry.wordBytes n = Semantics.wordBytes n := by
  unfold AbiEntry.wordBytes Semantics.wordBytes
  apply List.map_congr_left
  intro i hi
  exact UInt8.ofNat_mod_size.symm

/-- The actual 32 byte observations ignore arbitrary earlier/later bytes. -/
theorem bytes_word (pre post : List UInt8) (n : Nat) :
    bytesAt (pre ++ AbiEntry.wordBytes n ++ post) pre.length 32 = AbiEntry.wordBytes n := by
  apply List.ext_getElem (by simp only [bytesAt,List.length_map,List.length_range,MixedPacket.word_length])
  intro i hi hj
  have h : i < 32 := by simpa only [MixedPacket.word_length] using hj
  simp only [bytesAt,List.getElem_map,List.getElem_range,byteAt,List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [MixedPacket.word_length] using h),
    List.getElem?_eq_getElem hj]
  rfl

/-- Full unsigned read, not low-byte truncation. W is the original word modulus. -/
theorem load_word (pre post : List UInt8) (n : Nat) (hn : n < AbiEntry.W) :
    load (pre ++ AbiEntry.wordBytes n ++ post) pre.length = n := by
  have hh := bytes_word pre post n
  have fold : load (pre ++ AbiEntry.wordBytes n ++ post) pre.length =
      Semantics.bytesNat (bytesAt (pre ++ AbiEntry.wordBytes n ++ post) pre.length 32) % AbiEntry.W := by
    simp only [load,Semantics.bytesNat,bytesAt,List.foldl_map]
  rw [fold,hh,word_codec,read_word n (by simpa only [AbiEntry.W] using hn),Nat.mod_eq_of_lt hn]

/-- Each canonical element decodes to its ACTUAL indexed full-word value. -/
theorem mdec_uint (I : Input) (v : UInt) (p a f : Nat)
    (read : load I.data p = (WordArrayPacket.uintWord v).val) :
    mdec I (f + 1) (.word (.uint 256)) p a = .ok (.word (WordArrayPacket.uintWord v),a) := by
  simp only [mdec,read,(WordArrayPacket.uintWord v).valid,dite_true]

/-- Sufficient ORIGINAL fuel relation for actual mseq/melem/mdec recursion.
The input bytes, arbitrary prefix/suffix, index and allocation cursor are real. -/
theorem mseq_words (xs : List UInt) (I : Input) (pre post : List UInt8)
    (base i a f : Nat)
    (data : I.data = pre ++ xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post)
    (position : pre.length = base + i * 32) (fuel : xs.length + 2 ≤ f) :
    mseq I f (.word (.uint 256)) base i xs.length a =
      .ok (WordArrayPacket.sequence xs,a) := by
  induction xs generalizing pre i f with
  | nil => cases f <;> rfl
  | cons v xs ih =>
    simp only [List.length_cons] at fuel
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have read : load I.data (base + i * 32) = (WordArrayPacket.uintWord v).val := by
      rw [data,← position,WordArrayPacket.uintWord_value]
      have range : v.val.toNat < AbiEntry.W := by
        rw [← WordArrayPacket.uintWord_value]
        exact (WordArrayPacket.uintWord v).lt
      simpa only [List.flatMap_cons,List.append_assoc] using
        load_word pre (xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post) v.val.toNat range
    have tail := ih (pre ++ AbiEntry.wordBytes v.val.toNat) (i + 1) (j + 1 + 1)
      (by simpa only [List.flatMap_cons,List.append_assoc] using data)
      (by simp only [List.length_append,MixedPacket.word_length]; omega) (by omega)
    simp only [List.length_cons,mseq,melem,Shape.dynamic,Bool.false_eq_true,ite_false,Shape.headSize,
      mdec_uint I v _ a j read,tail,WordArrayPacket.sequence]

/-- Allocation trace is word aligned; no alternative allocator is introduced. -/
theorem roundUp_words (n : Nat) : roundUp (n * 32 + 32) = n * 32 + 32 := by
  simp only [roundUp]
  omega

theorem words_length (xs : List UInt) :
    (xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat)).length = xs.length * 32 := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    simp only [List.flatMap_cons,List.length_append,MixedPacket.word_length,ih,List.length_cons]
    omega

/-- Generic successful ACTUAL eager array decoding, with its exact allocation
trace. The bound is on the original allocator's free+cursor+size, not len<W. -/
theorem mdec_array (xs : List UInt) (I : Input) (pre post : List UInt8) (a f : Nat)
    (data : I.data = pre ++ AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post)
    (allocation : I.free + (a + (xs.length * 32 + 32)) ≤ lim)
    (fuel : xs.length + 3 ≤ f) :
    mdec I f WordArrayPacket.Shape pre.length a =
      .ok (.array (WordArrayPacket.sequence xs),a + (xs.length * 32 + 32)) := by
  have lenlim : xs.length ≤ lim := by omega
  have lenword : xs.length < AbiEntry.W := by
    have bound : lim < AbiEntry.W := by decide
    omega
  have read : load I.data pre.length = xs.length := by
    rw [data]
    simpa only [List.append_assoc] using load_word pre
      (xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post) xs.length lenword
  have region : pre.length + 32 + xs.length * 32 ≤ I.size := by
    simp only [Input.size,data,List.length_append,MixedPacket.word_length,words_length]
    omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := mseq_words xs I (pre ++ AbiEntry.wordBytes xs.length) post
    (pre.length + 32) 0 (a + (xs.length * 32 + 32)) g
    (by simpa only [List.append_assoc] using data)
    (by simp only [List.length_append,MixedPacket.word_length,Nat.zero_mul,Nat.add_zero]) (by omega)
  simp only [WordArrayPacket.Shape,mdec,read,if_pos (by omega : pre.length + 31 < I.size),
    if_neg (Nat.not_lt.mpr lenlim),alloc,roundUp_words,if_pos allocation,
    Shape.headSize,if_neg (Nat.not_lt.mpr region)]
  unfold mdec.match_3
  rw [read,decoded]

/-- A canonical tuple's existing codec bytes after an arbitrary selector,
with arbitrary trailing bytes. This is a test/lemma input, not an admission rule. -/
def input (xs : List UInt) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (WordArrayPacket.values xs) ++ post,free⟩

theorem input_size (xs : List UInt) (selector post : List UInt8) (free : Nat) :
    (input xs selector post free).size = selector.length + 64 + xs.length * 32 + post.length := by
  simp only [input,Input.size,WordArrayPacket.encoded_values,List.length_append,
    MixedPacket.word_length,words_length]
  omega

theorem input_reads (xs : List UInt) (selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim) :
    load (input xs selector post free).data 4 = 32 ∧
    load (input xs selector post free).data 36 = xs.length := by
  have lenword : xs.length < AbiEntry.W := by
    have bound : lim < AbiEntry.W := by decide
    omega
  constructor
  · have h := load_word selector (AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post) 32 (by decide)
    simpa only [input,WordArrayPacket.encoded_values,sel,List.append_assoc] using h
  · have h := load_word (selector ++ AbiEntry.wordBytes 32)
      (xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post) xs.length lenword
    simpa only [input,WordArrayPacket.encoded_values,sel,List.append_assoc,
      List.length_append,MixedPacket.word_length] using h

/-- Top-level dynamic melem retains the exact original allocation cursor. -/
theorem melem_array (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    melem (input xs selector post free) f WordArrayPacket.Shape 4 4 0 =
      .ok (.array (WordArrayPacket.sequence xs),xs.length * 32 + 32) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have reads := input_reads xs selector post free sel allocation
  have decoded := mdec_array xs (input xs selector post free)
    (selector ++ AbiEntry.wordBytes 32) post 0 g
    (by simp only [input,WordArrayPacket.encoded_values,List.append_assoc])
    (by simpa only [input,Nat.zero_add] using allocation) (by omega)
  simp only [List.length_append,MixedPacket.word_length,sel,Nat.zero_add] at decoded
  simp only [WordArrayPacket.Shape,melem,Shape.dynamic,reads.1,
    if_neg (by decide : ¬ lim < 32)]
  exact decoded

theorem eager_array (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    eager (input xs selector post free) f WordArrayPacket.Shape 0 =
      .ok (.array (WordArrayPacket.sequence xs)) := by
  simp only [eager,Nat.add_zero,melem_array xs selector post free f sel allocation fuel]

def params (loc : AbiEntry.Loc) : List Param := [{shape := WordArrayPacket.Shape,loc}]

/-- Actual eager memory entry and cursor, not just equality of encoded bytes. -/
theorem memory_entry (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    enter (input xs selector post free) f (params .memory) 0 0 =
      .ok (.cons (.val (.array (WordArrayPacket.sequence xs))) .nil,xs.length * 32 + 32) ∧
    entry (input xs selector post free) f (params .memory) =
      .ok (.cons (.val (.array (WordArrayPacket.sequence xs))) .nil) := by
  have entered : enter (input xs selector post free) f (params .memory) 0 0 =
      .ok (.cons (.val (.array (WordArrayPacket.sequence xs))) .nil,xs.length * 32 + 32) := by
    simp only [params,enter,Nat.add_zero,melem_array xs selector post free f sel allocation fuel,
      bind,Except.bind,pure,Except.pure]
  refine ⟨entered,?_⟩
  have size : ¬ (input xs selector post free).size < 4 + headsOf (params .memory) := by
    simp only [headsOf,params,List.map_cons,List.map_nil,Shape.headsSize,WordArrayPacket.Shape,
      Shape.headSize,Nat.add_zero,input_size,sel]
    omega
  simp only [entry,if_neg size,entered]

/-- Generic actual memory verdict supplies the canonical indexed typed identity. -/
theorem memory_verdict (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    verdict (input xs selector post free) f (params .memory) = .run (WordArrayPacket.values xs) := by
  rw [verdict,(memory_entry xs selector post free f sel allocation fuel).2]
  simp only [params,bodyValues,bind,Except.bind,pure,Except.pure,WordArrayPacket.values]

theorem calldata_reference (xs : List UInt) (selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim) :
    cref (input xs selector post free) WordArrayPacket.Shape 4 0 = .ok (68,xs.length) := by
  have reads := input_reads xs selector post free sel allocation
  have lenlim : xs.length ≤ lim := by omega
  have header : 36 + 31 < (input xs selector post free).size := by rw [input_size,sel]; omega
  have region : ¬ (input xs selector post free).size < 36 + 32 + xs.length * 32 := by
    rw [input_size,sel]; omega
  simp only [cref,Shape.dynamic,Nat.add_zero,reads.1,
    if_neg (by decide : ¬ lim < 32),if_pos header,reads.2,if_neg (Nat.not_lt.mpr lenlim),
    Shape.stride,Shape.headSize,if_neg region,ite_true]

theorem calldata_entry (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim) :
    entry (input xs selector post free) f (params .calldata) = .ok (.cons (.ref 68 xs.length) .nil) := by
  apply EntryTransport.single_calldata_entry
  · simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,WordArrayPacket.Shape,
      Shape.headSize,Nat.add_zero,input_size,sel]
    omega
  · exact calldata_reference xs selector post free sel allocation

theorem calldata_verdict (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    verdict (input xs selector post free) f (params .calldata) = .run (WordArrayPacket.values xs) := by
  rw [verdict,calldata_entry xs selector post free f sel allocation]
  simp only [params,bodyValues,eager_array xs selector post free f sel allocation fuel,
    bind,Except.bind,pure,Except.pure,WordArrayPacket.values]

/-- Full eager/lazy body readback with actual size/allocator bounds and exact
indexed values. This does not change any noncanonical/lazy-only verdict. -/
theorem roundtrip (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4)
    (size : (input xs selector post free).size ≤ lim)
    (allocation : free + (xs.length * 32 + 32) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    verdict (input xs selector post free) f (params .memory) = .run (WordArrayPacket.values xs) ∧
    verdict (input xs selector post free) f (params .calldata) = .run (WordArrayPacket.values xs) ∧
    EntryTransport.bodyObservation (input xs selector post free) f (params .memory) encodeArgs =
      some (encodeArgs (WordArrayPacket.values xs)) ∧
    EntryTransport.bodyObservation (input xs selector post free) f (params .calldata) encodeArgs =
      some (encodeArgs (WordArrayPacket.values xs)) ∧
    cval (input xs selector post free) (f - 1) WordArrayPacket.Shape 68 xs.length =
      .ok (.array (WordArrayPacket.sequence xs)) := by
  have hm := memory_verdict xs selector post free f sel allocation fuel
  have hc := calldata_verdict xs selector post free f sel allocation fuel
  have eagerValue := eager_array xs selector post free f sel allocation fuel
  have lazyValue : cval (input xs selector post free) (f - 1) WordArrayPacket.Shape 68 xs.length =
      .ok (.array (WordArrayPacket.sequence xs)) := by
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    obtain ⟨addr,len,ref,read⟩ := eager_cref size eagerValue
    rw [calldata_reference xs selector post free sel allocation] at ref
    cases ref
    exact read
  exact ⟨hm,hc,by simp only [EntryTransport.bodyObservation,hm],
    by simp only [EntryTransport.bodyObservation,hc],lazyValue⟩

/-- The exact enter cursor and original bound retain the actual free-pointer
upper-bound behavior; no fresh heap or target byte-memory relation is assumed. -/
theorem allocation_trace (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + (xs.length * 32 + 32) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    enter (input xs selector post free) f (params .memory) 0 0 =
      .ok (.cons (.val (.array (WordArrayPacket.sequence xs))) .nil,xs.length * 32 + 32) ∧
    free + (xs.length * 32 + 32) ≤ lim ∧
    (input xs selector post free).free = free :=
  ⟨(memory_entry xs selector post free f sel allocation fuel).1,allocation,rfl⟩

/-- A proved slice of the actual input is sufficient for its existing load.
This is a loader law, not a new byte reader or assumed ABI correspondence. -/
theorem load_slice (data : List UInt8) (p n : Nat)
    (slice : (data.drop p).take 32 = AbiEntry.wordBytes n) (range : n < AbiEntry.W) :
    load data p = n := by
  have enough : p + 32 ≤ data.length := by
    have h := congrArg List.length slice
    simp only [List.length_take,List.length_drop,MixedPacket.word_length] at h
    omega
  have prelen : (data.take p).length = p := by simp only [List.length_take]; omega
  have split : data = data.take p ++ (AbiEntry.wordBytes n ++ (data.drop p).drop 32) := by
    rw [← slice,List.take_append_drop,List.take_append_drop]
  rw [split]
  simpa only [prelen,List.append_assoc] using load_word (data.take p) ((data.drop p).drop 32) n range

/-- A canonical inner tail can be consumed at its actual byte position. -/
theorem mdec_tail (xs : List UInt) (I : Input) (p a f : Nat) (post : List UInt8)
    (tail : I.data.drop p = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post)
    (position : p ≤ I.size) (allocation : I.free + (a + (xs.length * 32 + 32)) ≤ lim)
    (fuel : xs.length + 3 ≤ f) :
    mdec I f WordArrayPacket.Shape p a =
      .ok (.array (WordArrayPacket.sequence xs),a + (xs.length * 32 + 32)) := by
  have decoded := mdec_array xs I (I.data.take p) post a f
    (by
      calc I.data = I.data.take p ++ I.data.drop p := (List.take_append_drop p I.data).symm
           _ = _ := by rw [tail]; simp only [List.append_assoc]) allocation fuel
  have prelen : (I.data.take p).length = p := by
    simp only [List.length_take,Input.size] at *
    omega
  rw [prelen] at decoded
  exact decoded

/-- Actual generic nested layout reaches the complete selected inner tail. -/
theorem nested_tail (pre : List (List UInt)) (xs : List UInt) (post : List (List UInt)) :
    (encodeArgs (NestedUintPacket.values (pre ++ xs :: post))).drop
      (64 + NestedUintPacket.innerOffset pre post) =
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++
        (NestedUintPacket.payloads post).flatten := by
  have addr : 64 + NestedUintPacket.innerOffset pre post =
      (64 + 32 * (pre ++ xs :: post).length) + (NestedUintPacket.payloads pre).flatten.length := by
    simp only [NestedUintPacket.innerOffset,List.length_append,List.length_cons]
    omega
  rw [addr,← List.drop_drop,NestedUintPacket.after_heads]
  simp only [NestedUintPacket.payloads,List.map_append,List.map_cons,List.flatten_append,List.flatten_cons]
  rw [List.drop_left,ArrayPairPacket.payload,MixedPacket.array_encoding]

/-- A useful nested decoder consequence, not a whole nested entry roundtrip:
consume one arbitrary inner array at the REAL post-length-relative offset. -/
theorem nested_inner (pre : List (List UInt)) (xs : List UInt) (post : List (List UInt))
    (I : Input) (a f : Nat)
    (data : I.data = encodeArgs (NestedUintPacket.values (pre ++ xs :: post)))
    (allocation : I.free + (a + (xs.length * 32 + 32)) ≤ lim)
    (fuel : xs.length + 3 ≤ f) :
    mdec I f WordArrayPacket.Shape (64 + NestedUintPacket.innerOffset pre post) a =
      .ok (.array (WordArrayPacket.sequence xs),a + (xs.length * 32 + 32)) := by
  have tail := nested_tail pre xs post
  rw [← data] at tail
  apply mdec_tail xs I _ a f (NestedUintPacket.payloads post).flatten tail _ allocation fuel
  have sizes := congrArg List.length tail
  simp only [List.length_drop,List.length_append,MixedPacket.word_length,words_length] at sizes
  simp only [Input.size]
  omega

/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.load_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_slice
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.mdec_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_tail
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.nested_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_tail
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.nested_inner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_inner
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.calldata_reference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_reference
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.calldata_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_entry
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.calldata_verdict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_verdict
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.allocation_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_trace
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_size
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.input_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_reads
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.melem_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms melem_array
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.eager_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eager_array
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.memory_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_entry
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.memory_verdict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_verdict
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.words_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms words_length
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.mdec_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_array
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.mdec_uint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_uint
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.mseq_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mseq_words
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.roundUp_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundUp_words
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.word_codec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_codec
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.bytes_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_word
/-- info: 'Solidity.Backend.AbiWorld.CanonicalReadback.load_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_word
end Solidity.Backend.AbiWorld.CanonicalReadback
