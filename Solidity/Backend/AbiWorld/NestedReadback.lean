import Solidity.Backend.AbiWorld.CanonicalReadback

/-! Canonical uint[][] readback through the EXISTING intrinsic codec and
mdec/melem/mseq. Allocation measurements describe the original allocator;
no replacement decoder, allocator, machine or admission predicate. -/
namespace Solidity.Backend.AbiWorld.NestedReadback
open AbiEntry CanonicalReadback
abbrev Rows := List (List UInt)

/-- The sum of actual inner payload lengths; each is the existing array's
rounded allocation size. This measures bytes, it does not allocate. -/
def innerBytes (rows : Rows) : Nat := (NestedUintPacket.payloads rows).flatten.length

theorem inner_nil : innerBytes [] = 0 := rfl

theorem inner_cons (xs : List UInt) (rows : Rows) :
    innerBytes (xs :: rows) = xs.length * 32 + 32 + innerBytes rows := by
  simp only [innerBytes,NestedUintPacket.payloads,List.map_cons,List.flatten_cons,List.length_append,
    ArrayPairPacket.payload_length]
  omega

theorem inner_formula (rows : Rows) : innerBytes rows = 32 * rows.length + 32 * rows.flatten.length :=
  NestedUintPacket.payload_total_length rows

/-- Lift an actual full-word slice through arbitrary earlier/later bytes. -/
theorem load_window (pre data post : List UInt8) (p n : Nat)
    (slice : (data.drop p).take 32 = AbiEntry.wordBytes n) (range : n < AbiEntry.W) :
    load (pre ++ data ++ post) (pre.length + p) = n := by
  have enough : p + 32 ≤ data.length := by
    have h := congrArg List.length slice
    simp only [List.length_take,List.length_drop,MixedPacket.word_length] at h
    omega
  have prelen : (data.take p).length = p := by simp only [List.length_take]; omega
  have split : data = data.take p ++ (AbiEntry.wordBytes n ++ (data.drop p).drop 32) := by
    rw [← slice,List.take_append_drop,List.take_append_drop]
  rw [split]
  simpa only [List.length_append,prelen,List.append_assoc] using
    load_word (pre ++ data.take p) ((data.drop p).drop 32 ++ post) n range

/-- Every head offset is bounded by the actual encoded input, not len<W. -/
theorem offset_bound (pre : Rows) (xs : List UInt) (post : Rows)
    (I : Input) (before after : List UInt8)
    (data : I.data = before ++ encodeArgs (NestedUintPacket.values (pre ++ xs :: post)) ++ after)
    (size : I.size ≤ lim) : NestedUintPacket.innerOffset pre post ≤ lim := by
  simp only [Input.size,data,List.length_append,NestedUintPacket.encoded_length,
    List.length_append,List.length_cons,List.flatten_append,List.flatten_cons] at size
  rw [NestedUintPacket.offset_formula]
  omega

theorem head_read (pre : Rows) (xs : List UInt) (post : Rows)
    (I : Input) (before after : List UInt8)
    (data : I.data = before ++ encodeArgs (NestedUintPacket.values (pre ++ xs :: post)) ++ after)
    (size : I.size ≤ lim) :
    load I.data (before.length + 64 + 32 * pre.length) = NestedUintPacket.innerOffset pre post := by
  have off := offset_bound pre xs post I before after data size
  have range : NestedUintPacket.innerOffset pre post < AbiEntry.W := by
    have bound : lim < AbiEntry.W := by decide
    omega
  rw [data]
  simpa only [Nat.add_assoc] using load_window before _ after _ _
    (NestedUintPacket.inner_head pre xs post) range

/-- The actual selected inner allocation, embedded in the same complete input. -/
theorem inner_decode (pre : Rows) (xs : List UInt) (post : Rows)
    (I : Input) (before after : List UInt8) (a f : Nat)
    (data : I.data = before ++ encodeArgs (NestedUintPacket.values (pre ++ xs :: post)) ++ after)
    (allocation : I.free + (a + (xs.length * 32 + 32)) ≤ lim)
    (fuel : xs.length + 3 ≤ f) :
    mdec I f WordArrayPacket.Shape (before.length + 64 + NestedUintPacket.innerOffset pre post) a =
      .ok (.array (WordArrayPacket.sequence xs),a + (xs.length * 32 + 32)) := by
  have tail := CanonicalReadback.nested_tail pre xs post
  have extent : 64 + NestedUintPacket.innerOffset pre post ≤
      (encodeArgs (NestedUintPacket.values (pre ++ xs :: post))).length := by
    have h := congrArg List.length tail
    simp only [List.length_drop,List.length_append,MixedPacket.word_length,words_length] at h
    omega
  have embedded : I.data.drop (before.length + 64 + NestedUintPacket.innerOffset pre post) =
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++
        ((NestedUintPacket.payloads post).flatten ++ after) := by
    rw [data,List.append_assoc,Nat.add_assoc,← List.drop_drop,List.drop_left,
      List.drop_append_of_le_length extent,tail]
    simp only [List.append_assoc]
  apply mdec_tail xs I _ a f ((NestedUintPacket.payloads post).flatten ++ after)
    embedded _ allocation fuel
  simp only [Input.size,data,List.length_append]
  omega

/-- Actual dynamic melem selects the just-proved inner decoder at the real
post-length base, with the original fuel decrement and cursor. -/
theorem element (pre : Rows) (xs : List UInt) (post : Rows)
    (I : Input) (before after : List UInt8) (a f : Nat)
    (data : I.data = before ++ encodeArgs (NestedUintPacket.values (pre ++ xs :: post)) ++ after)
    (size : I.size ≤ lim) (allocation : I.free + (a + (xs.length * 32 + 32)) ≤ lim)
    (fuel : xs.length + 3 ≤ f) :
    melem I (f + 1) WordArrayPacket.Shape (before.length + 64)
      (before.length + 64 + pre.length * 32) a =
      .ok (.array (WordArrayPacket.sequence xs),a + (xs.length * 32 + 32)) := by
  have read := head_read pre xs post I before after data size
  have off := offset_bound pre xs post I before after data size
  have decoded := inner_decode pre xs post I before after a f data allocation fuel
  simp only [Nat.mul_comm 32] at read
  simp only [WordArrayPacket.Shape,melem,Shape.dynamic,read,if_neg (Nat.not_lt.mpr off)]
  exact decoded

/-- The actual outer mseq, starting after the processed prefix's heads.
Each recursive step advances BOTH the real head index and allocation cursor.
No successful element/sequence result is a premise. -/
theorem outer_sequence (rest : Rows) (pre : Rows) (I : Input) (before after : List UInt8) (a f : Nat)
    (data : I.data = before ++ encodeArgs (NestedUintPacket.values (pre ++ rest)) ++ after)
    (size : I.size ≤ lim) (allocation : I.free + (a + innerBytes rest) ≤ lim)
    (fuel : rest.length + rest.flatten.length + 4 ≤ f) :
    mseq I f WordArrayPacket.Shape (before.length + 64) pre.length rest.length a =
      .ok (NestedUintPacket.sequence rest,a + innerBytes rest) := by
  induction rest generalizing pre a f with
  | nil => cases f <;> simp only [List.length_nil,mseq,NestedUintPacket.sequence,inner_nil,Nat.add_zero]
  | cons xs rest ih =>
    simp only [List.length_cons,List.flatten_cons,List.length_append] at fuel
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
    have allocHead : I.free + (a + (xs.length * 32 + 32)) ≤ lim := by
      rw [inner_cons] at allocation
      omega
    have step := element pre xs rest I before after a k data size allocHead (by omega)
    have tail := ih (pre ++ [xs]) (a + (xs.length * 32 + 32)) (k + 1)
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using data)
      (by rw [inner_cons] at allocation; omega) (by omega)
    simp only [List.length_append,List.length_singleton] at tail
    simp only [List.length_cons,mseq,WordArrayPacket.Shape,Shape.headSize,step,tail,NestedUintPacket.sequence]
    simp only [inner_cons,Nat.add_assoc]

/-- Exact outer head allocation followed by every actual inner allocation. -/
def allocationBytes (rows : Rows) : Nat := rows.length * 32 + 32 + innerBytes rows

theorem allocation_formula (rows : Rows) :
    allocationBytes rows = 32 + 64 * rows.length + 32 * rows.flatten.length := by
  rw [allocationBytes,inner_formula]
  omega

theorem encoded_allocation (rows : Rows) :
    (encodeArgs (NestedUintPacket.values rows)).length = 32 + allocationBytes rows := by
  rw [NestedUintPacket.encoded_length,allocation_formula]
  omega

/-- Generic actual outer mdec: the full indexed nested value and sequential
allocation cursor. The global bound entails each original alloc check. -/
theorem outer_decode (rows : Rows) (I : Input) (before after : List UInt8) (a f : Nat)
    (data : I.data = before ++ encodeArgs (NestedUintPacket.values rows) ++ after)
    (size : I.size ≤ lim) (allocation : I.free + (a + allocationBytes rows) ≤ lim)
    (fuel : rows.length + rows.flatten.length + 5 ≤ f) :
    mdec I f NestedUintPacket.Shape (before.length + 32) a =
      .ok (NestedUintPacket.value rows,a + allocationBytes rows) := by
  have allocOuter : I.free + (a + (rows.length * 32 + 32)) ≤ lim := by
    unfold allocationBytes at allocation
    omega
  have lenlim : rows.length ≤ lim := by omega
  have lenword : rows.length < AbiEntry.W := by
    have bound : lim < AbiEntry.W := by decide
    omega
  have read : load I.data (before.length + 32) = rows.length := by
    rw [data]
    exact load_window before _ after 32 rows.length (NestedUintPacket.outer_header rows).2 lenword
  have region : before.length + 32 + 32 + rows.length * 32 ≤ I.size := by
    simp only [Input.size,data,List.length_append,NestedUintPacket.encoded_length]
    omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := outer_sequence rows [] I before after (a + (rows.length * 32 + 32)) g
    (by simpa only [List.nil_append] using data) size
    (by unfold allocationBytes at allocation; omega) (by omega)
  simp only [List.length_nil] at decoded
  have addr : before.length + 32 + 32 = before.length + 64 := by omega
  simp only [NestedUintPacket.Shape,mdec,read,if_pos (by omega : before.length + 32 + 31 < I.size),
    if_neg (Nat.not_lt.mpr lenlim),alloc,roundUp_words,if_pos allocOuter,Shape.headSize,
    if_neg (Nat.not_lt.mpr region)]
  unfold mdec.match_3
  rw [read,addr,decoded]
  simp only [NestedUintPacket.value,allocationBytes,Nat.add_assoc]

/-- Existing canonical tuple bytes with actual selector and trailing data.
This auxiliary input is not a new source admission rule. -/
def input (rows : Rows) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (NestedUintPacket.values rows) ++ post,free⟩

def params (loc : AbiEntry.Loc) : List Param := [{shape := NestedUintPacket.Shape,loc}]

theorem input_size (rows : Rows) (selector post : List UInt8) (free : Nat) :
    (input rows selector post free).size = selector.length + 32 + allocationBytes rows + post.length := by
  simp only [input,Input.size,List.length_append,encoded_allocation]
  omega

theorem input_reads (rows : Rows) (selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes rows ≤ lim) :
    load (input rows selector post free).data 4 = 32 ∧
    load (input rows selector post free).data 36 = rows.length := by
  have lenword : rows.length < AbiEntry.W := by
    have bound : lim < AbiEntry.W := by decide
    unfold allocationBytes at allocation
    omega
  constructor
  · have h := load_window selector _ post 0 32 (NestedUintPacket.outer_header rows).1 (by decide)
    simpa only [input,sel,Nat.add_zero,List.drop_zero] using h
  · have h := load_window selector _ post 32 rows.length (NestedUintPacket.outer_header rows).2 lenword
    simpa only [input,sel] using h

/-- Top-level actual dynamic element with full nested indexed value/cursor. -/
theorem melem_nested (rows : Rows) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input rows selector post free).size ≤ lim)
    (allocation : free + allocationBytes rows ≤ lim)
    (fuel : rows.length + rows.flatten.length + 6 ≤ f) :
    melem (input rows selector post free) f NestedUintPacket.Shape 4 4 0 =
      .ok (NestedUintPacket.value rows,allocationBytes rows) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := outer_decode rows (input rows selector post free) selector post 0 g rfl size
    (by simpa only [input,Nat.zero_add] using allocation) (by omega)
  simp only [sel,Nat.zero_add] at decoded
  have reads := input_reads rows selector post free sel allocation
  simp only [NestedUintPacket.Shape,melem,Shape.dynamic,reads.1,
    if_neg (by decide : ¬ lim < 32)]
  exact decoded

theorem eager_nested (rows : Rows) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input rows selector post free).size ≤ lim)
    (allocation : free + allocationBytes rows ≤ lim)
    (fuel : rows.length + rows.flatten.length + 6 ≤ f) :
    eager (input rows selector post free) f NestedUintPacket.Shape 0 = .ok (NestedUintPacket.value rows) := by
  simp only [eager,Nat.add_zero,melem_nested rows selector post free f sel size allocation fuel]

/-- Actual memory enter records all sequential allocations exactly once. -/
theorem memory_entry (rows : Rows) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input rows selector post free).size ≤ lim)
    (allocation : free + allocationBytes rows ≤ lim)
    (fuel : rows.length + rows.flatten.length + 6 ≤ f) :
    enter (input rows selector post free) f (params .memory) 0 0 =
      .ok (.cons (.val (NestedUintPacket.value rows)) .nil,allocationBytes rows) ∧
    entry (input rows selector post free) f (params .memory) =
      .ok (.cons (.val (NestedUintPacket.value rows)) .nil) := by
  have entered : enter (input rows selector post free) f (params .memory) 0 0 =
      .ok (.cons (.val (NestedUintPacket.value rows)) .nil,allocationBytes rows) := by
    simp only [params,enter,Nat.add_zero,melem_nested rows selector post free f sel size allocation fuel,
      bind,Except.bind,pure,Except.pure]
  refine ⟨entered,?_⟩
  have heads : ¬ (input rows selector post free).size < 4 + headsOf (params .memory) := by
    simp only [headsOf,params,List.map_cons,List.map_nil,Shape.headsSize,NestedUintPacket.Shape,
      Shape.headSize,Nat.add_zero,input_size,sel,allocation_formula]
    omega
  simp only [entry,if_neg heads,entered]

theorem memory_verdict (rows : Rows) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input rows selector post free).size ≤ lim)
    (allocation : free + allocationBytes rows ≤ lim)
    (fuel : rows.length + rows.flatten.length + 6 ≤ f) :
    verdict (input rows selector post free) f (params .memory) = .run (NestedUintPacket.values rows) := by
  rw [verdict,(memory_entry rows selector post free f sel size allocation fuel).2]
  simp only [params,bodyValues,bind,Except.bind,pure,Except.pure,NestedUintPacket.values,NestedUintPacket.value]

/-- Calldata entry still installs the actual outer reference. Allocator bounds
are sufficient for this canonical eager/body route, not necessary for all calldata. -/
theorem calldata_reference (rows : Rows) (selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes rows ≤ lim) :
    cref (input rows selector post free) NestedUintPacket.Shape 4 0 = .ok (68,rows.length) := by
  have reads := input_reads rows selector post free sel allocation
  have lenlim : rows.length ≤ lim := by unfold allocationBytes at allocation; omega
  have header : 36 + 31 < (input rows selector post free).size := by
    rw [input_size,sel,allocation_formula]; omega
  have region : ¬ (input rows selector post free).size < 36 + 32 + rows.length * 32 := by
    rw [input_size,sel,allocation_formula]; omega
  simp only [cref,Shape.dynamic,Nat.add_zero,reads.1,
    if_neg (by decide : ¬ lim < 32),if_pos header,reads.2,if_neg (Nat.not_lt.mpr lenlim),
    Shape.stride,Shape.headSize,if_neg region,ite_true]

theorem calldata_entry (rows : Rows) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + allocationBytes rows ≤ lim) :
    entry (input rows selector post free) f (params .calldata) = .ok (.cons (.ref 68 rows.length) .nil) := by
  apply EntryTransport.single_calldata_entry
  · simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,NestedUintPacket.Shape,
      Shape.headSize,Nat.add_zero,input_size,sel,allocation_formula]
    omega
  · exact calldata_reference rows selector post free sel allocation

theorem calldata_verdict (rows : Rows) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input rows selector post free).size ≤ lim)
    (allocation : free + allocationBytes rows ≤ lim)
    (fuel : rows.length + rows.flatten.length + 6 ≤ f) :
    verdict (input rows selector post free) f (params .calldata) = .run (NestedUintPacket.values rows) := by
  rw [verdict,calldata_entry rows selector post free f sel allocation]
  simp only [params,bodyValues,eager_nested rows selector post free f sel size allocation fuel,
    bind,Except.bind,pure,Except.pure,NestedUintPacket.values,NestedUintPacket.value]

/-- Canonical nested roundtrip with exact actual typed identity and lazy read;
all original size/allocator/fuel conditions remain explicit auxiliary bounds. -/
theorem roundtrip (rows : Rows) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input rows selector post free).size ≤ lim)
    (allocation : free + allocationBytes rows ≤ lim)
    (fuel : rows.length + rows.flatten.length + 6 ≤ f) :
    verdict (input rows selector post free) f (params .memory) = .run (NestedUintPacket.values rows) ∧
    verdict (input rows selector post free) f (params .calldata) = .run (NestedUintPacket.values rows) ∧
    EntryTransport.bodyObservation (input rows selector post free) f (params .memory) encodeArgs =
      some (encodeArgs (NestedUintPacket.values rows)) ∧
    EntryTransport.bodyObservation (input rows selector post free) f (params .calldata) encodeArgs =
      some (encodeArgs (NestedUintPacket.values rows)) ∧
    cval (input rows selector post free) (f - 1) NestedUintPacket.Shape 68 rows.length =
      .ok (NestedUintPacket.value rows) := by
  have hm := memory_verdict rows selector post free f sel size allocation fuel
  have hc := calldata_verdict rows selector post free f sel size allocation fuel
  have eagerValue := eager_nested rows selector post free f sel size allocation fuel
  have lazyValue : cval (input rows selector post free) (f - 1) NestedUintPacket.Shape 68 rows.length =
      .ok (NestedUintPacket.value rows) := by
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    obtain ⟨addr,len,ref,read⟩ := eager_cref size eagerValue
    rw [calldata_reference rows selector post free sel allocation] at ref
    cases ref
    exact read
  exact ⟨hm,hc,by simp only [EntryTransport.bodyObservation,hm],
    by simp only [EntryTransport.bodyObservation,hc],lazyValue⟩

/-- The earlier conditional layout theorem is consumed GENERICALLY with a
proved actual canonical verdict, rather than another desired-result premise. -/
theorem canonical_layout (rows : Rows) (selector post : List UInt8) (free f : Nat) (lazy : Bool)
    (sel : selector.length = 4) (size : (input rows selector post free).size ≤ lim)
    (allocation : free + allocationBytes rows ≤ lim)
    (fuel : rows.length + rows.flatten.length + 6 ≤ f) :
    ∃ es, entry (input rows selector post free) f (params (if lazy then .calldata else .memory)) = .ok es ∧
      bodyValues (input rows selector post free) f (params (if lazy then .calldata else .memory)) es 0 =
        .ok (NestedUintPacket.values rows) ∧
      EntryTransport.bodyObservation (input rows selector post free) f
        (params (if lazy then .calldata else .memory)) encodeArgs =
          some (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes rows.length ++
            (List.range rows.length).flatMap (fun i => AbiEntry.wordBytes
              (32 * rows.length + ((NestedUintPacket.payloads rows).take i).flatten.length)) ++
            (NestedUintPacket.payloads rows).flatten) := by
  apply NestedUintPacket.accepted_layout
  cases lazy with
  | false => exact memory_verdict rows selector post free f sel size allocation fuel
  | true => exact calldata_verdict rows selector post free f sel size allocation fuel

/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.canonical_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_layout
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_size
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.input_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_reads
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.melem_nested' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms melem_nested
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.eager_nested' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eager_nested
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.memory_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_entry
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.memory_verdict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memory_verdict
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.calldata_reference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_reference
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.calldata_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_entry
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.calldata_verdict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_verdict
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.outer_sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outer_sequence
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.allocation_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_formula
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.encoded_allocation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_allocation
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.outer_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outer_decode
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.inner_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inner_cons
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.inner_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inner_formula
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.load_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_window
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.offset_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms offset_bound
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.head_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_read
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.inner_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inner_decode
/-- info: 'Solidity.Backend.AbiWorld.NestedReadback.element' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms element
end Solidity.Backend.AbiWorld.NestedReadback
