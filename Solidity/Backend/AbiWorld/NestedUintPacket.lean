import Solidity.Backend.AbiWorld.ArrayPairPacket

/-! Generic dynamic uint[][] observations through the EXISTING intrinsic codec.
Offsets are natural projections of assemble, relative to the post-length
outer-element head base. No runtime nested-heap representation, decoder,
admission rule, emitted byte encoder or source/native relation is introduced. -/
namespace Solidity.Backend.AbiWorld.NestedUintPacket
abbrev UInt := PrimTy.uint.Denote
abbrev Shape := AbiEntry.Shape.array WordArrayPacket.Shape
abbrev Values := AbiEntry.Vals [Shape]

/-- Outer and inner lengths remain indexed by the existing Seq constructors. -/
def sequence : (xss : List (List UInt)) → AbiEntry.Seq WordArrayPacket.Shape xss.length
  | [] => .nil
  | xs :: xss => .cons (.array (WordArrayPacket.sequence xs)) (sequence xss)
def value (xss : List (List UInt)) : AbiEntry.Val Shape := .array (sequence xss)
def values (xss : List (List UInt)) : Values := .cons (value xss) .nil

/-- Actual inner payloads, each using the published Val.enc codec. -/
def payloads (xss : List (List UInt)) := xss.map ArrayPairPacket.payload

/-- Projection of the REAL assemble recursion, not a replacement head encoder. -/
def dynamicHeads (bs : List (List UInt8)) (off : Nat) : List UInt8 :=
  (AbiEntry.assemble.go (bs.map (true, ·)) off).1

theorem sequence_parts (xss : List (List UInt)) :
    AbiEntry.Seq.parts (sequence xss) = (payloads xss).map (true, ·) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    simp only [sequence,AbiEntry.Seq.parts,AbiEntry.Shape.dynamic,AbiEntry.Val.enc,
      payloads,List.map_cons,ArrayPairPacket.payload,ih]

private theorem dynamic_head_count (bs : List (List UInt8)) (a : Nat) :
    (bs.map (true, ·)).foldl (fun acc (d,b) => acc + if d then 32 else b.length) a =
      a + 32 * bs.length := by
  induction bs generalizing a with
  | nil => simp only [List.map_nil,List.foldl_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
  | cons b bs ih =>
    simp only [List.map_cons,List.foldl_cons,ite_true,List.length_cons]
    rw [ih]
    omega

theorem dynamic_tails (bs : List (List UInt8)) (off : Nat) :
    (AbiEntry.assemble.go (bs.map (true, ·)) off).2 = bs.flatten := by
  induction bs generalizing off with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,AbiEntry.assemble.go,ite_true,ih,List.flatten_cons]

theorem heads_length (bs : List (List UInt8)) (off : Nat) :
    (dynamicHeads bs off).length = 32 * bs.length := by
  induction bs generalizing off with
  | nil => rfl
  | cons b bs ih =>
    change (AbiEntry.wordBytes off ++ dynamicHeads bs (off + b.length)).length = _
    rw [List.length_append,MixedPacket.word_length,ih,List.length_cons]
    omega

theorem heads_append (bs cs : List (List UInt8)) (off : Nat) :
    dynamicHeads (bs ++ cs) off = dynamicHeads bs off ++ dynamicHeads cs (off + bs.flatten.length) := by
  induction bs generalizing off with
  | nil => simp only [List.nil_append,dynamicHeads,List.map_nil,AbiEntry.assemble.go,
      List.flatten_nil,List.length_nil,Nat.add_zero,List.nil_append]
  | cons b bs ih =>
    change AbiEntry.wordBytes off ++ dynamicHeads (bs ++ cs) (off + b.length) =
      (AbiEntry.wordBytes off ++ dynamicHeads bs (off + b.length)) ++
        dynamicHeads cs (off + (b :: bs).flatten.length)
    rw [ih]
    simp only [List.flatten_cons,List.length_append,List.append_assoc,Nat.add_assoc]

/-- Complete head reconstruction with every offset derived from its actual
preceding tail lengths. This has no desired serialization parameter. -/
theorem heads_indexed (bs : List (List UInt8)) (off : Nat) :
    dynamicHeads bs off = (List.range bs.length).flatMap
      (fun i => AbiEntry.wordBytes (off + (bs.take i).flatten.length)) := by
  induction bs generalizing off with
  | nil => rfl
  | cons b bs ih =>
    change AbiEntry.wordBytes off ++ dynamicHeads bs (off + b.length) = _
    rw [ih,List.length_cons,List.range_succ_eq_map]
    simp only [List.flatMap_cons,List.flatMap_map,Function.comp_def,List.take_zero,
      List.flatten_nil,List.length_nil,Nat.add_zero,List.take_succ_cons,List.flatten_cons,
      List.length_append,Nat.add_assoc]

theorem assemble_dynamic (bs : List (List UInt8)) :
    AbiEntry.assemble (bs.map (true, ·)) = dynamicHeads bs (32 * bs.length) ++ bs.flatten := by
  unfold AbiEntry.assemble
  rw [dynamic_head_count,Nat.zero_add]
  have tails := dynamic_tails bs (32 * bs.length)
  unfold dynamicHeads
  cases h : AbiEntry.assemble.go (bs.map (true, ·)) (32 * bs.length) with
  | mk hs ts =>
    rw [h] at tails
    simp only [h,tails]

theorem value_encoding (xss : List (List UInt)) :
    AbiEntry.Val.enc (value xss) = AbiEntry.wordBytes xss.length ++
      AbiEntry.assemble ((payloads xss).map (true, ·)) := by
  change AbiEntry.wordBytes xss.length ++ AbiEntry.assemble (AbiEntry.Seq.parts (sequence xss)) = _
  rw [sequence_parts]

theorem encoded_layout (xss : List (List UInt)) :
    AbiEntry.encodeArgs (values xss) = AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes xss.length ++
      dynamicHeads (payloads xss) (32 * xss.length) ++ (payloads xss).flatten := by
  have top : AbiEntry.encodeArgs (values xss) = AbiEntry.wordBytes 32 ++ AbiEntry.Val.enc (value xss) := by
    simp only [values,AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
      AbiEntry.assemble,List.foldl_cons,List.foldl_nil,ite_true,Nat.zero_add,
      AbiEntry.assemble.go,List.append_nil,List.nil_append]
  rw [top,value_encoding,assemble_dynamic]
  simp only [payloads,List.length_map,List.append_assoc]

/-- Full arbitrary nested packet: top offset, outer length, EVERY relative
inner offset and EVERY complete actual inner payload, in order. -/
theorem encoded_indexed (xss : List (List UInt)) :
    AbiEntry.encodeArgs (values xss) = AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes xss.length ++
      (List.range xss.length).flatMap (fun i =>
        AbiEntry.wordBytes (32 * xss.length + ((payloads xss).take i).flatten.length)) ++
      (payloads xss).flatten := by
  rw [encoded_layout,heads_indexed]
  simp only [payloads,List.length_map]

theorem payload_total_length (xss : List (List UInt)) :
    (payloads xss).flatten.length = 32 * xss.length + 32 * xss.flatten.length := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    change (ArrayPairPacket.payload xs ++ (payloads xss).flatten).length = _
    rw [List.length_append,ArrayPairPacket.payload_length,ih]
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    omega

theorem encoded_length (xss : List (List UInt)) :
    (AbiEntry.encodeArgs (values xss)).length =
      64 + 64 * xss.length + 32 * xss.flatten.length := by
  rw [encoded_layout]
  simp only [List.length_append,MixedPacket.word_length,heads_length,payload_total_length]
  have n : (payloads xss).length = xss.length := List.length_map _
  rw [n]
  omega

theorem prefix_payload_length (xss : List (List UInt)) (i : Nat) :
    ((payloads xss).take i).flatten.length =
      32 * (xss.take i).length + 32 * (xss.take i).flatten.length := by
  change ((xss.map ArrayPairPacket.payload).take i).flatten.length = _
  rw [← List.map_take]
  exact payload_total_length (xss.take i)

theorem payload_words (xss : List (List UInt)) :
    (payloads xss).flatten = xss.flatMap (fun xs =>
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat)) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    change ArrayPairPacket.payload xs ++ (payloads xss).flatten = _
    rw [ArrayPairPacket.payload,MixedPacket.array_encoding,ih,List.flatMap_cons]

/-- Closed complete word formula for arbitrary outer/inner lengths. Every
relative offset is computed from the actual prefix sizes, not supplied by a client. -/
theorem encoded_words (xss : List (List UInt)) :
    AbiEntry.encodeArgs (values xss) = AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes xss.length ++
      (List.range xss.length).flatMap (fun i => AbiEntry.wordBytes
        (32 * xss.length + 32 * (xss.take i).length + 32 * (xss.take i).flatten.length)) ++
      xss.flatMap (fun xs => AbiEntry.wordBytes xs.length ++
        xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat)) := by
  rw [encoded_indexed,payload_words]
  simp only [prefix_payload_length,Nat.add_assoc]

/-- Natural relative offset measured from the element-head base AFTER the
outer length word. No W/lim/fuel/source-admission bound is inferred here. -/
def innerOffset (pre post : List (List UInt)) : Nat :=
  32 * (pre.length + 1 + post.length) + (payloads pre).flatten.length

theorem offset_formula (pre post : List (List UInt)) :
    innerOffset pre post = 32 * (pre.length + 1 + post.length) +
      32 * pre.length + 32 * pre.flatten.length := by
  rw [innerOffset,payload_total_length]
  omega

theorem heads_cons (b : List UInt8) (bs : List (List UInt8)) (off : Nat) :
    dynamicHeads (b :: bs) off = AbiEntry.wordBytes off ++ dynamicHeads bs (off + b.length) := rfl

theorem after_header (xss : List (List UInt)) :
    (AbiEntry.encodeArgs (values xss)).drop 64 =
      dynamicHeads (payloads xss) (32 * xss.length) ++ (payloads xss).flatten := by
  have grouped : AbiEntry.encodeArgs (values xss) =
      (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes xss.length) ++
      (dynamicHeads (payloads xss) (32 * xss.length) ++ (payloads xss).flatten) := by
    simpa only [List.append_assoc] using encoded_layout xss
  rw [grouped,List.drop_left' (by simp only [List.length_append,MixedPacket.word_length] :
    (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes xss.length).length = 64)]

theorem after_heads (xss : List (List UInt)) :
    (AbiEntry.encodeArgs (values xss)).drop (64 + 32 * xss.length) = (payloads xss).flatten := by
  rw [← List.drop_drop (i := 32 * xss.length) (j := 64),after_header]
  exact List.drop_left' (by simpa only [payloads,List.length_map] using (heads_length (payloads xss) (32 * xss.length)))

private theorem head_word (pre : List (List UInt8)) (b : List UInt8)
    (post : List (List UInt8)) (off : Nat) (extra : List UInt8) :
    ((dynamicHeads (pre ++ b :: post) off ++ extra).drop (32 * pre.length)).take 32 =
      AbiEntry.wordBytes (off + pre.flatten.length) := by
  rw [heads_append,heads_cons]
  simp only [List.append_assoc]
  rw [List.drop_left' (heads_length pre off)]
  exact List.take_left' (MixedPacket.word_length _)

/-- Every inner head offset is relative to byte64 in the top-level packet:
the top offset32 PLUS the outer length word32. Not relative to byte32. -/
theorem inner_head (pre : List (List UInt)) (xs : List UInt) (post : List (List UInt)) :
    ((AbiEntry.encodeArgs (values (pre ++ xs :: post))).drop (64 + 32 * pre.length)).take 32 =
      AbiEntry.wordBytes (innerOffset pre post) := by
  rw [← List.drop_drop (i := 32 * pre.length) (j := 64),after_header]
  have head := head_word (payloads pre) (ArrayPairPacket.payload xs) (payloads post)
    (32 * (pre ++ xs :: post).length) (payloads (pre ++ xs :: post)).flatten
  simpa only [payloads,List.map_append,List.map_cons,List.length_map,List.length_append,
    List.length_cons,innerOffset,Nat.add_assoc,Nat.add_comm post.length 1] using head

/-- Every exact inner payload has its own length and ALL ordered full words. -/
theorem inner_payload (pre : List (List UInt)) (xs : List UInt) (post : List (List UInt)) :
    ((AbiEntry.encodeArgs (values (pre ++ xs :: post))).drop (64 + innerOffset pre post)).take
      (32 + 32 * xs.length) =
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) := by
  have addr : 64 + innerOffset pre post =
      (64 + 32 * (pre ++ xs :: post).length) + (payloads pre).flatten.length := by
    simp only [innerOffset,List.length_append,List.length_cons]
    omega
  rw [addr,← List.drop_drop (i := (payloads pre).flatten.length)
    (j := 64 + 32 * (pre ++ xs :: post).length),after_heads]
  simp only [payloads,List.map_append,List.map_cons,List.flatten_append,List.flatten_cons]
  rw [List.drop_left,← ArrayPairPacket.payload_length xs,List.take_left]
  exact MixedPacket.array_encoding xs

/-- Actual codec split around one arbitrary inner member. -/
theorem layout_split (pre : List (List UInt)) (xs : List UInt) (post : List (List UInt)) :
    AbiEntry.encodeArgs (values (pre ++ xs :: post)) =
      AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (pre.length + 1 + post.length) ++
      dynamicHeads (payloads pre) (32 * (pre.length + 1 + post.length)) ++
      AbiEntry.wordBytes (innerOffset pre post) ++
      dynamicHeads (payloads post) (innerOffset pre post + (ArrayPairPacket.payload xs).length) ++
      (payloads pre).flatten ++ ArrayPairPacket.payload xs ++ (payloads post).flatten := by
  rw [encoded_layout]
  simp only [payloads,List.map_append,List.map_cons,List.flatten_append,List.flatten_cons,
    List.length_append,List.length_cons]
  rw [heads_append,heads_cons]
  simp only [innerOffset,payloads,List.append_assoc,Nat.add_assoc,Nat.add_comm post.length 1]

/-- Earlier tail bytes remain independent of arbitrary later inner values. -/
theorem earlier_payload_prefix (pre post : List (List UInt)) :
    ((AbiEntry.encodeArgs (values (pre ++ post))).drop (64 + 32 * (pre ++ post).length)).take
      (payloads pre).flatten.length = (payloads pre).flatten := by
  rw [after_heads]
  simp only [payloads,List.map_append,List.flatten_append]
  exact List.take_left

/-- The earlier HEAD prefix is independent of later payloads when the outer
count is unchanged. Entire later head entries can change if a middle tail grows. -/
theorem earlier_head_prefix (pre post : List (List UInt)) :
    (AbiEntry.encodeArgs (values (pre ++ post))).take (64 + 32 * pre.length) =
      AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (pre.length + post.length) ++
      dynamicHeads (payloads pre) (32 * (pre.length + post.length)) := by
  have split : AbiEntry.encodeArgs (values (pre ++ post)) =
      (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (pre.length + post.length) ++
        dynamicHeads (payloads pre) (32 * (pre.length + post.length))) ++
      (dynamicHeads (payloads post) (32 * (pre.length + post.length) + (payloads pre).flatten.length) ++
        (payloads (pre ++ post)).flatten) := by
    rw [encoded_layout]
    simp only [payloads,List.map_append,List.length_append]
    rw [heads_append]
    simp only [List.append_assoc]
  rw [split]
  apply List.take_left'
  simp only [List.length_append,MixedPacket.word_length,heads_length,payloads,List.length_map]

theorem earlier_heads_noninterference (pre post₁ post₂ : List (List UInt))
    (count : post₁.length = post₂.length) :
    (AbiEntry.encodeArgs (values (pre ++ post₁))).take (64 + 32 * pre.length) =
      (AbiEntry.encodeArgs (values (pre ++ post₂))).take (64 + 32 * pre.length) := by
  rw [earlier_head_prefix,earlier_head_prefix,count]

/-- Keeping the outer member count fixed, current/later payload changes cannot
change this earlier relative offset. This is NOT whole-packet invariance. -/
theorem inner_head_noninterference (pre post₁ post₂ : List (List UInt)) (xs ys : List UInt)
    (count : post₁.length = post₂.length) :
    ((AbiEntry.encodeArgs (values (pre ++ xs :: post₁))).drop (64 + 32 * pre.length)).take 32 =
      ((AbiEntry.encodeArgs (values (pre ++ ys :: post₂))).drop (64 + 32 * pre.length)).take 32 := by
  rw [inner_head,inner_head,innerOffset,innerOffset,count]

/-- Changing the LAST inner value even changes its length without affecting
any previous head or payload. Its own tail starts after this exact prefix. -/
theorem before_last (pre : List (List UInt)) (xs : List UInt) :
    (AbiEntry.encodeArgs (values (pre ++ [xs]))).take
      (64 + 32 * (pre.length + 1) + (payloads pre).flatten.length) =
      AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (pre.length + 1) ++
      dynamicHeads (payloads pre) (32 * (pre.length + 1)) ++
      AbiEntry.wordBytes (innerOffset pre []) ++ (payloads pre).flatten := by
  rw [layout_split]
  simp only [List.length_nil,Nat.add_zero,payloads,List.map_nil,List.flatten_nil,
    dynamicHeads,AbiEntry.assemble.go,List.append_nil]
  apply List.take_left'
  simp only [List.length_append,MixedPacket.word_length]
  have heads := heads_length (payloads pre) (32 * (pre.length + 1))
  simp only [payloads,List.length_map,dynamicHeads] at heads
  rw [heads]
  omega

theorem last_noninterference (pre : List (List UInt)) (xs ys : List UInt) :
    (AbiEntry.encodeArgs (values (pre ++ [xs]))).take
      (64 + 32 * (pre.length + 1) + (payloads pre).flatten.length) =
    (AbiEntry.encodeArgs (values (pre ++ [ys]))).take
      (64 + 32 * (pre.length + 1) + (payloads pre).flatten.length) := by
  rw [before_last,before_last]

/-- Useful composition: regrouping TWO already observed arrays into one pure
nested value prefixes their actual pair codec, without a nested runtime heap. -/
theorem two_arrays (xs ys : List UInt) :
    AbiEntry.encodeArgs (values [xs,ys]) = AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2 ++
      AbiEntry.encodeArgs (ArrayPairPacket.values xs ys) := by
  rw [encoded_layout,ArrayPairPacket.encoded_values]
  simp only [payloads,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
    List.length_cons,List.length_nil,heads_cons,dynamicHeads,AbiEntry.assemble.go,
    List.append_nil,ArrayPairPacket.secondOffset,List.append_assoc,ite_true]

/-- The top-level dynamic offset and outer length are exact complete words. -/
theorem outer_header (xss : List (List UInt)) :
    (AbiEntry.encodeArgs (values xss)).take 32 = AbiEntry.wordBytes 32 ∧
    ((AbiEntry.encodeArgs (values xss)).drop 32).take 32 = AbiEntry.wordBytes xss.length := by
  constructor
  · rw [encoded_layout]
    simp only [List.append_assoc]
    exact List.take_left' (MixedPacket.word_length 32)
  · rw [encoded_layout]
    simp only [List.append_assoc]
    rw [List.drop_left' (MixedPacket.word_length 32)]
    exact List.take_left' (MixedPacket.word_length xss.length)

theorem aligned (xss : List (List UInt)) (pre post : List (List UInt)) :
    (AbiEntry.encodeArgs (values xss)).length % 32 = 0 ∧ innerOffset pre post % 32 = 0 := by
  rw [encoded_length,offset_formula]
  omega

/-- Consume a REAL accepted entry/body result when its exact typed witness is
available. This is not universal source admission or an admitted source encoder. -/
theorem accepted_layout (I : AbiEntry.Input) (fuel : Nat) (loc : AbiEntry.Loc)
    (xss : List (List UInt))
    (accepted : AbiEntry.verdict I fuel [{shape := Shape,loc}] = .run (values xss)) :
    ∃ es, AbiEntry.entry I fuel [{shape := Shape,loc}] = .ok es ∧
      AbiEntry.bodyValues I fuel [{shape := Shape,loc}] es 0 = .ok (values xss) ∧
      EntryTransport.bodyObservation I fuel [{shape := Shape,loc}] AbiEntry.encodeArgs =
        some (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes xss.length ++
          (List.range xss.length).flatMap (fun i => AbiEntry.wordBytes
            (32 * xss.length + ((payloads xss).take i).flatten.length)) ++ (payloads xss).flatten) := by
  obtain ⟨es,entered,body,observed⟩ := EntryTransport.body_witness (I := I) (fuel := fuel) (ps := [{shape := Shape,loc}]) (values xss) AbiEntry.encodeArgs accepted
  rw [encoded_indexed] at observed
  exact ⟨es,entered,body,observed⟩

/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.prefix_payload_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_payload_length
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.payload_words' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms payload_words
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.encoded_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_words
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.outer_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outer_header
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aligned
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.accepted_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_layout

/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.after_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms after_header
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.after_heads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms after_heads
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.inner_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inner_head
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.inner_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inner_payload
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.layout_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms layout_split
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.earlier_payload_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms earlier_payload_prefix
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.inner_head_noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inner_head_noninterference
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.earlier_head_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms earlier_head_prefix
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.earlier_heads_noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms earlier_heads_noninterference
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.before_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms before_last
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.last_noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms last_noninterference
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.two_arrays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms two_arrays

/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.sequence_parts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms sequence_parts
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.heads_indexed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heads_indexed
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.encoded_indexed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_indexed
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.dynamic_tails' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_tails
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.heads_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heads_length
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.heads_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms heads_append
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.assemble_dynamic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assemble_dynamic
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.value_encoding' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms value_encoding
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.encoded_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_layout
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.payload_total_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payload_total_length
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.encoded_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_length
/-- info: 'Solidity.Backend.AbiWorld.NestedUintPacket.offset_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms offset_formula
end Solidity.Backend.AbiWorld.NestedUintPacket
