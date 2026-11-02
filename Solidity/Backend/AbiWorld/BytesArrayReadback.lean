import Solidity.Backend.AbiWorld.EntryComposition

/-! Heterogeneous dynamic bytes/uint-array canonical entry readback. Actual
codec offsets, original allocation/fuel and indexed values are retained.
No new semantics, admission restriction, runtime encoder or native agreement. -/
namespace Solidity.Backend.AbiWorld.BytesArrayReadback
open AbiEntry CanonicalReadback
abbrev UInt := PrimTy.uint.Denote

def bytePayload (bs : List UInt8) : List UInt8 := AbiEntry.Val.enc (.bytes bs)
def arrayPayload (xs : List UInt) : List UInt8 := ArrayPairPacket.payload xs

def values (bs : List UInt8) (xs : List UInt) : Vals [.bytes,WordArrayPacket.Shape] :=
  ArrayPairPacket.append (BytesReadback.values bs) (WordArrayPacket.values xs)
def reverseValues (bs : List UInt8) (xs : List UInt) : Vals [WordArrayPacket.Shape,.bytes] :=
  ArrayPairPacket.append (WordArrayPacket.values xs) (BytesReadback.values bs)

theorem byte_payload_length (bs : List UInt8) : (bytePayload bs).length = BytesReadback.allocationBytes bs := by
  have h := BytesReadback.rounded_bounds bs.length
  simp only [bytePayload,Val.enc,List.length_append,MixedPacket.word_length,List.length_replicate,
    BytesReadback.allocationBytes]
  omega

theorem array_payload_length (xs : List UInt) : (arrayPayload xs).length = TupleReadback.cost xs := by
  rw [arrayPayload,ArrayPairPacket.payload_length,TupleReadback.cost]
  omega

theorem encoded (bs : List UInt8) (xs : List UInt) : encodeArgs (values bs xs) =
    AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (64 + (bytePayload bs).length) ++
      bytePayload bs ++ arrayPayload xs :=
  EntryComposition.encoded_dynamic_pair (.bytes bs) (.array (WordArrayPacket.sequence xs)) rfl rfl

theorem reverse_encoded (bs : List UInt8) (xs : List UInt) : encodeArgs (reverseValues bs xs) =
    AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (64 + (arrayPayload xs).length) ++
      arrayPayload xs ++ bytePayload bs :=
  EntryComposition.encoded_dynamic_pair (.array (WordArrayPacket.sequence xs)) (.bytes bs) rfl rfl

/-- Byte payload decoding at the actual tuple-relative offset and arbitrary
allocation cursor. The allocator runs before its payload-region check. -/
theorem bytes_window (bs : List UInt8) (I : Input) (pos off a f : Nat) (post : List UInt8)
    (head : load I.data (4 + pos) = off) (offset : off ≤ lim)
    (tail : I.data.drop (4 + off) = AbiEntry.wordBytes bs.length ++ bs ++ post)
    (position : 4 + off ≤ I.size)
    (allocation : I.free + (a + BytesReadback.allocationBytes bs) ≤ lim) (fuel : 2 ≤ f) :
    melem I f .bytes 4 (4 + pos) a = .ok (.bytes bs,a + BytesReadback.allocationBytes bs) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have prelen : (I.data.take (4 + off)).length = 4 + off := by
    simp only [List.length_take,Input.size] at *
    omega
  have data : I.data = I.data.take (4 + off) ++ AbiEntry.wordBytes bs.length ++ bs ++ post := by
    calc I.data = I.data.take (4 + off) ++ I.data.drop (4 + off) := (List.take_append_drop _ I.data).symm
         _ = _ := by rw [tail]; simp only [List.append_assoc]
  have decoded := BytesReadback.mdec_bytes bs I (I.data.take (4 + off)) post a g data allocation (by omega)
  rw [prelen] at decoded
  simp only [melem,Shape.dynamic,head,if_neg (Nat.not_lt.mpr offset)]
  exact decoded

theorem bytes_reference (bs : List UInt8) (I : Input) (pos off : Nat) (post : List UInt8)
    (head : load I.data (4 + pos) = off) (offset : off ≤ lim)
    (tail : I.data.drop (4 + off) = AbiEntry.wordBytes bs.length ++ bs ++ post)
    (position : 4 + off ≤ I.size) (size : I.size ≤ lim) :
    cref I .bytes 4 pos = .ok (4 + off + 32,bs.length) := by
  have extent : 4 + off + 32 + bs.length ≤ I.size := by
    have h := congrArg List.length tail
    simp only [List.length_drop,List.length_append,MixedPacket.word_length,Input.size] at *
    omega
  have lenlim : bs.length ≤ lim := by omega
  have range : bs.length < AbiEntry.W := by
    have h : lim < AbiEntry.W := by decide
    omega
  have slice : (I.data.drop (4 + off)).take 32 = AbiEntry.wordBytes bs.length := by
    rw [tail]
    simpa only [MixedPacket.word_length,List.append_assoc] using
      (List.take_left (l₁ := AbiEntry.wordBytes bs.length) (l₂ := bs ++ post))
  have read := load_slice I.data (4 + off) bs.length slice range
  simp only [cref,Shape.dynamic,head,if_neg (Nat.not_lt.mpr offset),
    if_pos (by omega : 4 + off + 31 < I.size),read,if_neg (Nat.not_lt.mpr lenlim),
    Shape.stride,Nat.mul_one,if_neg (Nat.not_lt.mpr extent),ite_true]

def byteParam (lazy : Bool) : Param := {shape := .bytes,loc := if lazy then .calldata else .memory}
def spentBytes (lazy : Bool) (bs : List UInt8) : Nat := if lazy then 0 else BytesReadback.allocationBytes bs

def params (bl al : Bool) : List Param := [byteParam bl,TupleReadback.arrayParam al]
def reverseParams (bl al : Bool) : List Param := [TupleReadback.arrayParam al,byteParam bl]

def input (bs : List UInt8) (xs : List UInt) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (values bs xs) ++ post,free⟩
def reverseInput (bs : List UInt8) (xs : List UInt) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (reverseValues bs xs) ++ post,free⟩

def byteEntry (lazy : Bool) (bs : List UInt8) (off : Nat) : Entered .bytes :=
  if lazy then .ref (4 + off + 32) bs.length else .val (.bytes bs)
def entries (bl al : Bool) (bs : List UInt8) (xs : List UInt) : Entries (params bl al) :=
  .cons (byteEntry bl bs 64) (.cons (TupleReadback.arrayEntry al xs (64 + (bytePayload bs).length)) .nil)
def reverseEntries (bl al : Bool) (bs : List UInt8) (xs : List UInt) : Entries (reverseParams bl al) :=
  .cons (TupleReadback.arrayEntry al xs 64) (.cons (byteEntry bl bs (64 + (arrayPayload xs).length)) .nil)

theorem input_size (bs : List UInt8) (xs : List UInt) (selector post : List UInt8) (free : Nat) :
    (input bs xs selector post free).size = selector.length + 64 + BytesReadback.allocationBytes bs +
      TupleReadback.cost xs + post.length := by
  simp only [input,Input.size,encoded,List.length_append,MixedPacket.word_length,
    byte_payload_length,array_payload_length]
  omega

theorem reverse_input_size (bs : List UInt8) (xs : List UInt) (selector post : List UInt8) (free : Nat) :
    (reverseInput bs xs selector post free).size = selector.length + 64 + TupleReadback.cost xs +
      BytesReadback.allocationBytes bs + post.length := by
  simp only [reverseInput,Input.size,reverse_encoded,List.length_append,MixedPacket.word_length,
    byte_payload_length,array_payload_length]
  omega

/-- Both actual decoders, references and eager body values follow from the
actual codec. Natural offsets are bounded using complete input size. -/
theorem entry_body (bs : List UInt8) (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (bl al : Bool) (sel : selector.length = 4) (size : (input bs xs selector post free).size ≤ lim)
    (allocation : free + (BytesReadback.allocationBytes bs + TupleReadback.cost xs) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    enter (input bs xs selector post free) f (params bl al) 0 0 =
      .ok (entries bl al bs xs,spentBytes bl bs + TupleReadback.spent al xs) ∧
    verdict (input bs xs selector post free) f (params bl al) = .run (values bs xs) := by
  let I := input bs xs selector post free
  let off := 64 + (bytePayload bs).length
  have offset : off ≤ lim := by
    change (input bs xs selector post free).size ≤ lim at size
    rw [input_size,sel] at size
    dsimp only [off]; rw [byte_payload_length]; omega
  have range : off < AbiEntry.W := by
    have h : lim < AbiEntry.W := by decide
    omega
  have representation : I.data = selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes off ++
      bytePayload bs ++ arrayPayload xs ++ post := by
    dsimp only [I,input]
    rw [encoded]
    simp only [off,List.append_assoc]
  have reads := EntryComposition.layout_reads (bytePayload bs) (arrayPayload xs) selector post sel range
  dsimp only at reads
  rw [← representation] at reads
  have bt : I.data.drop 68 = AbiEntry.wordBytes bs.length ++ bs ++
      (List.replicate (roundUp bs.length - bs.length) 0 ++ arrayPayload xs ++ post) := by
    rw [reads.2.2.1]; simp only [bytePayload,Val.enc,List.append_assoc]
  have arrayTail : I.data.drop (4 + off) = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post := by
    rw [reads.2.2.2]; simp only [arrayPayload,ArrayPairPacket.payload,MixedPacket.array_encoding,List.append_assoc]
  have bp : 4 + 64 ≤ I.size := by dsimp only [I]; rw [input_size,sel]; omega
  have ap : 4 + off ≤ I.size := by dsimp only [I,off]; rw [input_size,sel,byte_payload_length]; omega
  have db (a : Nat) (ha : a ≤ TupleReadback.cost xs) := bytes_window bs I 0 64 a f
    (List.replicate (roundUp bs.length - bs.length) 0 ++ arrayPayload xs ++ post)
    reads.1 (by decide) bt bp (by simp only [I,input]; omega) (by omega)
  have da (a : Nat) (ha : a ≤ BytesReadback.allocationBytes bs) := TupleReadback.array_window xs I 32 off a f post
    reads.2.1 offset arrayTail ap (by simp only [I,input]; omega) fuel
  have cb := bytes_reference bs I 0 64
    (List.replicate (roundUp bs.length - bs.length) 0 ++ arrayPayload xs ++ post)
    reads.1 (by decide) bt bp size
  have ca := TupleReadback.reference_window xs I 32 off post reads.2.1 offset arrayTail ap size
  have eb : eager I f .bytes 0 = .ok (.bytes bs) := by
    simp only [eager,Nat.add_zero,db 0 (by omega),Nat.zero_add]
  have ea : eager I f WordArrayPacket.Shape 32 = .ok (.array (WordArrayPacket.sequence xs)) := by
    simp only [eager,da 0 (by omega),Nat.zero_add]
  have entered : enter I f (params bl al) 0 0 =
      .ok (entries bl al bs xs,spentBytes bl bs + TupleReadback.spent al xs) := by
    change enter I f ([byteParam bl] ++ [TupleReadback.arrayParam al]) 0 0 = _
    rw [EntryComposition.enter_append]
    cases bl <;> cases al <;> simp only [params,entries,byteEntry,byteParam,TupleReadback.arrayParam,
      TupleReadback.arrayEntry,spentBytes,TupleReadback.spent,Bool.false_eq_true,ite_false,ite_true,
      enter,headsOf,List.map_cons,List.map_nil,Shape.headsSize,EntryComposition.appendEntries,
      Nat.add_zero,Nat.zero_add,Shape.headSize,WordArrayPacket.Shape,
      db 0 (by omega),da 0 (by omega),da (BytesReadback.allocationBytes bs) (by omega),cb,ca,
      bind,Except.bind,pure,Except.pure,off]
  refine ⟨entered,?_⟩
  have heads : ¬ I.size < 4 + headsOf (params bl al) := by
    simp only [headsOf,params,byteParam,TupleReadback.arrayParam,List.map_cons,List.map_nil,
      Shape.headsSize,Shape.headSize,WordArrayPacket.Shape,Nat.add_zero]
    omega
  dsimp only [I] at eb ea
  rw [verdict,entry,if_neg heads,entered]
  cases bl <;> cases al <;> simp only [params,entries,byteEntry,byteParam,TupleReadback.arrayParam,
    TupleReadback.arrayEntry,Bool.false_eq_true,ite_false,ite_true,bodyValues,Nat.add_zero,Nat.zero_add,
    WordArrayPacket.Shape,Shape.headSize,eb,ea,bind,Except.bind,pure,Except.pure,
    values,ArrayPairPacket.append,BytesReadback.values,WordArrayPacket.values]



/-- Reversing heterogeneous arguments changes the real second offset and
allocation order, while bl still denotes bytes and al still denotes array. -/
theorem reverse_entry_body (bs : List UInt8) (xs : List UInt) (selector post : List UInt8) (free f : Nat)
    (bl al : Bool) (sel : selector.length = 4) (size : (reverseInput bs xs selector post free).size ≤ lim)
    (allocation : free + (TupleReadback.cost xs + BytesReadback.allocationBytes bs) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    enter (reverseInput bs xs selector post free) f (reverseParams bl al) 0 0 =
      .ok (reverseEntries bl al bs xs,TupleReadback.spent al xs + spentBytes bl bs) ∧
    verdict (reverseInput bs xs selector post free) f (reverseParams bl al) = .run (reverseValues bs xs) := by
  let I := reverseInput bs xs selector post free
  let off := 64 + (arrayPayload xs).length
  have offset : off ≤ lim := by
    change (reverseInput bs xs selector post free).size ≤ lim at size
    rw [reverse_input_size,sel] at size
    dsimp only [off]; rw [array_payload_length]; omega
  have range : off < AbiEntry.W := by
    have h : lim < AbiEntry.W := by decide
    omega
  have representation : I.data = selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes off ++
      arrayPayload xs ++ bytePayload bs ++ post := by
    dsimp only [I,reverseInput]
    rw [reverse_encoded]
    simp only [off,List.append_assoc]
  have reads := EntryComposition.layout_reads (arrayPayload xs) (bytePayload bs) selector post sel range
  dsimp only at reads
  rw [← representation] at reads
  have arrayTail : I.data.drop 68 = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ (bytePayload bs ++ post) := by
    rw [reads.2.2.1]
    simp only [arrayPayload,ArrayPairPacket.payload,MixedPacket.array_encoding,List.append_assoc]
  have bt : I.data.drop (4 + off) = AbiEntry.wordBytes bs.length ++ bs ++
      (List.replicate (roundUp bs.length - bs.length) 0 ++ post) := by
    rw [reads.2.2.2]; simp only [bytePayload,Val.enc,List.append_assoc]
  have ap : 4 + 64 ≤ I.size := by dsimp only [I]; rw [reverse_input_size,sel]; omega
  have bp : 4 + off ≤ I.size := by dsimp only [I,off]; rw [reverse_input_size,sel,array_payload_length]; omega
  have da (a : Nat) (ha : a ≤ BytesReadback.allocationBytes bs) := TupleReadback.array_window xs I 0 64 a f
    (bytePayload bs ++ post) reads.1 (by decide) arrayTail ap
    (by simp only [I,reverseInput]; omega) fuel
  have db (a : Nat) (ha : a ≤ TupleReadback.cost xs) := bytes_window bs I 32 off a f
    (List.replicate (roundUp bs.length - bs.length) 0 ++ post) reads.2.1 offset bt bp
    (by simp only [I,reverseInput]; omega) (by omega)
  have ca := TupleReadback.reference_window xs I 0 64 (bytePayload bs ++ post) reads.1 (by decide) arrayTail ap size
  have cb := bytes_reference bs I 32 off (List.replicate (roundUp bs.length - bs.length) 0 ++ post)
    reads.2.1 offset bt bp size
  have ea : eager I f WordArrayPacket.Shape 0 = .ok (.array (WordArrayPacket.sequence xs)) := by
    simp only [eager,Nat.add_zero,da 0 (by omega),Nat.zero_add]
  have eb : eager I f .bytes 32 = .ok (.bytes bs) := by
    simp only [eager,db 0 (by omega),Nat.zero_add]
  have entered : enter I f (reverseParams bl al) 0 0 =
      .ok (reverseEntries bl al bs xs,TupleReadback.spent al xs + spentBytes bl bs) := by
    change enter I f ([TupleReadback.arrayParam al] ++ [byteParam bl]) 0 0 = _
    rw [EntryComposition.enter_append]
    cases bl <;> cases al <;> simp only [reverseParams,reverseEntries,byteEntry,byteParam,TupleReadback.arrayParam,
      TupleReadback.arrayEntry,spentBytes,TupleReadback.spent,Bool.false_eq_true,ite_false,ite_true,
      enter,headsOf,List.map_cons,List.map_nil,Shape.headsSize,EntryComposition.appendEntries,
      Nat.add_zero,Nat.zero_add,Shape.headSize,WordArrayPacket.Shape,
      da 0 (by omega),db 0 (by omega),db (TupleReadback.cost xs) (by omega),cb,ca,
      bind,Except.bind,pure,Except.pure,off]
  refine ⟨entered,?_⟩
  have heads : ¬ I.size < 4 + headsOf (reverseParams bl al) := by
    simp only [headsOf,reverseParams,byteParam,TupleReadback.arrayParam,List.map_cons,List.map_nil,
      Shape.headsSize,Shape.headSize,WordArrayPacket.Shape,Nat.add_zero]
    omega
  dsimp only [I] at eb ea
  rw [verdict,entry,if_neg heads,entered]
  cases bl <;> cases al <;> simp only [reverseParams,reverseEntries,byteEntry,byteParam,TupleReadback.arrayParam,
    TupleReadback.arrayEntry,Bool.false_eq_true,ite_false,ite_true,bodyValues,Nat.add_zero,Nat.zero_add,
    WordArrayPacket.Shape,Shape.headSize,eb,ea,bind,Except.bind,pure,Except.pure,
    reverseValues,ArrayPairPacket.append,BytesReadback.values,WordArrayPacket.values]


/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.byte_payload_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byte_payload_length
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.array_payload_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_payload_length
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.reverse_encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms reverse_encoded
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.bytes_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_window
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.bytes_reference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_reference
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.input_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_size
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.reverse_input_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverse_input_size
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.entry_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_body
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayReadback.reverse_entry_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverse_entry_body
end Solidity.Backend.AbiWorld.BytesArrayReadback
