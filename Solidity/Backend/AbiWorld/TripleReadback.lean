import Solidity.Backend.AbiWorld.BodyComposition
import Solidity.Backend.AbiWorld.BytesArrayReadback

/-! Actual typed bytes/uint-array/scalar entry and body readback. Both enter
and bodyValues composition are consumed; complete codec bytes discharge their
premises. No runtime encoder, raw-return phase, admission or world simulation. -/
namespace Solidity.Backend.AbiWorld.TripleReadback
open AbiEntry CanonicalReadback
abbrev UInt := PrimTy.uint.Denote

def values (bs : List UInt8) (xs : List UInt) (v : UInt) :
    Vals [.bytes,WordArrayPacket.Shape,MixedPacket.ScalarShape] :=
  .cons (.bytes bs) (.cons (.array (WordArrayPacket.sequence xs)) (.cons (.word (WordArrayPacket.uintWord v)) .nil))
def params (bl al : Bool) : List Param := BytesArrayReadback.params bl al ++ [TupleReadback.scalarParam]
def prefixEntries (bl al : Bool) (bs : List UInt8) (xs : List UInt) : Entries (BytesArrayReadback.params bl al) :=
  .cons (BytesArrayReadback.byteEntry bl bs 96)
    (.cons (TupleReadback.arrayEntry al xs (96 + (BytesArrayReadback.bytePayload bs).length)) .nil)
def tailEntries (v : UInt) : Entries [TupleReadback.scalarParam] := .cons (.val (.word (WordArrayPacket.uintWord v))) .nil
def entries (bl al : Bool) (bs : List UInt8) (xs : List UInt) (v : UInt) : Entries (params bl al) :=
  EntryComposition.appendEntries (prefixEntries bl al bs xs) (tailEntries v)
def cursor (bl al : Bool) (bs : List UInt8) (xs : List UInt) : Nat :=
  BytesArrayReadback.spentBytes bl bs + TupleReadback.spent al xs

theorem encoded (bs : List UInt8) (xs : List UInt) (v : UInt) : encodeArgs (values bs xs v) =
    AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes (96 + (BytesArrayReadback.bytePayload bs).length) ++
      AbiEntry.wordBytes v.val.toNat ++ BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs := by
  have parts : Vals.parts (values bs xs v) =
      [(true,BytesArrayReadback.bytePayload bs),(true,BytesArrayReadback.arrayPayload xs),
       (false,AbiEntry.Val.enc (.word (WordArrayPacket.uintWord v)))] := rfl
  have scalar : AbiEntry.Val.enc (.word (WordArrayPacket.uintWord v)) = AbiEntry.wordBytes v.val.toNat := by
    rw [Val.enc,WordArrayPacket.uintWord_value]
  rw [encodeArgs,parts,scalar]
  simp only [AbiEntry.assemble,List.foldl_cons,List.foldl_nil,ite_true,Bool.false_eq_true,ite_false,
    MixedPacket.word_length,Nat.zero_add,AbiEntry.assemble.go,List.append_nil,List.append_assoc]

def input (bs : List UInt8) (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (values bs xs v) ++ post,free⟩

theorem input_size (bs : List UInt8) (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat) :
    (input bs xs v selector post free).size = selector.length + 96 + BytesReadback.allocationBytes bs +
      TupleReadback.cost xs + post.length := by
  simp only [input,Input.size,encoded,List.length_append,MixedPacket.word_length,
    BytesArrayReadback.byte_payload_length,BytesArrayReadback.array_payload_length]
  omega

theorem reads (bs : List UInt8) (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (size : (input bs xs v selector post free).size ≤ lim) :
    let I := input bs xs v selector post free
    let off := 96 + (BytesArrayReadback.bytePayload bs).length
    load I.data 4 = 96 ∧ load I.data 36 = off ∧ load I.data 68 = (WordArrayPacket.uintWord v).val ∧
    I.data.drop 100 = BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs ++ post ∧
    I.data.drop (4 + off) = BytesArrayReadback.arrayPayload xs ++ post := by
  let I := input bs xs v selector post free
  let off := 96 + (BytesArrayReadback.bytePayload bs).length
  have range : off < AbiEntry.W := by
    rw [input_size,sel] at size
    have h : lim < AbiEntry.W := by decide
    dsimp only [off]; rw [BytesArrayReadback.byte_payload_length]; omega
  have vrange : v.val.toNat < AbiEntry.W := by
    rw [← WordArrayPacket.uintWord_value]; exact (WordArrayPacket.uintWord v).lt
  have representation : I.data = selector ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes off ++
      AbiEntry.wordBytes v.val.toNat ++ BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs ++ post := by
    dsimp only [I,input]; rw [encoded]; simp only [off,List.append_assoc]
  dsimp only
  change load I.data 4 = 96 ∧ load I.data 36 = off ∧ load I.data 68 = (WordArrayPacket.uintWord v).val ∧
    I.data.drop 100 = BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs ++ post ∧
    I.data.drop (4 + off) = BytesArrayReadback.arrayPayload xs ++ post
  rw [representation]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [List.append_assoc,sel] using load_word selector (AbiEntry.wordBytes off ++ AbiEntry.wordBytes v.val.toNat ++
      BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs ++ post) 96 (by decide)
  · simpa only [List.append_assoc,sel,List.length_append,MixedPacket.word_length] using
      load_word (selector ++ AbiEntry.wordBytes 96) (AbiEntry.wordBytes v.val.toNat ++
        BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs ++ post) off range
  · simpa only [List.append_assoc,sel,List.length_append,MixedPacket.word_length,WordArrayPacket.uintWord_value] using
      load_word (selector ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes off)
        (BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs ++ post) v.val.toNat vrange
  · have h : (selector ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes off ++ AbiEntry.wordBytes v.val.toNat).length = 100 := by
      simp only [List.length_append,MixedPacket.word_length,sel]
    simpa only [List.append_assoc] using List.drop_left' h
      (l₂ := BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs ++ post)
  · have h : (selector ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes off ++ AbiEntry.wordBytes v.val.toNat ++
        BytesArrayReadback.bytePayload bs).length = 4 + off := by
      simp only [List.length_append,MixedPacket.word_length,sel,off]; omega
    simpa only [List.append_assoc] using List.drop_left' h (l₂ := BytesArrayReadback.arrayPayload xs ++ post)

/-- Generic actual typed triple. The scalar is decoded at its real head and
appended only after the actual heterogeneous prefix; neither success is assumed. -/
theorem roundtrip (bs : List UInt8) (xs : List UInt) (v : UInt) (selector post : List UInt8) (free f : Nat)
    (bl al : Bool) (sel : selector.length = 4) (size : (input bs xs v selector post free).size ≤ lim)
    (allocation : free + (BytesReadback.allocationBytes bs + TupleReadback.cost xs) ≤ lim)
    (fuel : xs.length + 4 ≤ f) :
    enter (input bs xs v selector post free) f (params bl al) 0 0 = .ok (entries bl al bs xs v,cursor bl al bs xs) ∧
    entry (input bs xs v selector post free) f (params bl al) = .ok (entries bl al bs xs v) ∧
    bodyValues (input bs xs v selector post free) f (params bl al) (entries bl al bs xs v) 0 = .ok (values bs xs v) ∧
    verdict (input bs xs v selector post free) f (params bl al) = .run (values bs xs v) := by
  let I := input bs xs v selector post free
  let off := 96 + (BytesArrayReadback.bytePayload bs).length
  have r := reads bs xs v selector post free sel size
  dsimp only at r
  have offset : off ≤ lim := by
    rw [input_size,sel] at size
    dsimp only [off]; rw [BytesArrayReadback.byte_payload_length]; omega
  have bp : 4 + 96 ≤ I.size := by dsimp only [I]; rw [input_size,sel]; omega
  have ap : 4 + off ≤ I.size := by dsimp only [I,off]; rw [input_size,sel,BytesArrayReadback.byte_payload_length]; omega
  have bt : I.data.drop 100 = AbiEntry.wordBytes bs.length ++ bs ++
      (List.replicate (roundUp bs.length - bs.length) 0 ++ BytesArrayReadback.arrayPayload xs ++ post) := by
    rw [r.2.2.2.1]; simp only [BytesArrayReadback.bytePayload,Val.enc,List.append_assoc]
  have atail : I.data.drop (4 + off) = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post := by
    rw [r.2.2.2.2]; simp only [BytesArrayReadback.arrayPayload,ArrayPairPacket.payload,MixedPacket.array_encoding,List.append_assoc]
  have db := BytesArrayReadback.bytes_window bs I 0 96 0 f
    (List.replicate (roundUp bs.length - bs.length) 0 ++ BytesArrayReadback.arrayPayload xs ++ post)
    r.1 (by decide) bt bp (by simp only [I,input,Nat.zero_add]; omega) (by omega)
  have da (a : Nat) (ha : a ≤ BytesReadback.allocationBytes bs) :=
    TupleReadback.array_window xs I 32 off a f post r.2.1 offset atail ap (by simp only [I,input]; omega) fuel
  have dv (a : Nat) := TupleReadback.scalar_window v I 64 a f r.2.2.1 (by omega)
  have cb := BytesArrayReadback.bytes_reference bs I 0 96
    (List.replicate (roundUp bs.length - bs.length) 0 ++ BytesArrayReadback.arrayPayload xs ++ post)
    r.1 (by decide) bt bp size
  have ca := TupleReadback.reference_window xs I 32 off post r.2.1 offset atail ap size
  have eb : eager I f .bytes 0 = .ok (.bytes bs) := by simp only [eager,Nat.add_zero,db,Nat.zero_add]
  have ea : eager I f WordArrayPacket.Shape 32 = .ok (.array (WordArrayPacket.sequence xs)) := by
    simp only [eager,da 0 (by omega),Nat.zero_add]
  have prefixRun : enter I f (BytesArrayReadback.params bl al) 0 0 =
      .ok (prefixEntries bl al bs xs,cursor bl al bs xs) := by
    cases bl <;> cases al <;> simp only [BytesArrayReadback.params,prefixEntries,BytesArrayReadback.byteParam,
      TupleReadback.arrayParam,BytesArrayReadback.byteEntry,TupleReadback.arrayEntry,cursor,
      BytesArrayReadback.spentBytes,TupleReadback.spent,Bool.false_eq_true,ite_false,ite_true,enter,
      Nat.add_zero,Nat.zero_add,Shape.headSize,WordArrayPacket.Shape,db,da 0 (by omega),
      da (BytesReadback.allocationBytes bs) (by omega),cb,ca,off,bind,Except.bind,pure,Except.pure]
  have tailRun : enter I f [TupleReadback.scalarParam] 64 (cursor bl al bs xs) =
      .ok (tailEntries v,cursor bl al bs xs) := by
    simp only [enter,TupleReadback.scalarParam,dv,tailEntries,MixedPacket.ScalarShape,Shape.headSize,bind,Except.bind,pure,Except.pure]
  have prefixBody : bodyValues I f (BytesArrayReadback.params bl al) (prefixEntries bl al bs xs) 0 =
      .ok (BytesArrayReadback.values bs xs) := by
    cases bl <;> cases al <;> simp only [BytesArrayReadback.params,prefixEntries,BytesArrayReadback.byteParam,
      TupleReadback.arrayParam,BytesArrayReadback.byteEntry,TupleReadback.arrayEntry,Bool.false_eq_true,ite_false,ite_true,
      bodyValues,Nat.add_zero,Nat.zero_add,Shape.headSize,WordArrayPacket.Shape,eb,ea,
      BytesArrayReadback.values,ArrayPairPacket.append,BytesReadback.values,WordArrayPacket.values,bind,Except.bind,pure,Except.pure]
  have tailBody : bodyValues I f [TupleReadback.scalarParam] (tailEntries v) 64 =
      .ok (.cons (.word (WordArrayPacket.uintWord v)) .nil) := by
    simp only [bodyValues,tailEntries,bind,Except.bind,pure,Except.pure]
  have headSize : headsOf (BytesArrayReadback.params bl al) = 64 := rfl
  have entered : enter I f (params bl al) 0 0 = .ok (entries bl al bs xs v,cursor bl al bs xs) := by
    change enter I f (BytesArrayReadback.params bl al ++ [TupleReadback.scalarParam]) 0 0 = _
    rw [EntryComposition.enter_append,prefixRun]
    simp only [bind,Except.bind,headSize,Nat.zero_add,tailRun,pure,Except.pure,entries]
  have body : bodyValues I f (params bl al) (entries bl al bs xs v) 0 = .ok (values bs xs v) := by
    have h := BodyComposition.body_success I f (prefixEntries bl al bs xs) (tailEntries v)
      (BytesArrayReadback.values bs xs) (.cons (.word (WordArrayPacket.uintWord v)) .nil) 0 prefixBody
      (by simpa only [headSize,Nat.zero_add] using tailBody)
    exact h
  have heads : ¬ I.size < 4 + headsOf (params bl al) := by
    rw [params,EntryComposition.heads_append,headSize]
    simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,TupleReadback.scalarParam,
      MixedPacket.ScalarShape,Shape.headSize,Nat.add_zero]
    omega
  have enteredEntry : entry I f (params bl al) = .ok (entries bl al bs xs v) := by
    rw [entry,if_neg heads,entered]
  refine ⟨entered,enteredEntry,body,?_⟩
  rw [verdict,enteredEntry]
  dsimp only [I] at body
  simp only [body]



/-- Actual calldata entry does not allocate or validate body copies. Its
scalar still needs the original two decoder steps. No body success is claimed. -/
theorem calldata_entry (bs : List UInt8) (xs : List UInt) (v : UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input bs xs v selector post free).size ≤ lim) (fuel : 2 ≤ f) :
    entry (input bs xs v selector post free) f (params true true) = .ok (entries true true bs xs v) := by
  let I := input bs xs v selector post free
  let off := 96 + (BytesArrayReadback.bytePayload bs).length
  have r := reads bs xs v selector post free sel size
  dsimp only at r
  have offset : off ≤ lim := by
    rw [input_size,sel] at size
    dsimp only [off]; rw [BytesArrayReadback.byte_payload_length]; omega
  have bp : 4 + 96 ≤ I.size := by dsimp only [I]; rw [input_size,sel]; omega
  have ap : 4 + off ≤ I.size := by dsimp only [I,off]; rw [input_size,sel,BytesArrayReadback.byte_payload_length]; omega
  have bt : I.data.drop 100 = AbiEntry.wordBytes bs.length ++ bs ++
      (List.replicate (roundUp bs.length - bs.length) 0 ++ BytesArrayReadback.arrayPayload xs ++ post) := by
    rw [r.2.2.2.1]; simp only [BytesArrayReadback.bytePayload,Val.enc,List.append_assoc]
  have atail : I.data.drop (4 + off) = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post := by
    rw [r.2.2.2.2]; simp only [BytesArrayReadback.arrayPayload,ArrayPairPacket.payload,MixedPacket.array_encoding,List.append_assoc]
  have cb := BytesArrayReadback.bytes_reference bs I 0 96
    (List.replicate (roundUp bs.length - bs.length) 0 ++ BytesArrayReadback.arrayPayload xs ++ post)
    r.1 (by decide) bt bp size
  have ca := TupleReadback.reference_window xs I 32 off post r.2.1 offset atail ap size
  have dv := TupleReadback.scalar_window v I 64 0 f r.2.2.1 fuel
  have entered : enter I f (params true true) 0 0 = .ok (entries true true bs xs v,0) := by
    simp only [params,BytesArrayReadback.params,BytesArrayReadback.byteParam,TupleReadback.arrayParam,
      List.cons_append,List.nil_append,enter,TupleReadback.scalarParam,cb,ca,dv,Nat.add_zero,Nat.zero_add,
      Bool.true_eq,ite_true,Shape.headSize,WordArrayPacket.Shape,MixedPacket.ScalarShape,
      entries,prefixEntries,tailEntries,EntryComposition.appendEntries,BytesArrayReadback.byteEntry,
      TupleReadback.arrayEntry,off,bind,Except.bind,pure,Except.pure]
  have heads : ¬ I.size < 4 + headsOf (params true true) := by
    change ¬ I.size < 100
    omega
  rw [entry,if_neg heads,entered]

/-- A real typed bytes prefix can succeed even when later parameters exhaust
fuel. This derives the head value, not an assumed body-success premise. -/
theorem bytes_prefix (bs : List UInt8) (xs : List UInt) (v : UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (size : (input bs xs v selector post free).size ≤ lim)
    (allocation : free + BytesReadback.allocationBytes bs ≤ lim) (fuel : 2 ≤ f) :
    bodyValues (input bs xs v selector post free) f [BytesArrayReadback.byteParam true]
      (.cons (BytesArrayReadback.byteEntry true bs 96) .nil) 0 = .ok (.cons (.bytes bs) .nil) := by
  let I := input bs xs v selector post free
  have r := reads bs xs v selector post free sel size
  dsimp only at r
  have bt : I.data.drop 100 = AbiEntry.wordBytes bs.length ++ bs ++
      (List.replicate (roundUp bs.length - bs.length) 0 ++ BytesArrayReadback.arrayPayload xs ++ post) := by
    rw [r.2.2.2.1]; simp only [BytesArrayReadback.bytePayload,Val.enc,List.append_assoc]
  have d := BytesArrayReadback.bytes_window bs I 0 96 0 f
    (List.replicate (roundUp bs.length - bs.length) 0 ++ BytesArrayReadback.arrayPayload xs ++ post)
    r.1 (by decide) bt (by dsimp only [I]; rw [input_size,sel]; omega)
    (by simpa only [I,input,Nat.zero_add] using allocation) fuel
  have e : eager I f .bytes 0 = .ok (.bytes bs) := by simp only [eager,Nat.add_zero,d]
  dsimp only [I] at e
  simp only [bodyValues,BytesArrayReadback.byteEntry,BytesArrayReadback.byteParam,ite_true,e,bind,Except.bind,pure,Except.pure]

/-- info: 'Solidity.Backend.AbiWorld.TripleReadback.encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded
/-- info: 'Solidity.Backend.AbiWorld.TripleReadback.input_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_size
/-- info: 'Solidity.Backend.AbiWorld.TripleReadback.reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reads
/-- info: 'Solidity.Backend.AbiWorld.TripleReadback.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
/-- info: 'Solidity.Backend.AbiWorld.TripleReadback.calldata_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_entry
/-- info: 'Solidity.Backend.AbiWorld.TripleReadback.bytes_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_prefix
end Solidity.Backend.AbiWorld.TripleReadback
