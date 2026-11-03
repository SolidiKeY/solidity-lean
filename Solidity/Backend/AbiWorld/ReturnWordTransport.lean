import Solidity.Semantics.ExternalReturnBytes
import Solidity.Backend.AbiWorld.LibraryResultPacket
import Solidity.Backend.AbiWorld.PanicReadWindow

/-! Primitive return-word transport over actual indexed ABI values and the
published byte reader. Declared Source return demand remains a separate owner. -/
namespace Solidity.Backend.AbiWorld.ReturnWordTransport
open Semantics Failure
abbrev UInt := AbiEntry.Word (.uint 256)

def values : (xs : List UInt) → AbiEntry.Vals (List.replicate xs.length (.word (.uint 256)))
  | [] => .nil
  | x::xs => .cons (.word x) (values xs)

def semanticWord (x : UInt) : Semantics.Word :=
  PanicReadWindow.word x.val (by rw [← AbiEntry.W_eq]; exact x.lt)

/-- Reused original owned CanonicalReadback byte-window argument; no new loader. -/
theorem bytes_word (pre post : List UInt8) (n : Nat) :
    AbiEntry.bytesAt (pre ++ AbiEntry.wordBytes n ++ post) pre.length 32 = AbiEntry.wordBytes n := by
  apply List.ext_getElem (by simp only [AbiEntry.bytesAt,List.length_map,List.length_range,LibraryResultPacket.word_bytes,word_length])
  intro i hi hj
  have h : i<32 := by simpa only [LibraryResultPacket.word_bytes,word_length] using hj
  simp only [AbiEntry.bytesAt,List.getElem_map,List.getElem_range,AbiEntry.byteAt,List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [LibraryResultPacket.word_bytes,word_length] using h),List.getElem?_eq_getElem hj]
  rfl

/-- Reused original owned full-word load argument, with its nonwrap premise. -/
theorem load_word (pre post : List UInt8) (x : UInt) :
    AbiEntry.load (pre ++ AbiEntry.wordBytes x.val ++ post) pre.length = x.val := by
  have fold : AbiEntry.load (pre ++ AbiEntry.wordBytes x.val ++ post) pre.length =
      bytesNat (AbiEntry.bytesAt (pre ++ AbiEntry.wordBytes x.val ++ post) pre.length 32) % AbiEntry.W := by
    simp only [AbiEntry.load,bytesNat,AbiEntry.bytesAt,List.foldl_map]
  rw [fold,bytes_word,LibraryResultPacket.word_bytes,read_word x.val (by simpa only [AbiEntry.W] using x.lt),Nat.mod_eq_of_lt x.lt]

theorem static_go (xs : List UInt) (offset : Nat) :
    AbiEntry.assemble.go (AbiEntry.Vals.parts (values xs)) offset =
      (xs.flatMap (fun x => AbiEntry.wordBytes x.val),[]) := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih =>
    simp only [values,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,AbiEntry.Val.enc,
      AbiEntry.assemble.go,Bool.false_eq_true,↓reduceIte,List.flatMap_cons,ih]

theorem encoded_values (xs : List UInt) : AbiEntry.encodeArgs (values xs) =
    xs.flatMap (fun x => AbiEntry.wordBytes x.val) := by
  simp only [AbiEntry.encodeArgs,AbiEntry.assemble,static_go,List.append_nil]

theorem byte_length (xs : List UInt) :
    (xs.flatMap (fun x => AbiEntry.wordBytes x.val)).length = 32*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have size : (AbiEntry.wordBytes x.val).length = 32 := by rw [LibraryResultPacket.word_bytes,word_length]
    simp only [List.flatMap_cons,List.length_append,size,List.length_cons,ih]
    omega

theorem wordAt_window (pre post : List UInt8) (x : UInt) :
    ExternalReturnBytes.wordAt (pre ++ AbiEntry.wordBytes x.val ++ post) pre.length = semanticWord x := by
  apply Subtype.ext
  change (AbiEntry.load (pre ++ AbiEntry.wordBytes x.val ++ post) pre.length : Int) = (x.val : Int)
  rw [load_word]

theorem wordAt_index (xs : List UInt) (suffix : List UInt8) (j : Nat) (hj : j < xs.length) :
    ExternalReturnBytes.wordAt (AbiEntry.encodeArgs (values xs) ++ suffix) (j*32) = semanticWord xs[j] := by
  have parts : xs.take j ++ xs[j] :: xs.drop (j+1) = xs := by
    rw [← List.drop_eq_getElem_cons hj]
    exact List.take_append_drop _ _
  have split := congrArg (fun ys : List UInt => ys.flatMap (fun x => AbiEntry.wordBytes x.val)) parts
  simp only [List.flatMap_append,List.flatMap_cons] at split
  have bytes : xs.flatMap (fun x => AbiEntry.wordBytes x.val) ++ suffix =
      (xs.take j).flatMap (fun x => AbiEntry.wordBytes x.val) ++ AbiEntry.wordBytes xs[j].val ++
        ((xs.drop (j+1)).flatMap (fun x => AbiEntry.wordBytes x.val) ++ suffix) := by
    rw [← split]
    simp only [List.append_assoc]
  have position : ((xs.take j).flatMap (fun x => AbiEntry.wordBytes x.val)).length = j*32 := by
    rw [byte_length,List.length_take,Nat.min_eq_left (Nat.le_of_lt hj),Nat.mul_comm]
  rw [encoded_values,bytes,← position]
  exact wordAt_window _ _ _

/-- Complete demanded words of the actual canonical result, with arbitrary
extra bytes. No Source declared-demand/binder-discard law is asserted. -/
theorem words_readback (xs : List UInt) (suffix : List UInt8) :
    ExternalReturnBytes.words xs.length (AbiEntry.encodeArgs (values xs) ++ suffix) =
      .ok (xs.map semanticWord) := by
  have complete : xs.length*32 ≤ (AbiEntry.encodeArgs (values xs) ++ suffix).length := by
    rw [encoded_values,List.length_append,byte_length]
    omega
  rw [ExternalReturnBytes.words,if_pos complete]
  apply congrArg Except.ok
  apply List.ext_getElem (by simp only [List.length_map,List.length_range])
  intro j hi hj
  have h : j<xs.length := by simpa only [List.length_map] using hj
  simp only [List.getElem_map,List.getElem_range]
  exact wordAt_index xs suffix j h

/-- All existing primitive-binder validation remains in the actual decoder. -/
theorem decode_transport {C : Contract} {H : HTy} {ρ : Ctx} (rets : Binders ρ)
    (xs : List UInt) (count : ρ.length = xs.length) (suffix : List UInt8) :
    ExternalReturnBytes.decode (C:=C) (H:=H) rets (AbiEntry.encodeArgs (values xs) ++ suffix) =
      rets.decodeT (C:=C) (H:=H) (xs.map semanticWord) := by
  unfold ExternalReturnBytes.decode
  rw [count,words_readback]
  rfl

/-- The complete-word check rejects a missing final demanded byte even though
AbiEntry.load itself zero-pads. This is not an aggregate decoder theorem. -/
theorem truncated (xs : List UInt) (nonempty : xs ≠ []) :
    ExternalReturnBytes.words xs.length ((AbiEntry.encodeArgs (values xs)).take (32*xs.length-1)) = .error .revert := by
  have positive : 0<xs.length := List.length_pos_iff.mpr nonempty
  have short : ((AbiEntry.encodeArgs (values xs)).take (32*xs.length-1)).length < xs.length*32 := by
    rw [List.length_take,encoded_values,byte_length]
    omega
  rw [ExternalReturnBytes.words,if_neg (Nat.not_le_of_gt short)]

/-- Actual known-packet emission and reached-byte readback into the published
word reader; no fetched CALL/RETURNDATA or synchronized byte/word machine law. -/
theorem emitted (xs : List UInt) (address : Nat) (tail : Program) (machine : Slice.Machine)
    (fits : Fits address (AbiEntry.encodeArgs (values xs))) (stack : machine.stack.length+2≤1024) :
    let data := AbiEntry.encodeArgs (values xs)
    Slice.checkedRun (emit address (.returned data) ++ tail) machine =
      some ({machine with memory := Slice.putBytes machine.memory address data},some (.success data)) ∧
    ExternalReturnBytes.words xs.length (Slice.getBytes (Slice.putBytes machine.memory address data) address data.length) =
      .ok (xs.map semanticWord) := by
  refine ⟨checkedRun_emit_suffix address (.returned _) tail machine fits stack,?_⟩
  rw [Slice.getBytes_putBytes]
  simpa only [List.append_nil] using words_readback xs []

end Solidity.Backend.AbiWorld.ReturnWordTransport
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransport.encoded_values
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransport.wordAt_index
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransport.words_readback
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransport.decode_transport
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransport.emitted


#print axioms Solidity.Backend.AbiWorld.ReturnWordTransport.truncated
