import Solidity.Semantics.AbiEntry
import Solidity.Backend.AbiWorld.ErrorLayout

/-! Scalar plus bytes result observations of the existing indexed ABI codec.
No runtime memory encoder or source library execution is defined here. -/
namespace Solidity.Backend.AbiWorld.LibraryResultPacket
open Semantics

def uint (n : Fin AbiEntry.W) : AbiEntry.Word (.uint 256) :=
  ⟨n.val,n.isLt,by change decide (n.val < 2^256) = true; rw [← AbiEntry.W_eq]; exact decide_eq_true n.isLt⟩
def values (n : Fin AbiEntry.W) (bs : List UInt8) : AbiEntry.Vals [.word (.uint 256),.bytes] :=
  .cons (.word (uint n)) (.cons (.bytes bs) .nil)

theorem word_bytes (n : Nat) : AbiEntry.wordBytes n = Semantics.wordBytes n := by
  unfold AbiEntry.wordBytes Semantics.wordBytes
  apply List.map_congr_left
  intro i member
  exact UInt8.ofNat_mod_size.symm

theorem encoded_values (n : Fin AbiEntry.W) (bs : List UInt8) :
    AbiEntry.encodeArgs (values n bs) = wordBytes n.val ++ wordBytes 64 ++ wordBytes bs.length ++ pad32 bs := by
  have padding : AbiEntry.roundUp bs.length-bs.length = (32-bs.length%32)%32 := by
    unfold AbiEntry.roundUp
    omega
  simp only [values,AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
    AbiEntry.Val.enc,uint,AbiEntry.assemble,AbiEntry.assemble.go,List.foldl_cons,List.foldl_nil,
    Bool.false_eq_true,↓reduceIte,Nat.zero_add,word_bytes,word_length,List.append_nil,
    List.append_assoc,pad32,padding]

/-- This is a natural byte-length equation, not a nonwrapping admission law. -/
theorem length (n : Fin AbiEntry.W) (bs : List UInt8) :
    (AbiEntry.encodeArgs (values n bs)).length = 96+bs.length+(32-bs.length%32)%32 := by
  rw [encoded_values]
  simp only [List.length_append,word_length,padded_length]
  omega

theorem marker (n : Fin AbiEntry.W) (bs : List UInt8) :
    (AbiEntry.encodeArgs (values n bs)).take 32 = wordBytes n.val := by
  rw [encoded_values]
  simp only [List.append_assoc]
  exact List.take_left' (word_length _)

theorem offset (n : Fin AbiEntry.W) (bs : List UInt8) :
    ((AbiEntry.encodeArgs (values n bs)).drop 32).take 32 = wordBytes 64 := by
  rw [encoded_values]
  simp only [List.append_assoc]
  have hd : (wordBytes n.val ++ (wordBytes 64 ++ (wordBytes bs.length ++ pad32 bs))).drop 32 =
      wordBytes 64 ++ (wordBytes bs.length ++ pad32 bs) := List.drop_left' (word_length _)
  rw [hd]
  exact List.take_left' (word_length _)

theorem payload (n : Fin AbiEntry.W) (bs : List UInt8) :
    ((AbiEntry.encodeArgs (values n bs)).drop 96).take bs.length = bs := by
  rw [encoded_values]
  have hd : (wordBytes n.val ++ wordBytes 64 ++ wordBytes bs.length ++ pad32 bs).drop 96 = pad32 bs :=
    List.drop_left' (by simp only [List.length_append,word_length])
  rw [hd,padded_payload]
end Solidity.Backend.AbiWorld.LibraryResultPacket
#print axioms Solidity.Backend.AbiWorld.LibraryResultPacket.encoded_values
#print axioms Solidity.Backend.AbiWorld.LibraryResultPacket.length
#print axioms Solidity.Backend.AbiWorld.LibraryResultPacket.marker
#print axioms Solidity.Backend.AbiWorld.LibraryResultPacket.offset
#print axioms Solidity.Backend.AbiWorld.LibraryResultPacket.payload
