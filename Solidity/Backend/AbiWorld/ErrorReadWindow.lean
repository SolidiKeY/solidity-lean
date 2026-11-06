import Solidity.Backend.AbiWorld.ErrorRoundtrip
import Solidity.Backend.Failure.Correct

/-! Observations of the existing Error decoder on complete payload windows.
No new decoder, admission predicate, caller phase or runtime ABI encoder. -/
namespace Solidity.Backend.AbiWorld.ErrorReadWindow
open Semantics Failure

/-- Padding and trailing bytes are not inspected by the published decoder. -/
theorem unpadded (bs suffix : List UInt8) (hlen : bs.length < 256^32) :
    decodeError (errorSelector ++ wordBytes 32 ++ wordBytes bs.length ++ bs ++ suffix) = some bs := by
  have hs : (errorSelector ++ wordBytes 32 ++ wordBytes bs.length ++ bs ++ suffix).take 4 = errorSelector := by
    simp only [List.append_assoc]
    exact List.take_left' (by decide)
  have hb : (errorSelector ++ wordBytes 32 ++ wordBytes bs.length ++ bs ++ suffix).drop 4 =
      wordBytes 32 ++ (wordBytes bs.length ++ (bs ++ suffix)) := by
    simp only [List.append_assoc]
    exact List.drop_left' (by decide)
  have ho : (wordBytes 32 ++ (wordBytes bs.length ++ (bs ++ suffix))).take 32 = wordBytes 32 :=
    List.take_left' (word_length 32)
  have hr : (wordBytes 32 ++ (wordBytes bs.length ++ (bs ++ suffix))).drop 32 =
      wordBytes bs.length ++ (bs ++ suffix) := List.drop_left' (word_length 32)
  have hl : (wordBytes bs.length ++ (bs ++ suffix)).take 32 = wordBytes bs.length :=
    List.take_left' (word_length bs.length)
  have hd : (wordBytes bs.length ++ (bs ++ suffix)).drop 32 = bs ++ suffix :=
    List.drop_left' (word_length bs.length)
  have enoughHead : ¬ (wordBytes 32 ++ (wordBytes bs.length ++ (bs ++ suffix))).length < 32 := by
    simp only [List.length_append, word_length]
    omega
  have enoughLength : ¬ (wordBytes bs.length ++ (bs ++ suffix)).length < 32 := by
    simp only [List.length_append, word_length]
    omega
  simp only [decodeError, hs, ite_true, hb, ho, read_word 32 (by decide), hr,
    enoughHead, enoughLength, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    hl, read_word bs.length hlen, hd, List.take_left]

/-- The window is cut from the existing encoder, not a replacement encoder. -/
theorem source_prefix (bs : List UInt8) :
    (encodeError bs).take (68 + bs.length) =
      errorSelector ++ wordBytes 32 ++ wordBytes bs.length ++ bs := by
  have hlen : (errorSelector ++ wordBytes 32 ++ wordBytes bs.length ++ bs).length = 68 + bs.length := by
    simp only [List.length_append, errorSelector, List.length_cons, List.length_nil, word_length]
  have enc : encodeError bs =
      (errorSelector ++ wordBytes 32 ++ wordBytes bs.length ++ bs) ++
        List.replicate ((32-bs.length%32)%32) 0 := by
    simp only [encodeError, pad32, List.append_assoc]
  rw [enc, ← hlen]
  exact List.take_left

/-- Arbitrary trailing data and omitted padding leave the reason unchanged. -/
theorem prefix_readback (bs suffix : List UInt8) (hlen : bs.length < 256^32) :
    decodeError ((encodeError bs).take (68+bs.length) ++ suffix) = some bs := by
  rw [source_prefix]
  exact unpadded bs suffix hlen

/-- Actual constant-packet terminal execution and readback. Padding is absent
and suffix bytes remain in the full revert; only the decoded reason ignores them.
No source-caller catch or runtime-memory encoder is inferred. -/
theorem emitted (bs suffix : List UInt8) (address : Nat) (tail : Program)
    (machine : Slice.Machine)
    (fits : Fits address ((encodeError bs).take (68+bs.length) ++ suffix))
    (stack : machine.stack.length+2 ≤ 1024) :
    let data := (encodeError bs).take (68+bs.length) ++ suffix
    Slice.checkedRun (emit address (.custom data) ++ tail) machine =
      some ({machine with memory := Slice.putBytes machine.memory address data},
        some (Roadmap.Outcome.revert data)) ∧
    Slice.getBytes (Slice.putBytes machine.memory address data) address data.length = data ∧
    decodeError (Slice.getBytes (Slice.putBytes machine.memory address data) address data.length) = some bs := by
  have hlen : bs.length < 256^32 := by
    change bs.length < wordLimit
    have h := fits.2.1
    rw [source_prefix] at h
    simp only [List.length_append, errorSelector, List.length_cons, List.length_nil, word_length] at h
    omega
  refine ⟨checkedRun_emit_suffix address (.custom _) tail machine fits stack,
    Slice.getBytes_putBytes _ _ _, ?_⟩
  rw [Slice.getBytes_putBytes]
  exact prefix_readback bs suffix hlen

end Solidity.Backend.AbiWorld.ErrorReadWindow

#print axioms Solidity.Backend.AbiWorld.ErrorReadWindow.unpadded
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindow.source_prefix
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindow.prefix_readback
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindow.emitted
#check Solidity.Backend.AbiWorld.ErrorReadWindow.emitted

