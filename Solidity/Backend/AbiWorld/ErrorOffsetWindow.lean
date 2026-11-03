import Solidity.Backend.AbiWorld.ErrorReadWindow

/-! Existing Error decoder observations with arbitrary ignored gap bytes.
No new decoder or acceptance profile; offsets remain explicitly representable. -/
namespace Solidity.Backend.AbiWorld.ErrorOffsetWindow
open Semantics Failure

theorem gap_readback (gap bs suffix : List UInt8)
    (hoff : 32+gap.length < 256^32) (hlen : bs.length < 256^32) :
    decodeError (errorSelector ++ wordBytes (32+gap.length) ++ gap ++ wordBytes bs.length ++ bs ++ suffix) = some bs := by
  have hs : (errorSelector ++ wordBytes (32+gap.length) ++ gap ++ wordBytes bs.length ++ bs ++ suffix).take 4 = errorSelector := by
    simp only [List.append_assoc]
    exact List.take_left' (by decide)
  have hb : (errorSelector ++ wordBytes (32+gap.length) ++ gap ++ wordBytes bs.length ++ bs ++ suffix).drop 4 =
      wordBytes (32+gap.length) ++ (gap ++ (wordBytes bs.length ++ (bs ++ suffix))) := by
    simp only [List.append_assoc]
    exact List.drop_left' (by decide)
  have ho : (wordBytes (32+gap.length) ++ (gap ++ (wordBytes bs.length ++ (bs ++ suffix)))).take 32 = wordBytes (32+gap.length) :=
    List.take_left' (word_length _)
  have hr : (wordBytes (32+gap.length) ++ (gap ++ (wordBytes bs.length ++ (bs ++ suffix)))).drop (32+gap.length) = wordBytes bs.length ++ (bs ++ suffix) := by
    rw [← List.append_assoc (wordBytes (32+gap.length)) gap]
    exact List.drop_left' (by rw [List.length_append,word_length])
  have hl : (wordBytes bs.length ++ (bs ++ suffix)).take 32 = wordBytes bs.length :=
    List.take_left' (word_length _)
  have hd : (wordBytes bs.length ++ (bs ++ suffix)).drop 32 = bs ++ suffix :=
    List.drop_left' (word_length _)
  have enoughHead : ¬ (wordBytes (32+gap.length) ++ (gap ++ (wordBytes bs.length ++ (bs ++ suffix)))).length < 32 := by
    simp only [List.length_append,word_length]
    omega
  have enoughLength : ¬ (wordBytes bs.length ++ (bs ++ suffix)).length < 32 := by
    simp only [List.length_append,word_length]
    omega
  simp only [decodeError,hs,ite_true,hb,ho,read_word _ hoff,hr,enoughHead,enoughLength,
    decide_false,Bool.false_or,Bool.false_eq_true,ite_false,hl,read_word _ hlen,hd,List.take_left]

/-- The published representation permits the offset word to double as an
empty length word. This is decoder behavior, not canonical encoding. -/
theorem zero_offset (suffix : List UInt8) :
    decodeError (errorSelector ++ wordBytes 0 ++ suffix) = some [] := by
  have hs : (errorSelector ++ wordBytes 0 ++ suffix).take 4 = errorSelector := by
    rw [List.append_assoc]
    exact List.take_left' (by decide)
  have hb : (errorSelector ++ wordBytes 0 ++ suffix).drop 4 = wordBytes 0 ++ suffix := by
    rw [List.append_assoc]
    exact List.drop_left' (by decide)
  have ho : (wordBytes 0 ++ suffix).take 32 = wordBytes 0 := List.take_left' (word_length _)
  have enough : ¬ (wordBytes 0 ++ suffix).length < 32 := by
    simp only [List.length_append,word_length]
    omega
  simp only [decodeError,hs,ite_true,hb,ho,read_word 0 (by decide),List.drop_zero,
    enough,decide_false,Bool.false_or,Bool.false_eq_true,ite_false,List.take_zero,List.length_nil]

/-- Actual terminal execution preserves all skipped gap bytes in the full
packet. Only the decoded reason is independent of those bytes. -/
theorem emitted (gap bs suffix : List UInt8) (address : Nat) (tail : Program)
    (machine : Slice.Machine)
    (fits : Fits address (errorSelector ++ wordBytes (32+gap.length) ++ gap ++ wordBytes bs.length ++ bs ++ suffix))
    (stack : machine.stack.length+2 ≤ 1024) :
    let data := errorSelector ++ wordBytes (32+gap.length) ++ gap ++ wordBytes bs.length ++ bs ++ suffix
    Slice.checkedRun (emit address (.custom data) ++ tail) machine =
      some ({machine with memory := Slice.putBytes machine.memory address data}, some (Roadmap.Outcome.revert data)) ∧
    Slice.getBytes (Slice.putBytes machine.memory address data) address data.length = data ∧
    decodeError (Slice.getBytes (Slice.putBytes machine.memory address data) address data.length) = some bs := by
  have size := fits.2.1
  simp only [List.length_append,errorSelector,List.length_cons,List.length_nil,word_length] at size
  have hoff : 32+gap.length < 256^32 := by change 32+gap.length < wordLimit; omega
  have hlen : bs.length < 256^32 := by change bs.length < wordLimit; omega
  refine ⟨checkedRun_emit_suffix address (.custom _) tail machine fits stack,Slice.getBytes_putBytes _ _ _,?_⟩
  rw [Slice.getBytes_putBytes]
  exact gap_readback gap bs suffix hoff hlen

end Solidity.Backend.AbiWorld.ErrorOffsetWindow

#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindow.gap_readback
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindow.zero_offset
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindow.emitted
#check Solidity.Backend.AbiWorld.ErrorOffsetWindow.emitted
