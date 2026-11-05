import Solidity.Backend.AbiWorld.ErrorRoundtrip
import Solidity.Backend.Failure.Correct
import Solidity.Semantics.RevertData

/-! Generic full-word Panic decoding and real constant-packet terminal emission.
No source profile, decoder or runtime-memory encoder is introduced. -/
namespace Solidity.Backend.AbiWorld.PanicReadWindow
open Semantics Failure

def word (n : Nat) (hn : n < 2^256) : Semantics.Word :=
  ⟨n, PrimTy.inRange_uint_of_lt hn⟩

theorem decode (n : Nat) (hn : n < 2^256) (suffix : List UInt8) :
    decodePanic (encodePanic n ++ suffix) = some (word n hn) := by
  have hs : (encodePanic n ++ suffix).take 4 = panicSelector := by
    simp only [encodePanic,List.append_assoc]
    exact List.take_left' (by decide)
  have hb : (encodePanic n ++ suffix).drop 4 = wordBytes n ++ suffix := by
    simp only [encodePanic,List.append_assoc]
    exact List.drop_left' (by decide)
  have hw : (wordBytes n ++ suffix).take 32 = wordBytes n := List.take_left' (word_length _)
  have hl : 36 ≤ (encodePanic n ++ suffix).length := by
    simp only [encodePanic,List.length_append,panicSelector,List.length_cons,List.length_nil,word_length]
    omega
  simp only [decodePanic,hs,hl,and_self,ite_true,hb,hw,read_word n hn,dif_pos hn,word]

/-- Panic packets cannot select the preceding Error decoder branch. -/
theorem error_reject (n : Nat) (suffix : List UInt8) :
    decodeError (encodePanic n ++ suffix) = none := by
  have hs : (encodePanic n ++ suffix).take 4 = panicSelector := by
    simp only [encodePanic,List.append_assoc]
    exact List.take_left' (by decide)
  have different : panicSelector ≠ errorSelector := by decide
  simp only [decodeError,hs,different,ite_false]

/-- The published Panic emitter returns the exact full word; no ByteRange
premise is imposed on the code. This is not an unknown-memory encoder. -/
theorem emitted (n : Fin wordLimit) (address : Nat) (tail : Program)
    (machine : Slice.Machine) (fits : Fits address (encodePanic n.val))
    (stack : machine.stack.length+2 ≤ 1024) :
    Slice.checkedRun (emit address (.panic n) ++ tail) machine =
      some ({machine with memory := Slice.putBytes machine.memory address (encodePanic n.val)},
        some (Roadmap.Outcome.revert (encodePanic n.val))) ∧
    decodePanic (Slice.getBytes (Slice.putBytes machine.memory address (encodePanic n.val)) address 36) =
      some (word n.val n.isLt) := by
  have hl : (encodePanic n.val).length = 36 := panic_length n
  refine ⟨checkedRun_emit_suffix address (.panic n) tail machine fits stack,?_⟩
  rw [← hl,Slice.getBytes_putBytes]
  simpa only [List.append_nil] using decode n.val n.isLt []

end Solidity.Backend.AbiWorld.PanicReadWindow
#print axioms Solidity.Backend.AbiWorld.PanicReadWindow.decode
#print axioms Solidity.Backend.AbiWorld.PanicReadWindow.error_reject
#print axioms Solidity.Backend.AbiWorld.PanicReadWindow.emitted
