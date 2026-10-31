import Solidity.Backend.AbiWorld.ErrorRoundtrip
import Solidity.Backend.Failure.Correct
import Solidity.Semantics.Run

/-! Error-packet adapter to the published emitter and intrinsic catch decoder.
Slice execution excludes gas/expansion and whole-call simulation. -/
namespace Solidity.Backend.AbiWorld
open Failure

/-- Emit the actual published Error(string) bytes with a REVERT terminal. -/
def emitError (a : Nat) (reason : List UInt8) : Program := emit a (.reason reason)

/-- Actual straight-line execution returns exact bytes and leaves the stack.
Fits and two free stack cells are architectural prerequisites. -/
theorem execute_error (a : Nat) (reason : List UInt8) (suffix : Program)
    (s : Slice.Machine) (hf : Fits a (Semantics.encodeError reason))
    (hs : s.stack.length + 2 ≤ 1024) :
    Slice.checkedRun (emitError a reason ++ suffix) s =
      some ({ s with memory := Slice.putBytes s.memory a (Semantics.encodeError reason) },
        some (.revert (Semantics.encodeError reason))) :=
  checkedRun_emit_suffix a (.reason reason) suffix s hf hs

/-- Actual intrinsic reason-catch dispatch decodes every representable reason. -/
theorem catch_error (reason : List UInt8) (hlen : reason.length < 256 ^ 32) :
    CatchKind.reason.decode (Semantics.encodeError reason) = some reason := by
  have h : reason.length < 2 ^ 256 := by simpa using hlen
  simp only [CatchKind.decode, error_roundtrip reason hlen, Option.filter_some,
    decide_eq_true h, ite_true]

/-- Every intrinsic uint256 Panic code roundtrips at its original type. -/
theorem panic_roundtrip (code : Semantics.Word) :
    Semantics.decodePanic (Semantics.encodePanic code.1.toNat) = some code := by
  have hc : 0 ≤ code.1 ∧ code.1 < ((2 ^ 256 : Nat) : Int) :=
    of_decide_eq_true code.2
  have hn : code.1.toNat < 2 ^ 256 := (Int.toNat_lt hc.1).2 hc.2
  have hr : Semantics.bytesNat (Semantics.wordBytes code.1.toNat) = code.1.toNat :=
    read_word _ (by simpa using hn)
  have hs : (Semantics.encodePanic code.1.toNat).take 4 = Semantics.panicSelector :=
    List.take_left' (by decide)
  have hd : (Semantics.encodePanic code.1.toNat).drop 4 = Semantics.wordBytes code.1.toNat :=
    List.drop_left' (by decide)
  have hl : (Semantics.encodePanic code.1.toNat).length = 36 := by
    simp only [Semantics.encodePanic, List.length_append, Semantics.panicSelector,
      List.length_cons, List.length_nil, word_length]
  have ht : (Semantics.wordBytes code.1.toNat).take 32 = Semantics.wordBytes code.1.toNat :=
    List.take_of_length_le (by rw [word_length]; exact Nat.le_refl _)
  simp only [Semantics.decodePanic, hs, hl, Nat.le_refl, and_self, ite_true, hd, ht, hr, dif_pos hn]
  apply congrArg some
  apply Subtype.ext
  exact Int.toNat_of_nonneg hc.1

/-- Catch-all preserves the exact packet when it is representable as an array. -/
theorem catch_raw (packet : List UInt8) (hlen : packet.length < 2 ^ 256) :
    CatchKind.raw.decode packet = some packet := by
  simp only [CatchKind.decode, hlen, ite_true]

/-- info: 'Solidity.Backend.AbiWorld.panic_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms panic_roundtrip

/-- info: 'Solidity.Backend.AbiWorld.execute_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_error
/-- info: 'Solidity.Backend.AbiWorld.catch_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms catch_error
end Solidity.Backend.AbiWorld
