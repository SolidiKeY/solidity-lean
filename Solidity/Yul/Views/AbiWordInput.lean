import Solidity.Yul.Views.ObjectMemoryAllocation
import Solidity.Yul.Views.Inputs

namespace Solidity.Yul.Views

/-- The actual ABI reader is word bounded because fitBytes has EXACTLY32
bytes, including zero padding. No canonical offset/alignment condition. -/
theorem abi_wordAt_bound (input : Roadmap.Bytes) (i : Nat) : Source.wordAt input i < 2^256 := by
  have bound := scalar_beValue_bound (Source.fitBytes 32 (input.drop (32*i)))
  rw [Source.fitBytes_length] at bound
  change Source.beValue (Source.fitBytes 32 (input.drop (32*i))) < 2^256
  exact bound

def abiInputWord (input : Roadmap.Bytes) (i : Nat) : Roadmap.Word :=
  ⟨Source.wordAt input i,abi_wordAt_bound input i⟩

/-- Canonical ABI uint256 decoding from an ACTUAL bounded word. Reuses owner
readInt and mkInt; no alternate signed/unsigned interpretation. -/
theorem abi_decode_uint_word (D : Source.Layout) (w : Roadmap.Word) :
    Source.decodeWord D w.val (.int Source.IntTy.u256)=.ok (uintValueOfWord D w) := by
  have range : Source.IntTy.u256.lo≤(w.val : Int) ∧ (w.val : Int)≤Source.IntTy.u256.hi := by
    have bound := w.isLt
    change 0≤(w.val : Int) ∧ (w.val : Int)≤(2^256 : Nat)-1
    omega
  have inverse := Source.Val.word_int (D := D) (t := Source.IntTy.u256) (w.val : Int) range
  change (uintValueOfWord D w).word.bind (Source.readInt Source.IntTy.u256)=some (w.val : Int) at inverse
  rw [uintValueOfWord_word] at inverse
  have same : Source.toWord w.val=w := Fin.ext (Nat.mod_eq_of_lt w.isLt)
  change (match Source.readInt Source.IntTy.u256 (Source.toWord w.val) with
    | some value => Source.mkInt Source.IntTy.u256 value
    | none => .error (.revert []))=.ok (uintValueOfWord D w)
  change Source.readInt Source.IntTy.u256 w=some (w.val : Int) at inverse
  rw [same,inverse]
  change Source.mkInt Source.IntTy.u256 (w.val : Int)=.ok (uintValueOfWord D w)
  unfold Source.mkInt
  rw [dif_pos range]
  rfl

/-- The source ABI word reader is used directly; high bits are neither
truncated nor cleaned when interpreting a uint256 ABI element. -/
theorem abi_decode_uint_input (D : Source.Layout) (input : Roadmap.Bytes) (i : Nat) :
    Source.decodeWord D (Source.wordAt input i) (.int Source.IntTy.u256)=.ok (uintValueOfWord D (abiInputWord input i)) :=
  abi_decode_uint_word D (abiInputWord input i)

end Solidity.Yul.Views
