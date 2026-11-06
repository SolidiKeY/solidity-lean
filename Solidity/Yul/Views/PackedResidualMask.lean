import Solidity.Yul.Views.FiniteResidual

/-! Complement bytes derive from actual Field ranges. All eight bits of a
registered byte are owned; dirty bits INSIDE a canonical field remain an open
representation obligation, never reclassified as residual or cleaned. -/
namespace Solidity.Yul.Views

def packedOwnsByte {D L} (cs : List (ScalarPath D L)) (slot : Roadmap.Word) (i : Fin 32) : Bool :=
  cs.any (fun c => decide (c.slot = slot ∧ c.field.offset ≤ i.val ∧ i.val < c.field.offset+c.field.width))

theorem packedOwnsByte_iff {D L} (cs : List (ScalarPath D L)) (slot : Roadmap.Word) (i : Fin 32) :
    packedOwnsByte cs slot i = true ↔ ∃ c ∈ cs, c.slot = slot ∧ c.field.offset ≤ i.val ∧ i.val < c.field.offset+c.field.width := by
  simp only [packedOwnsByte,List.any_eq_true,decide_eq_true_eq]

def lowByte (w : Roadmap.Word) (i : Fin 32) : UInt8 := wordByte w (reverseByteIndex 32 i)

def wordFromLowBytes (bs : Fin 32 → UInt8) : Roadmap.Word :=
  mload (fun j => bs ⟨31-j%32,by have := Nat.mod_lt j (by decide : 0 < 32); omega⟩) 0

theorem lowByte_wordFrom (bs : Fin 32 → UInt8) (i : Fin 32) : lowByte (wordFromLowBytes bs) i = bs i := by
  rw [lowByte,wordFromLowBytes,wordByte_mload]
  congr 1
  apply Fin.ext
  simp only [reverseByteIndex,Nat.zero_add]
  have hi := i.isLt
  rw [Nat.mod_eq_of_lt (show 31-i.val < 32 by omega)]
  omega

theorem word_eq_of_lowBytes (a b : Roadmap.Word) (same : ∀ i, lowByte a i = lowByte b i) : a = b := by
  calc
    a = mload (mstore (fun _ => 0) 0 a) 0 := (mload_mstore _ _ _).symm
    _ = mload (mstore (fun _ => 0) 0 b) 0 := by
      apply mload_congr
      intro i
      rw [find_mstore,find_mstore]
      have eq := same (reverseByteIndex 32 i)
      have rev : reverseByteIndex 32 (reverseByteIndex 32 i) = i := by
        apply Fin.ext
        simp only [reverseByteIndex]
        have hi := i.isLt
        omega
      simpa only [lowByte,rev] using eq
    _ = b := mload_mstore _ _ _

def complementWord (owns : Fin 32 → Bool) (raw : Roadmap.Word) : Roadmap.Word :=
  wordFromLowBytes (fun i => if owns i then 0 else lowByte raw i)

theorem complementWord_byte (owns : Fin 32 → Bool) (raw : Roadmap.Word) (i : Fin 32) :
    lowByte (complementWord owns raw) i = if owns i then 0 else lowByte raw i := lowByte_wordFrom _ _

def packedMask {D L} (cs : List (ScalarPath D L)) (m : SlotView) : SlotView :=
  fun slot => complementWord (packedOwnsByte cs slot) (m slot)

theorem packedMask_residual {D L} (cs : List (ScalarPath D L)) (m : SlotView) (q : Roadmap.Word) (i : Fin 32)
    (unowned : packedOwnsByte cs q i = false) : lowByte (packedMask cs m q) i = lowByte (m q) i := by
  rw [packedMask,complementWord_byte,unowned]
  rfl

theorem packedMask_owned_zero {D L} (cs : List (ScalarPath D L)) (m : SlotView) (q : Roadmap.Word) (i : Fin 32)
    (owned : packedOwnsByte cs q i = true) : lowByte (packedMask cs m q) i = 0 := by
  rw [packedMask,complementWord_byte,owned]
  rfl

/-- An existing field's exact payload determines every byte it actually owns. -/
theorem Field.lowByte_of_find (f : Field) (a b : Roadmap.Word) (same : f.findWord a = f.findWord b)
    (i : Fin 32) (inside : f.offset ≤ i.val ∧ i.val < f.offset+f.width) : lowByte a i = lowByte b i := by
  let j := i.val-f.offset
  have sum : f.offset+j = i.val := by dsimp only [j]; omega
  have jlt : j+1 ≤ f.width := by dsimp only [j]; omega
  have factor : 256^f.width = 256^j*(256*256^(f.width-(j+1))) := by
    rw [← Nat.pow_succ',← Nat.pow_add]
    congr 1
    omega
  have observe (x : Nat) : f.find x / 256^j % 256 = x / 256^i.val % 256 := by
    unfold Field.find Field.base Field.modulus
    rw [factor,Nat.mod_mul_right_div_self,Nat.mod_mul_right_mod,Nat.div_div_eq_div_mul,← Nat.pow_add,sum]
  have payload := congrArg Fin.val same
  have eq := congrArg (fun x => x / 256^j % 256) payload
  change f.find a.val / 256^j % 256 = f.find b.val / 256^j % 256 at eq
  rw [observe,observe] at eq
  apply UInt8.toNat_inj.mp
  have rev : 31-(31-i.val) = i.val := by have hi := i.isLt; omega
  simpa only [lowByte,wordByte,reverseByteIndex,rev,UInt8.toNat_ofNat'] using eq

end Solidity.Yul.Views
