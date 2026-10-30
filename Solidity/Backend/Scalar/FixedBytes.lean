import Solidity.Backend.Scalar.Shifts
import Solidity.Backend.Scalar.CastChains

/-! Fixed-bytes payloads use the existing intrinsic uint carrier in its low
bits. Resizing preserves byte-string order: widening pads on the right and
narrowing drops the rightmost bytes. ABI left alignment is a separate layer. -/
namespace Solidity.Backend.Scalar

def bytesResizeNat (src dst : Fin 32) (a : Nat) : Nat :=
  if widthBits src ≤ widthBits dst then a * 2^(widthBits dst-widthBits src)
  else a / 2^(widthBits src-widthBits dst)

def bytesResize (src dst : Fin 32) (a : Word) : Word :=
  BitVec.ofNat 256 (bytesResizeNat src dst a.toNat)

def bytesResizeCode (src dst : Fin 32) : Program :=
  if widthBits src ≤ widthBits dst then
    [pushWord (BitVec.ofNat 256 (widthBits dst-widthBits src)), .op .SHL]
  else [pushWord (BitVec.ofNat 256 (widthBits src-widthBits dst)), .op .SHR]

theorem bytesResize_correct (src dst : Fin 32) (a : Word) (tail : Stack) :
    run (bytesResizeCode src dst) (a::tail) = some (bytesResize src dst a::tail) := by
  have hf := widthBits_bounds src
  have ht := widthBits_bounds dst
  by_cases hw : widthBits src ≤ widthBits dst
  · rw [bytesResizeCode, if_pos hw, run, step_pushWord]
    change some ((if (BitVec.ofNat 256 (widthBits dst-widthBits src)).toNat<256
      then a <<< (BitVec.ofNat 256 (widthBits dst-widthBits src)).toNat else 0)::tail) = _
    have hn : widthBits dst-widthBits src<256 := by omega
    have hnW : widthBits dst-widthBits src<2^256 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnW, hn, if_true,
      shiftLeft_word, bytesResize, bytesResizeNat, hw]
  · rw [bytesResizeCode, if_neg hw, run, step_pushWord]
    change some ((if (BitVec.ofNat 256 (widthBits src-widthBits dst)).toNat<256
      then a >>> (BitVec.ofNat 256 (widthBits src-widthBits dst)).toNat else 0)::tail) = _
    have hn : widthBits src-widthBits dst<256 := by omega
    have hnW : widthBits src-widthBits dst<2^256 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnW, hn, if_true,
      bytesResize, bytesResizeNat, hw, if_false]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    have hq := Nat.lt_of_le_of_lt (Nat.div_le_self a.toNat (2^(widthBits src-widthBits dst))) a.isLt
    exact (Nat.mod_eq_of_lt hq).symm

theorem bytesResize_range (src dst : Fin 32) (a : Nat) (ha : a<2^widthBits src) :
    bytesResizeNat src dst a < 2^widthBits dst := by
  unfold bytesResizeNat
  split
  · rename_i hw
    have he : widthBits dst = widthBits src+(widthBits dst-widthBits src) := by omega
    conv => rhs; rw [he, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right ha (Nat.pow_pos (by decide : 0<2))
  · rename_i hw
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0<2))).mpr
    rw [← Nat.pow_add]
    have he : widthBits dst+(widthBits src-widthBits dst)=widthBits src := by omega
    rw [he]
    exact ha

theorem bytesResize_nat (src dst : Fin 32) (a : Word) (ha : a.toNat<2^widthBits src) :
    (bytesResize src dst a).toNat = bytesResizeNat src dst a.toNat := by
  have hb := bytesResize_range src dst a.toNat ha
  have hW := Nat.pow_le_pow_right (by decide : 0<2) (widthBits_bounds dst).2
  simp only [bytesResize, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hW)]

example : run (bytesResizeCode ⟨0, by decide⟩ ⟨1, by decide⟩) [0xab, 99] =
    some [0xab00, 99] := by decide +kernel
example : run (bytesResizeCode ⟨1, by decide⟩ ⟨0, by decide⟩) [0xabcd, 99] =
    some [0xab, 99] := by decide +kernel
example : bytesResize ⟨0, by decide⟩ ⟨1, by decide⟩ 0xab ≠ 0xab := by decide +kernel


/-- A shift-count literal in the existing intrinsic uint type. -/
def widthShift (a b : Fin 32) : PrimTy.uint.Denote :=
  ⟨((widthBits a-widthBits b : Nat) : Int), by
    have ha := widthBits_bounds a
    have hb := widthBits_bounds b
    simp only [PrimTy.inRange, decide_eq_true_eq]
    constructor
    · exact Int.natCast_nonneg _
    · omega⟩

theorem widthShift_word (a b : Fin 32) :
    encodeValue .uint (widthShift a b) = BitVec.ofNat 256 (widthBits a-widthBits b) := by
  exact BitVec.ofInt_natCast 256 _

theorem bytesWiden_intrinsic (src dst : Fin 32) (hw : widthBits src ≤ widthBits dst)
    (a : PrimTy.uint.Denote) (tail : Stack) :
    run (bytesResizeCode src dst) (encodeValue .uint a::tail) =
      (BinOp.evalT .shl (p := .uint) rfl a (widthShift dst src)).map
        (fun v => encodeValue .uint v::tail) := by
  have he : run (bytesResizeCode src dst) (encodeValue .uint a::tail) =
      run uintShl.code (encodeValue .uint a::encodeValue .uint (widthShift dst src)::tail) := by
    rw [bytesResizeCode, if_pos hw, run, step_pushWord, widthShift_word]
    rfl
  rw [he]
  exact uintShl.correct a (widthShift dst src) tail

theorem bytesNarrow_intrinsic (src dst : Fin 32) (hw : ¬ widthBits src ≤ widthBits dst)
    (a : PrimTy.uint.Denote) (tail : Stack) :
    run (bytesResizeCode src dst) (encodeValue .uint a::tail) =
      (BinOp.evalT .shr (p := .uint) rfl a (widthShift src dst)).map
        (fun v => encodeValue .uint v::tail) := by
  have he : run (bytesResizeCode src dst) (encodeValue .uint a::tail) =
      run uintShr.code (encodeValue .uint a::encodeValue .uint (widthShift src dst)::tail) := by
    rw [bytesResizeCode, if_neg hw, run, step_pushWord, widthShift_word]
    rfl
  rw [he]
  exact uintShr.correct a (widthShift src dst) tail


theorem bytesResize_roundtrip (src dst : Fin 32) (a : Word)
    (hw : widthBits src ≤ widthBits dst) (ha : a.toNat<2^widthBits src) :
    bytesResize dst src (bytesResize src dst a) = a := by
  have hwide : (bytesResize src dst a).toNat<2^widthBits dst := by
    rw [bytesResize_nat src dst a ha]
    exact bytesResize_range src dst a.toNat ha
  apply BitVec.eq_of_toNat_eq
  rw [bytesResize_nat dst src _ hwide, bytesResize_nat src dst a ha]
  unfold bytesResizeNat
  rw [if_pos hw]
  by_cases hr : widthBits dst ≤ widthBits src
  · have he : widthBits dst=widthBits src := Nat.le_antisymm hr hw
    simp only [he, Nat.le_refl, if_true, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
  · rw [if_neg hr, Nat.mul_div_left _ (Nat.pow_pos (by decide : 0<2))]

example : bytesResize ⟨0, by decide⟩ ⟨1, by decide⟩
    (bytesResize ⟨1, by decide⟩ ⟨0, by decide⟩ 0xabcd) ≠ 0xabcd := by decide +kernel

#print axioms bytesResize_roundtrip

#print axioms bytesWiden_intrinsic
#print axioms bytesNarrow_intrinsic

#print axioms bytesResize_correct
#print axioms bytesResize_range
end Solidity.Backend.Scalar
