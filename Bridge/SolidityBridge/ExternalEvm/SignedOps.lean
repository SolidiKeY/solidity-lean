import SolidityBridge.ExternalEvm.WordOps
import Solidity.Evm.Signed

set_option maxRecDepth 2048

namespace Solidity.Evm.External

theorem signed_lt_bool (a b : Fin W) :
    decide (sgn a.val < sgn b.val) = EvmYul.UInt256.sltBool (encode a) (encode b) := by
  apply Bool.eq_iff_iff.mpr
  unfold EvmYul.UInt256.sltBool
  by_cases ha : H ≤ a.val <;> by_cases hb : H ≤ b.val
  all_goals
    simp only [encode, EvmYul.UInt256.toNat, show (2 : Nat)^255 = H from rfl,
      ha, hb, ↓reduceIte, decide_eq_true_eq]
  · change sgn a.val < sgn b.val ↔ a.val < b.val
    simp only [sgn, if_neg (by omega : ¬ a.val < H), if_neg (by omega : ¬ b.val < H)]
    omega
  · simp only [sgn, if_neg (by omega : ¬ a.val < H), if_pos (by omega : b.val < H)]
    have hn : (a.val : Int) - W < 0 := by omega
    exact ⟨fun _ => trivial, fun _ => lt_of_lt_of_le hn (Int.natCast_nonneg _)⟩
  · simp only [sgn, if_pos (by omega : a.val < H), if_neg (by omega : ¬ b.val < H)]
    constructor
    · intro h
      have hbW : b.val < W := b.isLt
      omega
    · intro h
      cases h
  · change sgn a.val < sgn b.val ↔ a.val < b.val
    simp only [sgn, if_pos (by omega : a.val < H), if_pos (by omega : b.val < H)]
    omega

theorem signed_gt_bool (a b : Fin W) :
    decide (sgn b.val < sgn a.val) = EvmYul.UInt256.sgtBool (encode a) (encode b) := by
  have h : EvmYul.UInt256.sgtBool (encode a) (encode b) =
      EvmYul.UInt256.sltBool (encode b) (encode a) := by
    unfold EvmYul.UInt256.sgtBool EvmYul.UInt256.sltBool
    split <;> split <;> rfl
  rw [h]
  exact signed_lt_bool b a

theorem slt_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.slt.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.slt (encode a) (encode b))) :: st) := by
  change m.next (.val (bword (decide (sgn a.val < sgn b.val))) :: st) = _
  rw [EvmYul.UInt256.slt, decode_bool, signed_lt_bool]

theorem sgt_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.sgt.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.sgt (encode a) (encode b))) :: st) := by
  change m.next (.val (bword (decide (sgn b.val < sgn a.val))) :: st) = _
  rw [EvmYul.UInt256.sgt, decode_bool, signed_gt_bool]

theorem signed_negative (a : Fin W) (ha : H ≤ a.val) :
    sgn a.val = -((W - a.val : Nat) : Int) := by
  rw [sgn, if_neg (by omega)]
  have hW : a.val ≤ W := Nat.le_of_lt a.isLt
  omega

private theorem reference_abs_word (u : EvmYul.UInt256) (ha : 2^255 ≤ u.toNat) :
    (EvmYul.UInt256.abs u).toNat = EvmYul.UInt256.size - u.toNat := by
  have hw : EvmYul.UInt256.abs u = ⟨-u.val⟩ := by
    calc
      _ = EvmYul.UInt256.mk (u.val * (-1)) := if_pos ha
      _ = EvmYul.UInt256.mk (-u.val) := congrArg EvmYul.UInt256.mk (mul_neg_one u.val)
  have hv : (EvmYul.UInt256.abs u).toNat = (-u.val).val := congrArg EvmYul.UInt256.toNat hw
  rw [hv, Fin.val_neg]
  have hz : u.val ≠ 0 := by
    intro h
    have he : u.toNat = 0 := congrArg Fin.val h
    have hp : 0 < (2 : Nat)^255 := Nat.pow_pos (by decide)
    omega
  rw [if_neg hz]
  rfl

theorem reference_abs_negative (a : Fin W) (ha : H ≤ a.val) :
    (EvmYul.UInt256.abs (encode a)).toNat = W - a.val := by
  calc
    _ = EvmYul.UInt256.size - (encode a).toNat := reference_abs_word _ ha
    _ = W - a.val := by rw [size_eq]; rfl

theorem sword_reference (u : EvmYul.UInt256) : sword (u.toNat : Int) = decode u := by
  apply Fin.ext
  have hu : u.toNat < W := (decode u).isLt
  rw [sword_val (by have := W_pos; omega) (by omega)]
  simp only [toWord, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
  rfl

private theorem sword_neg_value (q : Nat) (hq : q < W) :
    (sword (-(q : Int))).val = if q = 0 then 0 else W - q := by
  rw [sword_val (by omega) (by have := W_pos; omega)]
  by_cases hz : q = 0
  · rw [if_pos hz, hz]
    rfl
  · rw [if_neg hz]
    have hp : 0 < q := by omega
    unfold toWord
    rw [if_neg (by omega)]
    omega

private theorem decode_neg_value (u : EvmYul.UInt256) :
    (decode ⟨-u.val⟩).val = if u.toNat = 0 then 0 else W - u.toNat := by
  change (-u.val).val = _
  rw [Fin.val_neg]
  simp only [Fin.ext_iff, Fin.val_zero]
  change (if u.toNat = 0 then 0 else EvmYul.UInt256.size - u.toNat) = _
  rw [size_eq]

theorem sword_reference_neg (u : EvmYul.UInt256) :
    sword (-(u.toNat : Int)) = decode ⟨-u.val⟩ :=
  Fin.ext ((sword_neg_value u.toNat (decode u).isLt).trans (decode_neg_value u).symm)

private theorem reference_div_nat (u v : EvmYul.UInt256) :
    (EvmYul.UInt256.div u v).toNat = u.toNat / v.toNat := rfl

private theorem reference_div_zero (u : EvmYul.UInt256) :
    EvmYul.UInt256.div u (.ofNat 0) = .ofNat 0 := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change u.toNat / 0 = 0
  exact Nat.div_zero _

private theorem reference_sdiv_cases (u v : EvmYul.UInt256) :
    EvmYul.UInt256.sdiv u v =
      if 2^255 ≤ u.toNat then
        if 2^255 ≤ v.toNat then EvmYul.UInt256.div u.abs v.abs
        else ⟨-(EvmYul.UInt256.div u.abs v).val⟩
      else if 2^255 ≤ v.toNat then ⟨-(EvmYul.UInt256.div u v.abs).val⟩
      else EvmYul.UInt256.div u v := by
  unfold EvmYul.UInt256.sdiv
  split <;> split <;> first | rfl | exact congrArg EvmYul.UInt256.mk (mul_neg_one _)

private theorem reference_sdiv_zero (u : EvmYul.UInt256) :
    EvmYul.UInt256.sdiv u (.ofNat 0) = .ofNat 0 := by
  rw [reference_sdiv_cases]
  have hzero : ¬ 2^255 ≤ (EvmYul.UInt256.ofNat 0).toNat := by decide
  rw [if_neg hzero]
  split
  · rw [reference_div_zero]
    change EvmYul.UInt256.mk (-(0 : Fin EvmYul.UInt256.size)) = .ofNat 0
    rw [neg_zero]
    rfl
  · exact reference_div_zero u

theorem sdiv_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.sdiv.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.sdiv (encode a) (encode b))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  change (if b.val = 0 then ⟨0, W_pos⟩ else sword (Int.tdiv (sgn a.val) (sgn b.val))) = _
  by_cases hz : b.val = 0
  · have hb : b = ⟨0, W_pos⟩ := Fin.ext hz
    rw [if_pos hz, hb]
    change _ = decode (EvmYul.UInt256.sdiv (encode a) (.ofNat 0))
    rw [reference_sdiv_zero]
    rfl
  · rw [if_neg hz, reference_sdiv_cases]
    by_cases ha : H ≤ a.val <;> by_cases hb : H ≤ b.val
    · rw [if_pos (show 2^255 ≤ (encode a).toNat from ha),
        if_pos (show 2^255 ≤ (encode b).toNat from hb),
        signed_negative a ha, signed_negative b hb, Int.neg_tdiv_neg, ← Int.ofNat_tdiv]
      have hq : (EvmYul.UInt256.div (encode a).abs (encode b).abs).toNat =
          (W - a.val) / (W - b.val) := by
        rw [reference_div_nat, reference_abs_negative a ha, reference_abs_negative b hb]
      rw [← hq, sword_reference]
    · rw [if_pos (show 2^255 ≤ (encode a).toNat from ha),
        if_neg (show ¬ 2^255 ≤ (encode b).toNat from hb), signed_negative a ha,
        sgn, if_pos (show b.val < H by omega), Int.neg_tdiv, ← Int.ofNat_tdiv]
      have hq : (EvmYul.UInt256.div (encode a).abs (encode b)).toNat =
          (W - a.val) / b.val := by rw [reference_div_nat, reference_abs_negative a ha]; rfl
      rw [← hq, sword_reference_neg]
    · rw [if_neg (show ¬ 2^255 ≤ (encode a).toNat from ha),
        if_pos (show 2^255 ≤ (encode b).toNat from hb), signed_negative b hb,
        sgn, if_pos (show a.val < H by omega), Int.tdiv_neg, ← Int.ofNat_tdiv]
      have hq : (EvmYul.UInt256.div (encode a) (encode b).abs).toNat =
          a.val / (W - b.val) := by rw [reference_div_nat, reference_abs_negative b hb]; rfl
      rw [← hq, sword_reference_neg]
    · rw [if_neg (show ¬ 2^255 ≤ (encode a).toNat from ha),
        if_neg (show ¬ 2^255 ≤ (encode b).toNat from hb),
        sgn, if_pos (show a.val < H by omega), sgn, if_pos (show b.val < H by omega),
        ← Int.ofNat_tdiv]
      exact sword_reference (EvmYul.UInt256.div (encode a) (encode b))

private theorem reference_toSigned (z : Int) : decode (EvmYul.UInt256.toSigned z) = sword z := by
  apply Fin.ext
  cases z with
  | ofNat n =>
    change n % EvmYul.UInt256.size = (toWord (n : Int)) % W
    simp only [toWord, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, size_eq]
  | negSucc n =>
    change (EvmYul.UInt256.size - 1 - n) % EvmYul.UInt256.size = (toWord (Int.negSucc n)) % W
    unfold toWord
    rw [if_neg (by omega), size_eq]
    have hn : W - 1 - n = (Int.negSucc n + W).toNat := by omega
    rw [hn]

private theorem reference_abs_natAbs (a : Fin W) :
    (EvmYul.UInt256.abs (encode a)).toNat = (sgn a.val).natAbs := by
  by_cases ha : H ≤ a.val
  · rw [reference_abs_negative a ha, signed_negative a ha, Int.natAbs_neg, Int.natAbs_natCast]
  · rw [EvmYul.UInt256.abs, if_neg (show ¬ 2^255 ≤ (encode a).toNat from ha),
      sgn, if_pos (show a.val < H by omega)]
    rfl

private theorem reference_sign (a : Fin W) :
    EvmYul.UInt256.sgn (encode a) = Int.sign (sgn a.val) := by
  by_cases ha : H ≤ a.val
  · rw [EvmYul.UInt256.sgn, if_pos (show 2^255 ≤ (encode a).toNat from ha)]
    have hn : sgn a.val < 0 := by
      rw [signed_negative a ha]
      have hW : a.val < W := a.isLt
      omega
    rw [Int.sign_eq_neg_one_of_neg hn]
  · rw [EvmYul.UInt256.sgn, if_neg (show ¬ 2^255 ≤ (encode a).toNat from ha),
      sgn, if_pos (show a.val < H by omega)]
    by_cases hz : a.val = 0
    · have he : encode a = EvmYul.UInt256.ofNat 0 := by
        have haz : a = ⟨0, W_pos⟩ := Fin.ext hz
        rw [haz]
        rfl
      rw [he, hz]
      rfl
    · have hb : (encode a).eq0 = false := by
        change ((encode a).val == 0) = false
        apply Bool.eq_false_iff.mpr
        intro h
        exact hz (congrArg Fin.val (beq_iff_eq.mp h))
      rw [hb]
      exact (Int.sign_eq_one_of_pos (by omega)).symm

private theorem tmod_sign (x y : Int) :
    Int.tmod x y = Int.sign x * ((x.natAbs % y.natAbs : Nat) : Int) := by
  cases x with
  | ofNat n =>
    cases n with
    | zero =>
      change Int.tmod 0 y = (0 : Int) * _
      rw [Int.zero_tmod, zero_mul]
    | succ n =>
      change Int.tmod (Int.ofNat n.succ) y = (1 : Int) * _
      rw [one_mul]
      cases y <;> rfl
  | negSucc n =>
    change Int.tmod (-((n + 1 : Nat) : Int)) y = (-1 : Int) * _
    rw [Int.neg_tmod, neg_one_mul]
    cases y <;> rfl

private theorem reference_mod_nat (u v : EvmYul.UInt256) (hv : v.toNat ≠ 0) :
    (EvmYul.UInt256.mod u v).toNat = u.toNat % v.toNat := by
  have hzero : ¬ (v.val == 0) = true := by
    simpa only [beq_iff_eq, Fin.ext_iff, Fin.val_zero] using hv
  rw [EvmYul.UInt256.mod, if_neg hzero]
  rfl

theorem smod_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.smod.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.smod (encode a) (encode b))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  change (if b.val = 0 then ⟨0, W_pos⟩ else sword (Int.tmod (sgn a.val) (sgn b.val))) = _
  by_cases hz : b.val = 0
  · rw [if_pos hz, EvmYul.UInt256.smod, if_pos (show ((encode b).toNat == 0) = true from beq_iff_eq.mpr hz)]
    rfl
  · rw [if_neg hz, EvmYul.UInt256.smod,
      if_neg (show ¬ ((encode b).toNat == 0) = true from fun h => hz (beq_iff_eq.mp h)),
      reference_toSigned, tmod_sign, reference_sign]
    have hb : (EvmYul.UInt256.abs (encode b)).toNat ≠ 0 := by
      rw [reference_abs_natAbs]
      intro h
      exact hz ((sgn_eq_zero b.isLt).mp (Int.natAbs_eq_zero.mp h))
    change sword ((sgn a.val).sign * _) =
      sword ((sgn a.val).sign * ((EvmYul.UInt256.mod (encode a).abs (encode b).abs).toNat : Int))
    rw [reference_mod_nat _ _ hb, reference_abs_natAbs, reference_abs_natAbs]

end Solidity.Evm.External
