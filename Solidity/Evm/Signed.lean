import Solidity.Evm.Compile

/-!
# Signed words

An `int256` lives in a word as its two's complement (`toWord`), and the word
reads back as the value (`sgn`).  This file proves the signed guard
sequences of `Compile.lean` (`sTail`, `negCode`) exact: each computes the
word of the interpreter's checked result, or reverts exactly when the
result leaves `[-2^255, 2^255)` (or divides by zero), as solc's
`checked_add_t_int256` and its siblings do.

The arithmetic is linear once the words are split at `2^255`, except for
`*`, whose check divides the wrapped product back (`smul_ok_iff`): the
remainder of a truncated division is smaller than the divisor, and a wrapped
product is off by a multiple of `2^256`, which no divisor below `2^255`
hides.
-/

namespace Solidity
namespace Evm

/-! ## Words and their signed reading -/

theorem H_pos : 0 < H := Nat.pow_pos (by decide)

/-- A word's signed reading is an `int256`. -/
theorem sgn_range {a : Nat} (ha : a < W) : -(H : Int) ≤ sgn a ∧ sgn a < H := by
  have := W_eq; unfold sgn; split <;> omega

/-- The word of a signed reading is the word. -/
theorem toWord_sgn {a : Nat} (ha : a < W) : toWord (sgn a) = a := by
  have := W_eq; unfold sgn toWord; split <;> split <;> omega

/-- An `int256` reads back from its word. -/
theorem sgn_toWord {n : Int} (h1 : -(H : Int) ≤ n) (h2 : n < H) : sgn (toWord n) = n := by
  have := W_eq; unfold sgn toWord; split <;> split <;> omega

/-- The word of an integer in `[-2^256, 2^256)` is a word. -/
theorem toWord_lt {n : Int} (h1 : -(W : Int) ≤ n) (h2 : n < W) : toWord n < W := by
  unfold toWord; split <;> omega

/-- Two words with the same signed reading are the same word. -/
theorem sgn_inj {a b : Nat} (ha : a < W) (hb : b < W) (h : sgn a = sgn b) : a = b := by
  rw [← toWord_sgn ha, ← toWord_sgn hb, h]

/-- Comparison words are equal exactly when the comparisons are. -/
@[simp] theorem bword_eq_bword (p q : Bool) : (bword p = bword q) = (p = q) := by
  cases p <;> cases q <;> decide

/-- A comparison's word is `0` exactly when it is false: `3 < 2` pushes `0`. -/
@[simp] theorem bword_eq_zero (b : Bool) : bword b = 0 ↔ b = false := by cases b <;> decide

/-- A sum of two words wraps at most once. -/
theorem modW {x : Nat} (h : x < W + W) : x % W = if x < W then x else x - W := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The arithmetic of solc's signed `+` check: the wrapped sum is below `y`
exactly when `x` is negative, unless the sum overflows. -/
theorem sadd_ok {a b : Nat} (ha : a < W) (hb : b < W) :
    ((sgn a < 0 ↔ sgn ((b + a) % W) < sgn b) ↔
      (-(H : Int) ≤ sgn a + sgn b ∧ sgn a + sgn b < H)) ∧
    ((-(H : Int) ≤ sgn a + sgn b ∧ sgn a + sgn b < H) → (b + a) % W = toWord (sgn a + sgn b)) := by
  have hW := W_eq
  rw [modW (by omega)]
  unfold sgn toWord
  by_cases h1 : a < H <;> by_cases h2 : b < H <;> by_cases h3 : b + a < W <;>
    simp only [h1, h2, h3, if_true, if_false] <;> (refine ⟨?_, ?_⟩) <;> (repeat' split) <;>
    (try simp) <;> omega

/-! ## The guard sequences -/

theorem sadd_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (sTail .add) { m with stack := .val b :: .val a :: st } =
      if -(H : Int) ≤ sgn a + sgn b ∧ sgn a + sgn b < H then
        .ok { m with stack := .val (toWord (sgn a + sgn b)) :: st } 0
      else .revert := by
  obtain ⟨k1, k2⟩ := sadd_ok ha hb
  simp [run, sTail, assertTop, Instr.step, Machine.next]
  by_cases h : -(H : Int) ≤ sgn a + sgn b ∧ sgn a + sgn b < H
  · rw [if_pos (k1.2 h), if_pos h, ← k2 h]; rfl
  · rw [if_neg (fun e => h (k1.1 e)), if_neg h]; rfl

/-- The arithmetic of solc's signed `-` check. -/
theorem ssub_ok {a b : Nat} (ha : a < W) (hb : b < W) :
    ((sgn b < 0 ↔ sgn a < sgn ((a + (W - b)) % W)) ↔
      (-(H : Int) ≤ sgn a - sgn b ∧ sgn a - sgn b < H)) ∧
    ((-(H : Int) ≤ sgn a - sgn b ∧ sgn a - sgn b < H) →
      (a + (W - b)) % W = toWord (sgn a - sgn b)) := by
  have hW := W_eq
  rw [modW (by omega)]
  unfold sgn toWord
  by_cases h1 : a < H <;> by_cases h2 : b < H <;> by_cases h3 : a + (W - b) < W <;>
    simp only [h1, h2, h3, if_true, if_false] <;> (refine ⟨?_, ?_⟩) <;> (repeat' split) <;>
    (try simp) <;> omega

theorem ssub_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (sTail .sub) { m with stack := .val b :: .val a :: st } =
      if -(H : Int) ≤ sgn a - sgn b ∧ sgn a - sgn b < H then
        .ok { m with stack := .val (toWord (sgn a - sgn b)) :: st } 0
      else .revert := by
  obtain ⟨k1, k2⟩ := ssub_ok ha hb
  simp [run, sTail, assertTop, Instr.step, Machine.next]
  by_cases h : -(H : Int) ≤ sgn a - sgn b ∧ sgn a - sgn b < H
  · rw [if_pos (k1.2 h), if_pos h, ← k2 h]; rfl
  · rw [if_neg (fun e => h (k1.1 e)), if_neg h]; rfl

/-- `AND` of two comparison words is the conjunction's word. -/
@[simp] theorem bword_and (p q : Bool) : (bword p &&& bword q) = bword (p && q) := by
  cases p <;> cases q <;> decide

/-- `OR` of two comparison words is the disjunction's word. -/
@[simp] theorem bword_or (p q : Bool) : (bword p ||| bword q) = bword (p || q) := by
  cases p <;> cases q <;> decide

/-- A word is `0` exactly when it reads as `0`. -/
theorem sgn_eq_zero {a : Nat} (ha : a < W) : sgn a = 0 ↔ a = 0 := by
  have := W_eq; unfold sgn; split <;> omega

/-- `x / y` on `int`s: revert on a zero divisor (`Panic(0x12)`) and on
`-2^255 / -1` (`Panic(0x11)`), else `SDIV`. -/
theorem sdiv_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (sTail .div) { m with stack := .val b :: .val a :: st } =
      if b = 0 then .revert
      else if a = H ∧ b = W - 1 then .revert
      else .ok { m with stack := .val (toWord (Int.tdiv (sgn a) (sgn b))) :: st } 0 := by
  by_cases h0 : b = 0
  · subst h0; simp [run, sTail, assertTop, Instr.step, Machine.next]
  · simp [run, sTail, assertTop, Instr.step, Machine.next, h0]
    by_cases h1 : a = H ∧ b = W - 1
    · rw [if_pos ⟨h1.2, h1.1⟩, if_pos h1]; rfl
    · rw [if_neg (fun h => h1 ⟨h.2, h.1⟩), if_neg h1]
      simp [Instr.step, Machine.next, h0]

/-- `x % y` on `int`s: revert on a zero divisor, else `SMOD`. -/
theorem smod_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (sTail .mod) { m with stack := .val b :: .val a :: st } =
      if b = 0 then .revert
      else .ok { m with stack := .val (toWord (Int.tmod (sgn a) (sgn b))) :: st } 0 := by
  by_cases h0 : b = 0
  · subst h0; rfl
  · simp [run, sTail, assertTop, Instr.step, Machine.next, h0]

/-- The signed comparisons: one or two instructions and no guard. -/
theorem scmp_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (sTail .lt) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (sgn a < sgn b))) :: st } 0 ∧
    run (sTail .gt) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (sgn b < sgn a))) :: st } 0 ∧
    run (sTail .le) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (sgn a ≤ sgn b))) :: st } 0 ∧
    run (sTail .ge) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (sgn b ≤ sgn a))) :: st } 0 ∧
    run (sTail .eqB) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (a = b))) :: st } 0 ∧
    run (sTail .neB) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (!decide (a = b))) :: st } 0 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [run, sTail, Instr.step, Machine.next, bword]
  · simp [run, sTail, Instr.step, Machine.next, bword]
  · simp [run, sTail, Instr.step, Machine.next, bword]
    by_cases h : a = b <;> simp [h, eq_comm]
  · simp [run, sTail, Instr.step, Machine.next, bword]
    by_cases h : a = b <;> simp [h, eq_comm]

/-- `-x` on `int`s: revert on `-2^255`, else `0 - x`. -/
theorem neg_run (m : Machine) (st : List Word) {a : Nat} (ha : a < W) :
    run negCode { m with stack := .val a :: st } =
      if -(H : Int) ≤ -sgn a ∧ -sgn a < H then
        .ok { m with stack := .val (toWord (-sgn a)) :: st } 0
      else .revert := by
  have hW := W_eq
  have e : (0 + (W - a)) % W = toWord (-sgn a) := by
    rw [modW (by omega)]; unfold sgn toWord; (repeat' split) <;> omega
  by_cases h : a = H
  · subst h
    have : ¬ (-(H : Int) ≤ -sgn H ∧ -sgn H < H) := by unfold sgn; simp; omega
    rw [if_neg this]
    simp [run, negCode, assertTop, Instr.step, Machine.next]
  · have : -(H : Int) ≤ -sgn a ∧ -sgn a < H := by unfold sgn; split <;> omega
    rw [if_pos this]
    simp [run, negCode, assertTop, Instr.step, Machine.next, Ne.symm h]
    simpa using e

/-! ## Signed division and multiplication -/

/-- `x / y` leaves `int256` only at `-2^255 / -1`. -/
theorem tdiv_range {x y : Int} (hx : -(H : Int) ≤ x ∧ x < H) (hy : y ≠ 0) :
    (-(H : Int) ≤ x.tdiv y ∧ x.tdiv y < H) ↔ ¬ (x = -H ∧ y = -1) := by
  have e := Int.natAbs_tdiv x y
  have hH := H_pos
  constructor
  · rintro ⟨_, h2⟩ ⟨rfl, rfl⟩
    rw [show (-1 : Int) = -1 from rfl, Int.tdiv_neg, Int.neg_tdiv, Int.tdiv_one] at h2
    omega
  · intro hn
    by_cases h1 : y.natAbs = 1
    · rcases (show y = 1 ∨ y = -1 by omega) with rfl | rfl
      · rw [Int.tdiv_one]; omega
      · rw [Int.tdiv_neg, Int.tdiv_one]; omega
    · have h2 : x.natAbs / y.natAbs ≤ x.natAbs / 2 := Nat.div_le_div_left (by omega) (by decide)
      change _ = x.natAbs / y.natAbs at e
      omega

/-- `x % y` stays in `int256`. -/
theorem tmod_range {x y : Int} (hy : -(H : Int) ≤ y ∧ y < H) (hy0 : y ≠ 0) :
    -(H : Int) ≤ x.tmod y ∧ x.tmod y < H := by
  have e := Int.natAbs_tmod x y
  have := Nat.mod_lt x.natAbs (show 0 < y.natAbs by omega)
  omega

/-- A wrapped product reads as the product, up to a multiple of `2^256`. -/
theorem sgn_mul_congr {a b : Nat} (ha : a < W) (hb : b < W) :
    ∃ k : Int, sgn (b * a % W) = sgn a * sgn b + W * k := by
  have hW := W_eq
  have ew : ∀ c : Nat, c < W → (c : Int) % W = sgn c % W := fun c hc => by
    unfold sgn; split
    · rfl
    · rw [show (c : Int) - W = c + (-1) * W by omega, Int.add_mul_emod_self_right]
  have hp : b * a % W < W := Nat.mod_lt _ W_pos
  have h1 : sgn (b * a % W) % W = (sgn a * sgn b) % W := by
    rw [← ew _ hp, Int.natCast_emod, Int.emod_emod, Int.natCast_mul, Int.mul_emod, ew _ ha,
      ew _ hb, ← Int.mul_emod, Int.mul_comm]
  have h2 : (sgn (b * a % W) - sgn a * sgn b) % W = 0 := by
    rw [Int.sub_emod, h1, Int.sub_self, Int.zero_emod]
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h2
  exact ⟨k, by omega⟩

/-- A multiple of `2^256` is `0` or at least `2^256` away from it. -/
theorem mulW_cases (k : Int) : W * k = 0 ∨ (W : Int) ≤ W * k ∨ W * k ≤ -(W : Int) := by
  rcases Int.lt_trichotomy k 0 with h | h | h
  · right; right
    have := Int.mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (show (0 : Int) ≤ W by omega)
    omega
  · left; subst h; simp
  · right; left
    have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (show (0 : Int) ≤ W by omega)
    omega

/-- The arithmetic of solc's signed `*` check: with `p` the wrapped product,
the code goes on exactly when the product is an `int256`. -/
theorem smul_ok {a b : Nat} (ha : a < W) (hb : b < W) :
    ((¬ (b = H ∧ sgn a < 0) ∧
        (b = (if a = 0 then 0 else toWord (Int.tdiv (sgn (b * a % W)) (sgn a))) ∨ a = 0)) ↔
      (-(H : Int) ≤ sgn a * sgn b ∧ sgn a * sgn b < H)) ∧
    ((-(H : Int) ≤ sgn a * sgn b ∧ sgn a * sgn b < H) → b * a % W = toWord (sgn a * sgn b)) := by
  have hW := W_eq
  have hH := H_pos
  obtain ⟨k, hk⟩ := sgn_mul_congr ha hb
  have hp : b * a % W < W := Nat.mod_lt _ W_pos
  have rp := sgn_range hp
  have ra := sgn_range ha
  have rb := sgn_range hb
  have hkW := mulW_cases k
  -- in range, the wrapped product is the product
  have inr : (-(H : Int) ≤ sgn a * sgn b ∧ sgn a * sgn b < H) → sgn (b * a % W) = sgn a * sgn b := by
    intro h; omega
  refine ⟨⟨fun ⟨hn, hq⟩ => ?_, fun h => ?_⟩, fun h => ?_⟩
  · rcases hq with hq | ha0
    · by_cases ha0 : a = 0
      · subst ha0; simp; omega
      · rw [if_neg ha0] at hq
        have hx : sgn a ≠ 0 := fun h => ha0 ((sgn_eq_zero ha).1 h)
        generalize ht : Int.tdiv (sgn (b * a % W)) (sgn a) = t at hq
        have et := Int.natAbs_tdiv (sgn (b * a % W)) (sgn a)
        have emod := Int.tmod_add_mul_tdiv (sgn (b * a % W)) (sgn a)
        have enat := Int.natAbs_tmod (sgn (b * a % W)) (sgn a)
        have hlt := Nat.mod_lt (sgn (b * a % W)).natAbs (show 0 < (sgn a).natAbs by omega)
        rw [ht] at et emod
        have et' : t.natAbs = (sgn (b * a % W)).natAbs / (sgn a).natAbs := et
        have hle := Nat.div_le_self (sgn (b * a % W)).natAbs (sgn a).natAbs
        by_cases htH : t < H
        · have ty : sgn b = t := by
            rw [hq, sgn_toWord (by omega) htH]
          rw [← ty] at emod
          omega
        · -- `t = 2^255`: only `x = ±1` reach it, and `x = -1` is the special case
          have tH : t = H := by omega
          have bH : b = H := by rw [hq, tH]; simp [toWord]
          have xpos : 0 < sgn a := by
            have := fun h => hn ⟨bH, h⟩; omega
          by_cases hx1 : (sgn a).natAbs = 1
          · have : sgn a = 1 := by omega
            rw [this, Int.tdiv_one] at ht
            omega
          · have h2 := Nat.div_le_div_left (a := (sgn (b * a % W)).natAbs)
              (show 2 ≤ (sgn a).natAbs by omega) (by decide)
            omega
    · subst ha0; simp; omega
  · have e := inr h
    refine ⟨fun ⟨hb', hx⟩ => ?_, ?_⟩
    · -- `x < 0` and `y = -2^255` overflow
      have hy : sgn b = -(H : Int) := by subst hb'; unfold sgn; simp; omega
      rw [hy] at h
      have := Int.mul_le_mul_of_nonneg_right (show sgn a ≤ -1 by omega)
        (show (0 : Int) ≤ H by omega)
      rw [Int.mul_neg] at h
      omega
    · by_cases ha0 : a = 0
      · exact .inr ha0
      · left
        have hx : sgn a ≠ 0 := fun h => ha0 ((sgn_eq_zero ha).1 h)
        rw [if_neg ha0, e, Int.mul_tdiv_cancel_left _ hx, toWord_sgn hb]
  · rw [← toWord_sgn hp, inr h]

theorem smul_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (sTail .mul) { m with stack := .val b :: .val a :: st } =
      if -(H : Int) ≤ sgn a * sgn b ∧ sgn a * sgn b < H then
        .ok { m with stack := .val (toWord (sgn a * sgn b)) :: st } 0
      else .revert := by
  obtain ⟨k1, k2⟩ := smul_ok ha hb
  simp [run, sTail, assertTop, Instr.step, Machine.next]
  by_cases h : -(H : Int) ≤ sgn a * sgn b ∧ sgn a * sgn b < H
  · obtain ⟨hn, hq⟩ := k1.2 h
    rw [if_neg hn, if_pos h]
    simp [Instr.step, Machine.next]
    rw [if_neg (by rintro ⟨h1, h2⟩; rcases hq with hq | hq <;> contradiction)]
    simp [Instr.step, Machine.next, k2 h]
  · rw [if_neg h]
    by_cases hn : b = H ∧ sgn a < 0
    · rw [if_pos hn]; rfl
    · rw [if_neg hn]
      simp [Instr.step, Machine.next]
      rw [if_pos]
      · rfl
      · refine ⟨fun ha0 => h (k1.1 ⟨hn, .inr ha0⟩), fun hq => h (k1.1 ⟨hn, .inl hq⟩)⟩

end Evm
end Solidity
