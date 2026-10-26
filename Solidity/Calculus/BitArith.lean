/-!
# Bitwise operators and products by a literal, as sums

The identities the cut (`Calculus/QuotientCut.lean`) writes a bitwise
operator with a literal, and a wrapping product by one, through: `x & c`
bit by bit from the lowest (`and_split`), `x | c` and `x ^ c` through
`x & c` (`and_add_or`, `xor_add_and`), and `x *% c` by doubling
(`mulMod_split`).  Truncating division at `int` by its sign cases
(`tdiv_iff`).
-/

namespace Solidity.Decide.BitArith

/-- **One bit off**: `x & c` is the low bits' product plus twice the rest. -/
theorem and_split (x c : Nat) : x &&& c = (x % 2) * (c % 2) + 2 * ((x / 2) &&& (c / 2)) := by
  have h1 := Nat.div_add_mod (x &&& c) 2
  rw [Nat.and_div_two] at h1
  have h2 : (x &&& c) % 2 = (x % 2) * (c % 2) := by
    have hx := Nat.mod_lt x (show 0 < 2 by decide)
    have hc := Nat.mod_lt c (show 0 < 2 by decide)
    have hb := Nat.mod_lt (x &&& c) (show 0 < 2 by decide)
    have key := (Nat.and_mod_two_eq_one (a := x) (b := c))
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h <;>
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with h' | h' <;>
      rw [h, h'] at key <;> rw [h, h'] <;> omega
  omega

theorem or_split (x c : Nat) : x ||| c = (if x % 2 = 1 ∨ c % 2 = 1 then 1 else 0) + 2 * ((x / 2) ||| (c / 2)) := by
  have h1 := Nat.div_add_mod (x ||| c) 2
  rw [Nat.or_div_two] at h1
  have h2 := Nat.or_mod_two_eq_one (a := x) (b := c)
  have hb := Nat.mod_lt (x ||| c) (show 0 < 2 by decide)
  split
  · have := h2.mpr (by assumption); omega
  · have : (x ||| c) % 2 ≠ 1 := fun h => by simp_all
    omega

theorem xor_split (x c : Nat) :
    x ^^^ c = (if (x % 2 = 1) = (c % 2 = 1) then 0 else 1) + 2 * ((x / 2) ^^^ (c / 2)) := by
  have h1 := Nat.div_add_mod (x ^^^ c) 2
  rw [Nat.xor_div_two] at h1
  have h2 := Nat.xor_mod_two_eq_one (a := x) (b := c)
  have hb := Nat.mod_lt (x ^^^ c) (show 0 < 2 by decide)
  split
  · rename_i h
    have : (x ^^^ c) % 2 ≠ 1 := fun h' => h2.mp h' (by rw [h])
    omega
  · rename_i h
    have : (x ^^^ c) % 2 = 1 := h2.mpr (fun h' => h (propext h'))
    omega

/-- **`|` through `&`**: `(x & c) + (x | c) = x + c`. -/
theorem and_add_or : ∀ (n x c : Nat), x < 2 ^ n → (x &&& c) + (x ||| c) = x + c
  | 0, x, c, hx => by
    have : x = 0 := by simp only [Nat.pow_zero] at hx; omega
    subst this
    simp only [Nat.zero_and, Nat.zero_or, Nat.zero_add]
  | n + 1, x, c, hx => by
    have ih := and_add_or n (x / 2) (c / 2) (by rw [Nat.pow_succ] at hx; omega)
    rw [and_split x c, or_split x c]
    have hc := Nat.div_add_mod c 2
    have hx' := Nat.div_add_mod x 2
    have hxm := Nat.mod_lt x (show 0 < 2 by decide)
    have hcm := Nat.mod_lt c (show 0 < 2 by decide)
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h <;>
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with h' | h' <;>
      simp [h, h'] <;> omega

/-- `c` past its own bits: `x & c` for `c < 2^n` needs `x`'s bits below `n` only. -/
theorem and_or_eq (x c : Nat) : (x &&& c) + (x ||| c) = x + c :=
  and_add_or x x c Nat.lt_two_pow_self

theorem xor_add_and : ∀ (n x c : Nat), x < 2 ^ n → (x ^^^ c) + 2 * (x &&& c) = x + c
  | 0, x, c, hx => by
    have : x = 0 := by simp only [Nat.pow_zero] at hx; omega
    subst this
    simp only [Nat.zero_xor, Nat.zero_and, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  | n + 1, x, c, hx => by
    have ih := xor_add_and n (x / 2) (c / 2) (by rw [Nat.pow_succ] at hx; omega)
    rw [and_split x c, xor_split x c]
    have hc := Nat.div_add_mod c 2
    have hx' := Nat.div_add_mod x 2
    have hxm := Nat.mod_lt x (show 0 < 2 by decide)
    have hcm := Nat.mod_lt c (show 0 < 2 by decide)
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h <;>
      rcases (show c % 2 = 0 ∨ c % 2 = 1 by omega) with h' | h' <;>
      simp only [h, h'] <;> simp <;> omega

theorem xor_and_eq (x c : Nat) : (x ^^^ c) + 2 * (x &&& c) = x + c :=
  xor_add_and x x c Nat.lt_two_pow_self

/-- **A wrapping product by doubling**: `x·c mod M` from `x·⌊c/2⌋ mod M`. -/
theorem mulMod_double (x k M : Int) : (x * k % M + x * k % M) % M = x * (2 * k) % M := by
  rw [show x * (2 * k) = x * k + x * k by rw [Int.two_mul, Int.mul_add]]
  exact (Int.add_emod _ _ _).symm

theorem mulMod_succ (x k M : Int) : (x * k % M + x) % M = x * (k + 1) % M := by
  rw [Int.mul_add, Int.mul_one, Int.emod_add_emod]

theorem ediv_iff {d : Int} (hd : 0 < d) (v w : Int) :
    w = v / d ↔ d * w ≤ v ∧ v ≤ d * w + (d - 1) := by
  constructor
  · rintro rfl
    have h1 := Int.ediv_mul_le v (Int.ne_of_gt hd)
    have h2 := Int.lt_ediv_add_one_mul_self v hd
    rw [Int.add_mul, Int.one_mul] at h2
    rw [Int.mul_comm]
    omega
  · rintro ⟨h1, h2⟩
    have hle : w ≤ v / d := (Int.le_ediv_iff_mul_le hd).mpr (by rw [Int.mul_comm]; exact h1)
    have hlt : v / d < w + 1 :=
      (Int.ediv_lt_iff_lt_mul hd).mpr (by rw [Int.add_mul, Int.one_mul, Int.mul_comm]; omega)
    omega

/-- The sign cases of truncating division, at a positive divisor. -/
def TdivRel (v c w : Int) (d : Int) : Prop :=
  (0 ≤ v → 0 ≤ v - c * w ∧ v - c * w ≤ d - 1) ∧ (v < 0 → 0 ≤ c * w - v ∧ c * w - v ≤ d - 1)

theorem tdiv_pos_iff {d : Int} (hd : 0 < d) (v w : Int) : w = v.tdiv d ↔ TdivRel v d w d := by
  unfold TdivRel
  rcases Int.lt_or_le v 0 with hv | hv
  · have ht : v.tdiv d = -((-v) / d) := by
      have := Int.neg_tdiv (-v) d
      rw [Int.neg_neg] at this
      rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    rw [ht]
    have := ediv_iff hd (-v) (-w)
    constructor
    · intro h
      have h' := this.mp (by rw [h, Int.neg_neg])
      rw [Int.mul_neg] at h'
      exact ⟨fun h0 => absurd h0 (by omega), fun _ => by omega⟩
    · rintro ⟨-, h⟩
      have h' := this.mpr (by rw [Int.mul_neg]; have := h hv; omega)
      omega
  · rw [Int.tdiv_eq_ediv_of_nonneg hv, ediv_iff hd]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun _ => ⟨by omega, by omega⟩, fun h0 => absurd h0 (by omega)⟩
    · rintro ⟨h, -⟩; have := h hv; omega

/-- **Truncating division by its remainder's sign**: `w = tdiv v c` exactly
where `v - c·w` lies between `0` and `|c| - 1` on `v`'s side of zero. -/
theorem tdiv_iff (v c w : Int) (hc : c ≠ 0) : w = v.tdiv c ↔ TdivRel v c w c.natAbs := by
  rcases Int.lt_or_le 0 c with hp | hn
  · have : (c.natAbs : Int) = c := Int.natAbs_of_nonneg (by omega)
    rw [this]; exact tdiv_pos_iff hp v w
  · have hcn : (c.natAbs : Int) = -c := by omega
    rw [hcn]
    have hd : 0 < -c := by omega
    have := tdiv_pos_iff hd v (-w)
    rw [Int.tdiv_neg] at this
    have e : -c * -w = c * w := by rw [Int.neg_mul_neg]
    unfold TdivRel at this ⊢
    rw [e] at this
    constructor
    · intro h; exact this.mp (by rw [h])
    · intro h; have := this.mpr h; omega

/-- A truncated remainder lies between `0` and the dividend. -/
theorem tmod_bounds (x v : Int) :
    (0 ≤ x → 0 ≤ x.tmod v ∧ x.tmod v ≤ x) ∧ (x < 0 → x ≤ x.tmod v ∧ x.tmod v ≤ 0) := by
  have h1 := Int.natAbs_tmod x v
  have h2 := Nat.mod_le x.natAbs v.natAbs
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have := Int.tmod_nonneg v hx; omega
  · have := Int.tmod_nonneg v (show 0 ≤ -x by omega); rw [Int.neg_tmod] at this; omega

/-- A truncated quotient by a divisor other than `0` and `-1` stays in range. -/
theorem tdiv_bounds (x v M : Int) (h0 : -M ≤ x) (h1 : x < M) (hv0 : v ≠ 0) (hv1 : v ≠ -1) :
    -M ≤ x.tdiv v ∧ x.tdiv v < M := by
  by_cases hv : v = 1
  · subst hv; rw [Int.tdiv_one]; exact ⟨h0, h1⟩
  · have h : (x.tdiv v).natAbs = x.natAbs / v.natAbs := Int.natAbs_tdiv x v
    have h2 : 2 ≤ v.natAbs := by omega
    have h3 := Nat.div_le_div_left (a := x.natAbs) h2 (by decide)
    omega

theorem tdiv_neg_one (x : Int) : x.tdiv (-1) = -x := by
  rw [Int.tdiv_neg, Int.tdiv_one]

theorem tmod_neg_one (x : Int) : x.tmod (-1) = 0 := by
  rw [Int.tmod_neg, Int.tmod_one]

end Solidity.Decide.BitArith
