

namespace Solidity.Language.FixedPoint

structure FxTy where
  signed : Bool
  bits : Nat
  digits : Nat
  valid : (decide (8 ≤ bits) && decide (bits ≤ 256) && bits % 8 == 0 &&
    decide (digits ≤ 80)) = true
  deriving DecidableEq

namespace FxTy

def mk? (signed : Bool) (bits digits : Nat) : Option FxTy :=
  if h : (decide (8 ≤ bits) && decide (bits ≤ 256) && bits % 8 == 0 &&
      decide (digits ≤ 80)) = true
  then some ⟨signed, bits, digits, h⟩ else none

def fixed : FxTy := ⟨true, 128, 18, by decide⟩

def ufixed : FxTy := ⟨false, 128, 18, by decide⟩

def name (t : FxTy) : String :=
  (if t.signed then "fixed" else "ufixed") ++ toString t.bits ++ "x" ++ toString t.digits

def scale (t : FxTy) : Int := 10 ^ t.digits

def lo (t : FxTy) : Int := if t.signed then -2 ^ (t.bits - 1) else 0

def hi (t : FxTy) : Int := if t.signed then 2 ^ (t.bits - 1) - 1 else 2 ^ t.bits - 1

def inRange (t : FxTy) (v : Int) : Bool := decide (t.lo ≤ v) && decide (v ≤ t.hi)

def storageBytes (t : FxTy) : Nat := t.bits / 8

def maxInt (t : FxTy) : Int := t.hi / t.scale

def minInt (t : FxTy) : Int := -((-t.lo) / t.scale)

theorem bits_ge (t : FxTy) : 8 ≤ t.bits := by
  have h := t.valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem bits_le (t : FxTy) : t.bits ≤ 256 := by
  have h := t.valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem scale_pos (t : FxTy) : 0 < t.scale := Int.pow_pos (by decide)

theorem pow_bits (t : FxTy) : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := by
  have h : t.bits = (t.bits - 1) + 1 := by have := t.bits_ge; omega
  rw [h, Int.pow_succ, Nat.add_sub_cancel, Int.mul_comm]

theorem half_pos (t : FxTy) : (0 : Int) < 2 ^ (t.bits - 1) := Int.pow_pos (by decide)

theorem lo_le_zero (t : FxTy) : t.lo ≤ 0 := by
  have h : (0 : Int) < 2 ^ (t.bits - 1) := t.half_pos
  simp only [lo]; split <;> omega

theorem hi_nonneg (t : FxTy) : 0 ≤ t.hi := by
  have h : (0 : Int) < 2 ^ (t.bits - 1) := t.half_pos
  have hp : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := t.pow_bits
  simp only [hi]; split <;> omega

end FxTy

def Fx (t : FxTy) : Type := {v : Int // t.inRange v = true}

instance (t : FxTy) : DecidableEq (Fx t) :=
  inferInstanceAs (DecidableEq {v : Int // t.inRange v = true})

inductive Fail where

  | overflow

  | divZero
  deriving DecidableEq, Repr

def Fail.panicCode : Fail → Nat
  | .overflow => 0x11
  | .divZero => 0x12

inductive Mode where
  | checked
  | unchecked
  deriving DecidableEq, Repr

namespace Fx

variable {t : FxTy}

def zero (t : FxTy) : Fx t :=
  ⟨0, by
    have := t.half_pos
    simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq]
    simp only [FxTy.lo, FxTy.hi]
    have := t.pow_bits
    cases t.signed <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega⟩

def ofInt? (t : FxTy) (v : Int) : Option (Fx t) :=
  if h : t.inRange v = true then some ⟨v, h⟩ else none

def wrapInt (t : FxTy) (v : Int) : Int :=
  if t.signed ∧ 2 ^ (t.bits - 1) ≤ v % 2 ^ t.bits then v % 2 ^ t.bits - 2 ^ t.bits
  else v % 2 ^ t.bits

theorem wrapInt_inRange (t : FxTy) (v : Int) : t.inRange (wrapInt t v) = true := by
  have hp := t.pow_bits
  have hh := t.half_pos
  have h0 : 0 ≤ v % 2 ^ t.bits := Int.emod_nonneg v (by omega)
  have h1 : v % 2 ^ t.bits < 2 ^ t.bits := Int.emod_lt_of_pos v (by omega)
  simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq]
  simp only [wrapInt, FxTy.lo, FxTy.hi]
  cases t.signed <;> simp only [Bool.false_eq_true, false_and, true_and, ite_false, ite_true] <;>
    first | omega | (split <;> omega)

def wrap (t : FxTy) (v : Int) : Fx t := ⟨wrapInt t v, wrapInt_inRange t v⟩

theorem wrapInt_of_inRange {v : Int} (h : t.inRange v = true) : wrapInt t v = v := by
  have hp := t.pow_bits
  have hh := t.half_pos
  simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [FxTy.lo, FxTy.hi] at h
  unfold wrapInt
  cases hs : t.signed
  · simp only [hs, Bool.false_eq_true, ite_false] at h ⊢
    exact Int.emod_eq_of_lt h.1 (by omega)
  · simp only [hs, ite_true] at h ⊢
    by_cases hv : 0 ≤ v
    · have hm : v % 2 ^ t.bits = v := Int.emod_eq_of_lt hv (by omega)
      simp only [hm, true_and]
      split <;> omega
    · have hm : v % 2 ^ t.bits = v + 2 ^ t.bits := by
        rw [← Int.add_emod_right]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      simp only [hm, true_and]
      split <;> omega

theorem wrapInt_emod (t : FxTy) (v : Int) : wrapInt t v % 2 ^ t.bits = v % 2 ^ t.bits := by
  unfold wrapInt
  split
  · rw [Int.sub_emod_right, Int.emod_emod]
  · rw [Int.emod_emod]

def result (m : Mode) (t : FxTy) (v : Int) : Except Fail (Fx t) :=
  match m with
  | .checked => if h : t.inRange v = true then .ok ⟨v, h⟩ else .error .overflow
  | .unchecked => .ok (wrap t v)

theorem result_of_inRange (m : Mode) {v : Int} (h : t.inRange v = true) :
    result m t v = .ok ⟨v, h⟩ := by
  cases m
  · simp only [result, h, dite_true]
  · simp only [result, wrap, wrapInt_of_inRange h]

theorem result_checked_overflow {v : Int} (h : t.inRange v = false) :
    result .checked t v = (.error .overflow : Except Fail (Fx t)) := by
  simp only [result, h, Bool.false_eq_true, dite_false]

def add (m : Mode) (a b : Fx t) : Except Fail (Fx t) := result m t (a.1 + b.1)

def sub (m : Mode) (a b : Fx t) : Except Fail (Fx t) := result m t (a.1 - b.1)

def neg (m : Mode) (a : Fx t) : Except Fail (Fx t) := result m t (-a.1)

def mul (m : Mode) (a b : Fx t) : Except Fail (Fx t) := result m t ((a.1 * b.1).tdiv t.scale)

def div (m : Mode) (a b : Fx t) : Except Fail (Fx t) :=
  if b.1 = 0 then .error .divZero else result m t ((a.1 * t.scale).tdiv b.1)

def mod (m : Mode) (a b : Fx t) : Except Fail (Fx t) :=
  if b.1 = 0 then .error .divZero else result m t (a.1.tmod b.1)

def inc (m : Mode) (a : Fx t) : Except Fail (Fx t) := result m t (a.1 + t.scale)

def dec (m : Mode) (a : Fx t) : Except Fail (Fx t) := result m t (a.1 - t.scale)

def lt (a b : Fx t) : Bool := decide (a.1 < b.1)

def le (a b : Fx t) : Bool := decide (a.1 ≤ b.1)

def SameValue {t' : FxTy} (a : Fx t) (b : Fx t') : Prop := a.1 * t'.scale = b.1 * t.scale

theorem add_eq (m : Mode) (a b : Fx t) (h : t.inRange (a.1 + b.1) = true) :
    add m a b = .ok ⟨a.1 + b.1, h⟩ := result_of_inRange m h

theorem add_overflow (a b : Fx t) (h : t.inRange (a.1 + b.1) = false) :
    add .checked a b = .error .overflow := result_checked_overflow h

theorem add_unchecked (a b : Fx t) : add .unchecked a b = .ok (wrap t (a.1 + b.1)) := rfl

theorem add_comm (m : Mode) (a b : Fx t) : add m a b = add m b a := by
  simp only [add, Int.add_comm]

theorem mul_comm (m : Mode) (a b : Fx t) : mul m a b = mul m b a := by
  simp only [mul, Int.mul_comm]

theorem sub_eq (m : Mode) (a b : Fx t) (h : t.inRange (a.1 - b.1) = true) :
    sub m a b = .ok ⟨a.1 - b.1, h⟩ := result_of_inRange m h

theorem add_zero (m : Mode) (a : Fx t) : add m a (zero t) = .ok a := by
  have h : t.inRange (a.1 + 0) = true := by rw [Int.add_zero]; exact a.2
  rw [add_eq m a (zero t) h]
  exact congrArg Except.ok (Subtype.ext (Int.add_zero a.1))

theorem mul_one (m : Mode) (a : Fx t) (h1 : t.inRange t.scale = true) :
    mul m a ⟨t.scale, h1⟩ = .ok a := by
  have he : (a.1 * t.scale).tdiv t.scale = a.1 :=
    Int.mul_tdiv_cancel a.1 (by have := t.scale_pos; omega)
  simp only [mul, he]
  exact result_of_inRange m a.2

theorem div_zero (m : Mode) (a : Fx t) : div m a (zero t) = .error .divZero := by
  simp only [div, zero, ite_true]

theorem mod_zero (m : Mode) (a : Fx t) : mod m a (zero t) = .error .divZero := by
  simp only [mod, zero, ite_true]

theorem tmod_between (x y : Int) : (0 ≤ x → 0 ≤ x.tmod y ∧ x.tmod y ≤ x) ∧
    (x < 0 → x ≤ x.tmod y ∧ x.tmod y ≤ 0) := by
  have cast_ofNat (n : Nat) : Int.ofNat n = (n : Int) := rfl
  rcases x with m | m <;> rcases y with n | n <;>
    simp only [Int.tmod, cast_ofNat, Nat.succ_eq_add_one] <;>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    have := Nat.mod_le m n <;> have := Nat.mod_le m (n + 1) <;>
    have := Nat.mod_le (m + 1) n <;> have := Nat.mod_le (m + 1) (n + 1) <;> omega

theorem mod_inRange (a b : Fx t) : t.inRange (a.1.tmod b.1) = true := by
  have ha := a.2
  have hb := tmod_between a.1 b.1
  simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
  have hl : t.lo ≤ 0 := t.lo_le_zero
  have hu : 0 ≤ t.hi := t.hi_nonneg
  by_cases h : 0 ≤ a.1
  · have := hb.1 h; omega
  · have := hb.2 (by omega); omega

theorem mod_eq (m : Mode) (a b : Fx t) (hb : b.1 ≠ 0) :
    mod m a b = .ok ⟨a.1.tmod b.1, mod_inRange a b⟩ := by
  simp only [mod, hb, ite_false]
  exact result_of_inRange m (mod_inRange a b)

theorem div_eq (m : Mode) (a b : Fx t) (hb : b.1 ≠ 0)
    (h : t.inRange ((a.1 * t.scale).tdiv b.1) = true) :
    div m a b = .ok ⟨(a.1 * t.scale).tdiv b.1, h⟩ := by
  simp only [div, hb, ite_false]
  exact result_of_inRange m h

theorem lt_iff (a b : Fx t) : lt a b = true ↔ a.1 < b.1 := by
  simp only [lt, decide_eq_true_eq]

def rescale (n n' : Nat) (v : Int) : Int :=
  if n ≤ n' then v * 10 ^ (n' - n) else v.tdiv (10 ^ (n - n'))

end Fx

namespace FxTy

def subsumes (t t' : FxTy) : Bool :=
  decide (t.digits ≤ t'.digits) && t'.inRange (t.lo * 10 ^ (t'.digits - t.digits)) &&
    t'.inRange (t.hi * 10 ^ (t'.digits - t.digits))

def solcImplicit (t t' : FxTy) : Bool :=
  decide (t.digits ≤ t'.digits) && decide (t.bits ≤ t'.bits) &&
    decide (t.maxInt ≤ t'.maxInt) && decide (t'.minInt ≤ t.minInt)

def implicitOK (t t' : FxTy) : Bool := solcImplicit t t' && subsumes t t'

def common? (t t' : FxTy) : Option FxTy :=
  if implicitOK t' t then some t else if implicitOK t t' then some t' else none

def intImplicit (t : FxTy) (lo hi : Int) : Bool :=
  decide (t.minInt ≤ lo) && decide (hi ≤ t.maxInt)

end FxTy

namespace Fx

variable {t t' : FxTy}

theorem inRange_mul_of_subsumes (h : t.subsumes t' = true) (a : Fx t) :
    t'.inRange (a.1 * 10 ^ (t'.digits - t.digits)) = true := by
  have ha := a.2
  have hc : (0 : Int) ≤ 10 ^ (t'.digits - t.digits) := Int.le_of_lt (Int.pow_pos (by decide))
  simp only [FxTy.subsumes, FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq] at h ha ⊢
  have h1 := Int.mul_le_mul_of_nonneg_right ha.1 hc
  have h2 := Int.mul_le_mul_of_nonneg_right ha.2 hc
  omega

def implicit (h : t.subsumes t' = true) (a : Fx t) : Fx t' :=
  ⟨a.1 * 10 ^ (t'.digits - t.digits), inRange_mul_of_subsumes h a⟩

theorem implicit_sameValue (h : t.subsumes t' = true) (a : Fx t) : SameValue a (implicit h a) := by
  have hd : t.digits ≤ t'.digits := by
    simp only [FxTy.subsumes, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  simp only [SameValue, implicit, FxTy.scale]
  have hp : (10 : Int) ^ t'.digits = 10 ^ (t'.digits - t.digits) * 10 ^ t.digits := by
    rw [← Int.pow_add, Nat.sub_add_cancel hd]
  rw [hp, Int.mul_assoc]

theorem implicit_lt (h : t.subsumes t' = true) (a b : Fx t) :
    lt (implicit h a) (implicit h b) = lt a b := by
  have hc : (0 : Int) < 10 ^ (t'.digits - t.digits) := Int.pow_pos (by decide)
  simp only [lt]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  simp only [implicit]
  constructor
  · intro hl
    exact Int.lt_of_mul_lt_mul_right hl (Int.le_of_lt hc)
  · intro hl
    exact Int.mul_lt_mul_of_pos_right hl hc

def explicit (t' : FxTy) (a : Fx t) : Fx t' :=
  wrap t' (rescale t.digits t'.digits a.1)

theorem explicit_of_subsumes (h : t.subsumes t' = true) (a : Fx t) :
    explicit t' a = implicit h a := by
  have hd : t.digits ≤ t'.digits := by
    simp only [FxTy.subsumes, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  simp only [explicit, rescale, hd, ite_true, wrap, implicit,
    wrapInt_of_inRange (inRange_mul_of_subsumes h a)]
  all_goals rfl

theorem ofInteger_inRange {lo hi k : Int} (h : t.intImplicit lo hi = true)
    (hk : lo ≤ k ∧ k ≤ hi) : t.inRange (k * t.scale) = true := by
  have hs := t.scale_pos
  have hp := t.pow_bits
  have hh := t.half_pos
  simp only [FxTy.intImplicit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [FxTy.maxInt, FxTy.minInt] at h
  have hu : k * t.scale ≤ t.hi := by
    have e1 : k * t.scale ≤ (t.hi / t.scale) * t.scale :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have e2 : (t.hi / t.scale) * t.scale ≤ t.hi := Int.ediv_mul_le t.hi (by omega)
    omega
  have hl : t.lo ≤ k * t.scale := by
    have e1 : -((-t.lo) / t.scale) * t.scale ≤ k * t.scale :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have e2 : ((-t.lo) / t.scale) * t.scale ≤ -t.lo := Int.ediv_mul_le (-t.lo) (by omega)
    rw [Int.neg_mul] at e1
    omega
  simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hl, hu⟩

def ofIntegerExplicit (t : FxTy) (k : Int) : Fx t := wrap t (k * t.scale)

theorem ofIntegerExplicit_of_implicit {lo hi k : Int} (h : t.intImplicit lo hi = true)
    (hk : lo ≤ k ∧ k ≤ hi) :
    ofIntegerExplicit t k = ⟨k * t.scale, ofInteger_inRange h hk⟩ := by
  simp only [ofIntegerExplicit, wrap, wrapInt_of_inRange (ofInteger_inRange h hk)]
  all_goals rfl

def ofBits (t : FxTy) (u : Int) : Fx t := wrap t u

def toBits (a : Fx t) : Int := a.1 % 2 ^ t.bits

def toIntTrunc (a : Fx t) : Int := a.1.tdiv t.scale

def ofLiteral? (t : FxTy) (num : Int) (den : Nat) : Option (Fx t) :=
  if den = 0 then none
  else if (num * t.scale) % den = 0 then ofInt? t ((num * t.scale) / den) else none

def literalTrunc (t : FxTy) (num : Int) (den : Nat) : Int := (num * t.scale).tdiv den

def explicitConst? (t : FxTy) (num : Int) (den : Nat) : Option (Fx t) :=
  if den = 0 then none else ofInt? t (literalTrunc t num den)

def toWord (a : Fx t) : Int := a.1 % 2 ^ 256

def ofWord? (t : FxTy) (w : Int) : Option (Fx t) :=
  ofInt? t (if t.signed ∧ 2 ^ 255 ≤ w then w - 2 ^ 256 else w)

example (w : Fin (2 ^ 256)) : 0 ≤ (w.val : Int) ∧ (w.val : Int) < 2 ^ 256 := by
  have h : (w.val : Int) < ((2 ^ 256 : Nat) : Int) := Int.ofNat_lt.mpr w.isLt
  simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using And.intro (Int.natCast_nonneg w.val) h

theorem pow_bits_le (t : FxTy) : (2 : Int) ^ t.bits ≤ 2 ^ 256 := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) t.bits_le
  have e1 : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := by
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  have e2 : ((2 ^ 256 : Nat) : Int) = (2 : Int) ^ 256 := by
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  omega

theorem toWord_range (a : Fx t) : 0 ≤ toWord a ∧ toWord a < 2 ^ 256 := by
  have hp : (0 : Int) < 2 ^ 256 := Int.pow_pos (by decide)
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hp⟩

theorem ofWord_toWord (a : Fx t) : ofWord? t (toWord a) = some a := by
  have ha := a.2
  have hp := t.pow_bits
  have hh := t.half_pos
  have hle := pow_bits_le t
  have h256 : (2 : Int) ^ 256 = 2 * 2 ^ 255 := by rw [Int.pow_succ, Int.mul_comm]
  simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq] at ha
  simp only [FxTy.lo, FxTy.hi] at ha
  have hw : (if t.signed ∧ 2 ^ 255 ≤ toWord a then toWord a - 2 ^ 256 else toWord a) = a.1 := by
    unfold toWord
    cases hs : t.signed
    · simp only [hs, Bool.false_eq_true, ite_false, false_and] at ha ⊢
      exact Int.emod_eq_of_lt ha.1 (by omega)
    · simp only [hs, ite_true, true_and] at ha ⊢
      by_cases hv : 0 ≤ a.1
      · have hm : a.1 % 2 ^ 256 = a.1 := Int.emod_eq_of_lt hv (by omega)
        rw [hm]
        split <;> omega
      · have hm : a.1 % 2 ^ 256 = a.1 + 2 ^ 256 := by
          rw [← Int.add_emod_right]
          exact Int.emod_eq_of_lt (by omega) (by omega)
        rw [hm]
        split <;> omega
  simp only [ofWord?, hw, ofInt?, a.2, dite_true]
  rfl

def fixed8x1 : FxTy := ⟨true, 8, 1, by decide⟩

example : fixed8x1.lo = -128 ∧ fixed8x1.hi = 127 ∧ fixed8x1.scale = 10 := by
  decide

def ufixed8x2 : FxTy := ⟨false, 8, 2, by decide⟩

example : ufixed8x2.lo = 0 ∧ ufixed8x2.hi = 255 ∧ ufixed8x2.scale = 100 := by
  decide

def ufixed16x2 : FxTy := ⟨false, 16, 2, by decide⟩

example : ufixed16x2.lo = 0 ∧ ufixed16x2.hi = 65535 ∧ ufixed16x2.scale = 100 := by
  decide

def fixed16x2 : FxTy := ⟨true, 16, 2, by decide⟩

example : fixed16x2.lo = -32768 ∧ fixed16x2.hi = 32767 ∧ fixed16x2.scale = 100 := by
  decide

def fixed8x3 : FxTy := ⟨true, 8, 3, by decide⟩

example : fixed8x3.lo = -128 ∧ fixed8x3.hi = 127 ∧ fixed8x3.scale = 1000 := by
  decide

def ufixed8x3 : FxTy := ⟨false, 8, 3, by decide⟩

example : ufixed8x3.lo = 0 ∧ ufixed8x3.hi = 255 ∧ ufixed8x3.scale = 1000 := by
  decide

def ufixed8x4 : FxTy := ⟨false, 8, 4, by decide⟩

example : ufixed8x4.lo = 0 ∧ ufixed8x4.hi = 255 ∧ ufixed8x4.scale = 10000 := by
  decide

example : (FxTy.mk? true 8 0).isSome ∧ (FxTy.mk? false 256 80).isSome ∧
    (FxTy.mk? true 7 8).isNone ∧ (FxTy.mk? true 264 1).isNone ∧
    (FxTy.mk? true 8 81).isNone := by
  decide

example : (ofLiteral? fixed8x1 (-128) 10).isSome ∧ (ofLiteral? fixed8x1 127 10).isSome ∧
    (ofLiteral? ufixed8x2 255 100).isSome ∧ (ofLiteral? fixed8x1 128 10).isNone ∧
    (ofLiteral? ⟨true, 40, 40, by decide⟩ 314 100).isNone := by
  decide +kernel

example : (explicitConst? ⟨false, 8, 1, by decide⟩ 1 3).map Subtype.val = some 3 ∧
    (explicitConst? ⟨false, 8, 1, by decide⟩ 201 2).isNone := by
  decide

theorem solc_lossy :
    FxTy.solcImplicit fixed8x3 ufixed8x3 = true ∧ FxTy.subsumes fixed8x3 ufixed8x3 = false ∧
    FxTy.solcImplicit ufixed8x3 ufixed8x4 = true ∧ FxTy.subsumes ufixed8x3 ufixed8x4 = false := by
  decide +kernel

example : (div .checked (⟨100, by decide⟩ : Fx ufixed16x2) ⟨300, by decide⟩).toOption.map
      Subtype.val = some 33 ∧
    (div .checked (⟨-100, by decide⟩ : Fx fixed16x2) ⟨300, by decide⟩).toOption.map
      Subtype.val = some (-33) := by
  decide

example : (neg .checked (⟨-128, by decide⟩ : Fx fixed8x1)).toOption.isNone ∧
    (neg .unchecked (⟨-128, by decide⟩ : Fx fixed8x1)).toOption.map Subtype.val =
      some (-128) := by
  decide

example : (mul .checked (⟨255, by decide⟩ : Fx ufixed16x2) ⟨200, by decide⟩).toOption.map
      Subtype.val = some 510 ∧
    (mul .checked (⟨25500, by decide⟩ : Fx ufixed16x2) ⟨300, by decide⟩).toOption.isNone ∧
    (mul .unchecked (⟨25500, by decide⟩ : Fx ufixed16x2) ⟨300, by decide⟩).toOption.map
      Subtype.val = some (76500 - 65536) := by
  decide

example : (mod .checked (⟨-350, by decide⟩ : Fx fixed16x2) ⟨100, by decide⟩).toOption.map
      Subtype.val = some (-50) := by
  decide

end Fx

end Solidity.Language.FixedPoint
