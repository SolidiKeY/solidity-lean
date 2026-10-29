/-!
# Fixed-point reference semantics

The values and operations of Solidity's `fixedMxN` / `ufixedMxN` types
(`docs/feature-work/fixed-point-semantics.md`).  solc 0.8.38 type-checks
them but generates no code for them (`UnimplementedFeatureError`), so this
module is the reference the scope decision G00 Q6 ("full fixed-point
support, beyond the acceptance boundary of pinned solc") needs.  It is not
wired into the AST, the elaborator or the compiler yet.

A type `FxTy` carries its signedness, its width `M` (8 … 256 in steps of 8)
and its decimal digits `N` (0 … 80), exactly solc's scanner bounds
(`liblangutil/Token.cpp`, `fromIdentifierOrKeyword`).  A value `Fx t` is
intrinsic: an integer `v` in the `M`-bit range of `t`, denoting `v / 10^N`
(the ABI specification's reading of `fixed<M>x<N>`).  Arithmetic stays on
`Int`, as the typed integers do (`Semantics/Value.lean`): the range is a
proof beside the number.

An operation computes the exact scaled result, truncated toward zero where
digits are dropped, then either range-checks it (`Mode.checked`: a result
outside the range fails with `Fail.overflow`, solc's `Panic(0x11)`) or wraps
it modulo `2^M` (`Mode.unchecked`).  A zero divisor fails with
`Fail.divZero` (`Panic(0x12)`) in either mode, as solc's integer division
does (its `control-structures.rst`: the check "can not be disabled through
`unchecked`"); G01 Q5 observes these codes exactly, where the current core
reads both as a revert (`docs/solc-alignment.md`).  Where the language
specification is silent, the user's answers to the document's questions
Q1–Q8 are encoded, each named at its definition.

This module imports nothing.
-/

namespace Solidity.Language.FixedPoint

/-- A fixed-point type: `fixedMxN` when `signed`, else `ufixedMxN`, with
`M = bits` and `N = digits` inside solc's bounds. -/
structure FxTy where
  signed : Bool
  bits : Nat
  digits : Nat
  valid : (decide (8 ≤ bits) && decide (bits ≤ 256) && bits % 8 == 0 &&
    decide (digits ≤ 80)) = true
  deriving DecidableEq

namespace FxTy

/-- The type `fixedMxN`/`ufixedMxN` when `M` and `N` are in solc's bounds,
the ones its scanner reads as a type name (any other spelling is an
identifier). -/
def mk? (signed : Bool) (bits digits : Nat) : Option FxTy :=
  if h : (decide (8 ≤ bits) && decide (bits ≤ 256) && bits % 8 == 0 &&
      decide (digits ≤ 80)) = true
  then some ⟨signed, bits, digits, h⟩ else none

/-- `fixed`, an alias of `fixed128x18`. -/
def fixed : FxTy := ⟨true, 128, 18, by decide⟩

/-- `ufixed`, an alias of `ufixed128x18`. -/
def ufixed : FxTy := ⟨false, 128, 18, by decide⟩

/-- The canonical name, also the ABI type name in a selector. -/
def name (t : FxTy) : String :=
  (if t.signed then "fixed" else "ufixed") ++ toString t.bits ++ "x" ++ toString t.digits

/-- `10^N`: the scaled integer of the value `1`. -/
def scale (t : FxTy) : Int := 10 ^ t.digits

/-- The least scaled integer. -/
def lo (t : FxTy) : Int := if t.signed then -2 ^ (t.bits - 1) else 0

/-- The greatest scaled integer. -/
def hi (t : FxTy) : Int := if t.signed then 2 ^ (t.bits - 1) - 1 else 2 ^ t.bits - 1

/-- The scaled integers of the type. -/
def inRange (t : FxTy) (v : Int) : Bool := decide (t.lo ≤ v) && decide (v ≤ t.hi)

/-- Bytes in a storage slot (solc's `storageBytes`, right-aligned). -/
def storageBytes (t : FxTy) : Nat := t.bits / 8

/-- solc's `maxIntegerValue`: the greatest integer the type holds. -/
def maxInt (t : FxTy) : Int := t.hi / t.scale

/-- solc's `minIntegerValue`: the least integer, the bound divided toward
zero (`-((-lo) / 10^N)`, as C++'s `bigint` division of the negative bound). -/
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

/-- `2^M = 2 · 2^(M-1)`. -/
theorem pow_bits (t : FxTy) : (2 : Int) ^ t.bits = 2 * 2 ^ (t.bits - 1) := by
  have h : t.bits = (t.bits - 1) + 1 := by have := t.bits_ge; omega
  rw [h, Int.pow_succ, Nat.add_sub_cancel, Int.mul_comm]

theorem half_pos (t : FxTy) : (0 : Int) < 2 ^ (t.bits - 1) := Int.pow_pos (by decide)

end FxTy

/-- A value of type `t`: its scaled integer, in range. -/
def Fx (t : FxTy) : Type := {v : Int // t.inRange v = true}

instance (t : FxTy) : DecidableEq (Fx t) :=
  inferInstanceAs (DecidableEq {v : Int // t.inRange v = true})

/-- Why an operation fails: solc's panic. -/
inductive Fail where
  /-- A checked result outside the range: `Panic(0x11)`. -/
  | overflow
  /-- A zero divisor of `/` or `%`: `Panic(0x12)`. -/
  | divZero
  deriving DecidableEq, Repr

/-- The panic code of a failure. -/
def Fail.panicCode : Fail → Nat
  | .overflow => 0x11
  | .divZero => 0x12

/-- Checked (the default) or inside `unchecked { }`. -/
inductive Mode where
  | checked
  | unchecked
  deriving DecidableEq, Repr

namespace Fx

variable {t : FxTy}

/-- The zero value: a type's default and what `delete` writes. -/
def zero (t : FxTy) : Fx t :=
  ⟨0, by
    have := t.half_pos
    simp only [FxTy.inRange, FxTy.lo, FxTy.hi, Bool.and_eq_true, decide_eq_true_eq]
    have := t.pow_bits
    cases t.signed <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega⟩

/-- A scaled integer at a type, range-checked. -/
def ofInt? (t : FxTy) (v : Int) : Option (Fx t) :=
  if h : t.inRange v = true then some ⟨v, h⟩ else none

/-- A scaled integer wrapped into the type's range modulo `2^M`, two's
complement where signed. -/
def wrapInt (t : FxTy) (v : Int) : Int :=
  if t.signed ∧ 2 ^ (t.bits - 1) ≤ v % 2 ^ t.bits then v % 2 ^ t.bits - 2 ^ t.bits
  else v % 2 ^ t.bits

theorem wrapInt_inRange (t : FxTy) (v : Int) : t.inRange (wrapInt t v) = true := by
  have hp := t.pow_bits
  have hh := t.half_pos
  have h0 : 0 ≤ v % 2 ^ t.bits := Int.emod_nonneg v (by omega)
  have h1 : v % 2 ^ t.bits < 2 ^ t.bits := Int.emod_lt_of_pos v (by omega)
  simp only [wrapInt, FxTy.inRange, FxTy.lo, FxTy.hi, Bool.and_eq_true, decide_eq_true_eq]
  cases t.signed <;> simp only [Bool.false_eq_true, false_and, true_and, if_false, if_true] <;>
    first | omega | (split <;> omega)

/-- A scaled integer wrapped into the type. -/
def wrap (t : FxTy) (v : Int) : Fx t := ⟨wrapInt t v, wrapInt_inRange t v⟩

/-- Wrapping keeps a scaled integer already in range. -/
theorem wrapInt_of_inRange {v : Int} (h : t.inRange v = true) : wrapInt t v = v := by
  have hp := t.pow_bits
  have hh := t.half_pos
  simp only [FxTy.inRange, FxTy.lo, FxTy.hi, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold wrapInt
  cases hs : t.signed
  · simp only [hs, Bool.false_eq_true, if_false] at h ⊢
    exact Int.emod_eq_of_lt h.1 (by omega)
  · simp only [hs, if_true] at h ⊢
    by_cases hv : 0 ≤ v
    · have hm : v % 2 ^ t.bits = v := Int.emod_eq_of_lt hv (by omega)
      simp only [hm, true_and]
      split <;> omega
    · have hm : v % 2 ^ t.bits = v + 2 ^ t.bits := by
        rw [← Int.add_emod_right]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      simp only [hm, true_and]
      split <;> omega

/-- Wrapping is the identity modulo `2^M`. -/
theorem wrapInt_emod (t : FxTy) (v : Int) : wrapInt t v % 2 ^ t.bits = v % 2 ^ t.bits := by
  unfold wrapInt
  split
  · rw [Int.sub_emod_right, Int.emod_emod]
  · rw [Int.emod_emod]

/-- The result of an operation from its exact scaled integer. -/
def result (m : Mode) (t : FxTy) (v : Int) : Except Fail (Fx t) :=
  match m with
  | .checked => if h : t.inRange v = true then .ok ⟨v, h⟩ else .error .overflow
  | .unchecked => .ok (wrap t v)

/-- A result in range is the exact one, in either mode. -/
theorem result_of_inRange (m : Mode) {v : Int} (h : t.inRange v = true) :
    result m t v = .ok ⟨v, h⟩ := by
  cases m
  · simp only [result, h, dite_true]
  · simp only [result, wrap, wrapInt_of_inRange h]

/-- A checked result out of range overflows. -/
theorem result_checked_overflow {v : Int} (h : t.inRange v = false) :
    result .checked t v = (.error .overflow : Except Fail (Fx t)) := by
  simp only [result, h, Bool.false_eq_true, dite_false]

/-- `a + b`. -/
def add (m : Mode) (a b : Fx t) : Except Fail (Fx t) := result m t (a.1 + b.1)

/-- `a - b`. -/
def sub (m : Mode) (a b : Fx t) : Except Fail (Fx t) := result m t (a.1 - b.1)

/-- `-a` (accepted at `ufixed` too, as solc's type checker does: there it
fails, or wraps, unless `a` is zero; Q5). -/
def neg (m : Mode) (a : Fx t) : Except Fail (Fx t) := result m t (-a.1)

/-- `a * b`: the exact product, its extra `N` digits truncated toward zero
(Q8, Q3). -/
def mul (m : Mode) (a b : Fx t) : Except Fail (Fx t) := result m t ((a.1 * b.1).tdiv t.scale)

/-- `a / b`: the exact quotient truncated toward zero at `N` digits (Q8, Q3). -/
def div (m : Mode) (a b : Fx t) : Except Fail (Fx t) :=
  if b.1 = 0 then .error .divZero else result m t ((a.1 * t.scale).tdiv b.1)

/-- `a % b`: `a - b · trunc(a / b)`, the sign of `a` (solc's rational `%`). -/
def mod (m : Mode) (a b : Fx t) : Except Fail (Fx t) :=
  if b.1 = 0 then .error .divZero else result m t (a.1.tmod b.1)

/-- `++a`: adds the value `1` (Q6). -/
def inc (m : Mode) (a : Fx t) : Except Fail (Fx t) := result m t (a.1 + t.scale)

/-- `--a`: subtracts the value `1`. -/
def dec (m : Mode) (a : Fx t) : Except Fail (Fx t) := result m t (a.1 - t.scale)

/-- `a < b`; the other comparisons are their integer ones on the scaled
integers likewise. -/
def lt (a b : Fx t) : Bool := decide (a.1 < b.1)

/-- `a <= b`. -/
def le (a b : Fx t) : Bool := decide (a.1 ≤ b.1)

/-- Two values of possibly different types denote the same number. -/
def SameValue {t' : FxTy} (a : Fx t) (b : Fx t') : Prop := a.1 * t'.scale = b.1 * t.scale

/-! ### Laws -/

/-- In either mode, addition without overflow is the scaled integer addition. -/
theorem add_eq (m : Mode) (a b : Fx t) (h : t.inRange (a.1 + b.1) = true) :
    add m a b = .ok ⟨a.1 + b.1, h⟩ := result_of_inRange m h

/-- Checked addition with overflow panics (`0x11`). -/
theorem add_overflow (a b : Fx t) (h : t.inRange (a.1 + b.1) = false) :
    add .checked a b = .error .overflow := result_checked_overflow h

/-- Unchecked addition wraps the scaled integer addition. -/
theorem add_unchecked (a b : Fx t) : add .unchecked a b = .ok (wrap t (a.1 + b.1)) := rfl

theorem add_comm (m : Mode) (a b : Fx t) : add m a b = add m b a := by
  simp only [add, Int.add_comm]

theorem mul_comm (m : Mode) (a b : Fx t) : mul m a b = mul m b a := by
  simp only [mul, Int.mul_comm]

/-- In either mode, subtraction without overflow is the scaled integer
subtraction. -/
theorem sub_eq (m : Mode) (a b : Fx t) (h : t.inRange (a.1 - b.1) = true) :
    sub m a b = .ok ⟨a.1 - b.1, h⟩ := result_of_inRange m h

/-- Adding zero. -/
theorem add_zero (m : Mode) (a : Fx t) : add m a (zero t) = .ok a := by
  have h : t.inRange (a.1 + 0) = true := by rw [Int.add_zero]; exact a.2
  rw [add_eq m a (zero t) h]
  exact congrArg Except.ok (Subtype.ext (Int.add_zero a.1))

/-- Multiplying by the value `1`, where the type holds it. -/
theorem mul_one (m : Mode) (a : Fx t) (h1 : t.inRange t.scale = true) :
    mul m a ⟨t.scale, h1⟩ = .ok a := by
  have he : (a.1 * t.scale).tdiv t.scale = a.1 :=
    Int.mul_tdiv_cancel a.1 (by have := t.scale_pos; omega)
  simp only [mul, he]
  exact result_of_inRange m a.2

/-- `a / 0` panics (`0x12`) in either mode. -/
theorem div_zero (m : Mode) (a : Fx t) : div m a (zero t) = .error .divZero := by
  simp only [div, zero, if_true]

/-- `a % 0` panics (`0x12`) in either mode. -/
theorem mod_zero (m : Mode) (a : Fx t) : mod m a (zero t) = .error .divZero := by
  simp only [mod, zero, if_true]

/-- `|a tmod b| ≤ |a|`, with the sign of `a`. -/
theorem tmod_between (x y : Int) : (0 ≤ x → 0 ≤ x.tmod y ∧ x.tmod y ≤ x) ∧
    (x < 0 → x ≤ x.tmod y ∧ x.tmod y ≤ 0) := by
  rcases x with m | m <;> rcases y with n | n <;>
    simp only [Int.tmod, Int.ofNat_eq_coe, Nat.succ_eq_add_one] <;>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    have := Nat.mod_le m n <;> have := Nat.mod_le m (n + 1) <;>
    have := Nat.mod_le (m + 1) n <;> have := Nat.mod_le (m + 1) (n + 1) <;> omega

/-- `%` never overflows: its result lies between `0` and the dividend. -/
theorem mod_inRange (a b : Fx t) : t.inRange (a.1.tmod b.1) = true := by
  have ha := a.2
  have hb := tmod_between a.1 b.1
  simp only [FxTy.inRange, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
  have hl : t.lo ≤ 0 := by
    have := t.half_pos
    simp only [FxTy.lo]; split <;> omega
  have hu : 0 ≤ t.hi := by
    have := t.half_pos
    have := t.pow_bits
    simp only [FxTy.hi]; split <;> omega
  by_cases h : 0 ≤ a.1
  · have := hb.1 h; omega
  · have := hb.2 (by omega); omega

/-- `a % b` for a nonzero `b`, in either mode: the truncated remainder. -/
theorem mod_eq (m : Mode) (a b : Fx t) (hb : b.1 ≠ 0) :
    mod m a b = .ok ⟨a.1.tmod b.1, mod_inRange a b⟩ := by
  simp only [mod, hb, if_false]
  exact result_of_inRange m (mod_inRange a b)

/-- In either mode, division by a nonzero divisor without overflow is the
truncated scaled quotient. -/
theorem div_eq (m : Mode) (a b : Fx t) (hb : b.1 ≠ 0)
    (h : t.inRange ((a.1 * t.scale).tdiv b.1) = true) :
    div m a b = .ok ⟨(a.1 * t.scale).tdiv b.1, h⟩ := by
  simp only [div, hb, if_false]
  exact result_of_inRange m h

/-- Comparison is the order of the denoted numbers. -/
theorem lt_iff (a b : Fx t) : lt a b = true ↔ a.1 < b.1 := by
  simp only [lt, decide_eq_true_eq]

/-! ### Conversions -/

/-- Rescaling a scaled integer from `n` to `n'` digits: exact when digits
are added, truncated toward zero when they are dropped. -/
def rescale (n n' : Nat) (v : Int) : Int :=
  if n ≤ n' then v * 10 ^ (n' - n) else v.tdiv (10 ^ (n - n'))

end Fx

namespace FxTy

/-- Every value of `t` is a value of `t'`: no digit dropped and both scaled
bounds in range. -/
def subsumes (t t' : FxTy) : Bool :=
  decide (t.digits ≤ t'.digits) && t'.inRange (t.lo * 10 ^ (t'.digits - t.digits)) &&
    t'.inRange (t.hi * 10 ^ (t'.digits - t.digits))

/-- solc's implicit conversion test between fixed-point types
(`FixedPointType::isImplicitlyConvertibleTo`): enough digits and bits, and
the integer parts in range.  It accepts lossy conversions (`solc_lossy`). -/
def solcImplicit (t t' : FxTy) : Bool :=
  decide (t.digits ≤ t'.digits) && decide (t.bits ≤ t'.bits) &&
    decide (t.maxInt ≤ t'.maxInt) && decide (t'.minInt ≤ t.minInt)

/-- The implicit conversion: solc's, restricted to the exact ones (the
user's answer to Q1 of the document); `FxTy.implicitOK_iff` (`FixedPoint/Laws.lean`)
proves it equal to `subsumes`. -/
def implicitOK (t t' : FxTy) : Bool := solcImplicit t t' && subsumes t t'

/-- The type a binary operation or comparison of `t` and `t'` runs at
(solc's `Type::commonType`): the left one if the right converts to it, else
the right one if the left converts, else the operation is refused. -/
def common? (t t' : FxTy) : Option FxTy :=
  if implicitOK t' t then some t else if implicitOK t t' then some t' else none

/-- solc's implicit integer-to-fixed test (`IntegerType::isImplicitlyConvertibleTo`),
the integer type given by its bounds. -/
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

/-- The implicit conversion along `subsumes`: exact. -/
def implicit (h : t.subsumes t' = true) (a : Fx t) : Fx t' :=
  ⟨a.1 * 10 ^ (t'.digits - t.digits), inRange_mul_of_subsumes h a⟩

/-- The implicit conversion keeps the number. -/
theorem implicit_sameValue (h : t.subsumes t' = true) (a : Fx t) : SameValue a (implicit h a) := by
  have hd : t.digits ≤ t'.digits := by
    simp only [FxTy.subsumes, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  simp only [SameValue, implicit, FxTy.scale]
  have hp : (10 : Int) ^ t'.digits = 10 ^ (t'.digits - t.digits) * 10 ^ t.digits := by
    rw [← Int.pow_add, Nat.sub_add_cancel hd]
  rw [hp, Int.mul_assoc]

/-- The implicit conversion keeps the order. -/
theorem implicit_lt (h : t.subsumes t' = true) (a b : Fx t) :
    lt (implicit h a) (implicit h b) = lt a b := by
  have hc : (0 : Int) < 10 ^ (t'.digits - t.digits) := Int.pow_pos (by decide)
  simp only [lt, implicit]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hl
    exact Int.lt_of_mul_lt_mul_right hl (Int.le_of_lt hc)
  · intro hl
    exact Int.mul_lt_mul_of_pos_right hl hc

/-- An explicit conversion of a run-time value: rescale (truncating toward
zero, Q3), then wrap modulo `2^M'`, as explicit integer conversions cut
higher-order bits and never fail (Q2).  An explicit conversion of a constant
is `explicitConst?`. -/
def explicit (t' : FxTy) (a : Fx t) : Fx t' :=
  wrap t' (rescale t.digits t'.digits a.1)

/-- Where the implicit conversion exists, the explicit one is it. -/
theorem explicit_of_subsumes (h : t.subsumes t' = true) (a : Fx t) :
    explicit t' a = implicit h a := by
  have hd : t.digits ≤ t'.digits := by
    simp only [FxTy.subsumes, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  simp only [explicit, rescale, hd, if_true, wrap, implicit,
    wrapInt_of_inRange (inRange_mul_of_subsumes h a)]

/-- An integer accepted by solc's implicit integer-to-fixed test is in
range once scaled: that conversion never fails. -/
theorem ofInteger_inRange {lo hi k : Int} (h : t.intImplicit lo hi = true)
    (hk : lo ≤ k ∧ k ≤ hi) : t.inRange (k * t.scale) = true := by
  have hs := t.scale_pos
  have hp := t.pow_bits
  have hh := t.half_pos
  simp only [FxTy.intImplicit, FxTy.maxInt, FxTy.minInt, Bool.and_eq_true, decide_eq_true_eq] at h
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

/-- An explicit integer-to-fixed conversion of a run-time value (solc admits
it where the implicit one exists and at the same width and signedness), by
value (Q7): the integer scaled, wrapped modulo `2^M` (Q2). -/
def ofIntegerExplicit (t : FxTy) (k : Int) : Fx t := wrap t (k * t.scale)

/-- Where solc's implicit integer-to-fixed conversion exists, the explicit
one is it: the exact scaled integer. -/
theorem ofIntegerExplicit_of_implicit {lo hi k : Int} (h : t.intImplicit lo hi = true)
    (hk : lo ≤ k ∧ k ≤ hi) :
    ofIntegerExplicit t k = ⟨k * t.scale, ofInteger_inRange h hk⟩ := by
  simp only [ofIntegerExplicit, wrap, wrapInt_of_inRange (ofInteger_inRange h hk)]

/-- An explicit `bytesM`-to-fixed conversion (solc admits it at the same
width), by bit pattern: the bytes' unsigned integer `u < 2^M` is the scaled
integer, two's complement where signed (Q7). -/
def ofBits (t : FxTy) (u : Int) : Fx t := wrap t u

/-- An explicit conversion to an integer, by value (Q7): the
integer part, truncated toward zero (then the integer type's own explicit
conversion). -/
def toIntTrunc (a : Fx t) : Int := a.1.tdiv t.scale

/-! ### Literals -/

/-- A rational literal `num / den` converted implicitly: only when it has at
most `N` digits and fits (solc's `RationalNumberType::isImplicitlyConvertibleTo`). -/
def ofLiteral? (t : FxTy) (num : Int) (den : Nat) : Option (Fx t) :=
  if den = 0 then none
  else if (num * t.scale) % den = 0 then ofInt? t ((num * t.scale) / den) else none

/-- A rational literal's scaled integer at `N` digits, truncated toward
zero (Q3): what an explicit conversion folds exactly. -/
def literalTrunc (t : FxTy) (num : Int) (den : Nat) : Int := (num * t.scale).tdiv den

/-- An explicit conversion of a constant `num / den`, folded exactly at the
target's digits: `none`, a compile error, when it does not fit (Q2), as an
explicit conversion of an out-of-range literal to an integer type is. -/
def explicitConst? (t : FxTy) (num : Int) (den : Nat) : Option (Fx t) :=
  if den = 0 then none else ofInt? t (literalTrunc t num den)

/-! ### ABI -/

/-- The ABI word (`enc(X · 10^N)` as an `int256`/`uint256`): two's
complement modulo `2^256`. -/
def toWord (a : Fx t) : Int := a.1 % 2 ^ 256

/-- A word `0 ≤ w < 2^256` (the premise of every caller) decoded at the
type: read as `int256` where signed, then
range-checked, so a word whose high bits are not the sign extension fails
(`none`), as solc's decoder rejects a dirty `intM`. -/
def ofWord? (t : FxTy) (w : Int) : Option (Fx t) :=
  ofInt? t (if t.signed ∧ 2 ^ 255 ≤ w then w - 2 ^ 256 else w)

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

/-- Decoding the encoding gives the value back. -/
theorem ofWord_toWord (a : Fx t) : ofWord? t (toWord a) = some a := by
  have ha := a.2
  have hp := t.pow_bits
  have hh := t.half_pos
  have hle := pow_bits_le t
  have h256 : (2 : Int) ^ 256 = 2 * 2 ^ 255 := by rw [Int.pow_succ, Int.mul_comm]
  simp only [FxTy.inRange, FxTy.lo, FxTy.hi, Bool.and_eq_true, decide_eq_true_eq] at ha
  have hw : (if t.signed ∧ 2 ^ 255 ≤ toWord a then toWord a - 2 ^ 256 else toWord a) = a.1 := by
    unfold toWord
    cases hs : t.signed
    · simp only [hs, Bool.false_eq_true, if_false, false_and] at ha ⊢
      exact Int.emod_eq_of_lt ha.1 (by omega)
    · simp only [hs, if_true, true_and] at ha ⊢
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

/-! ### Worked values -/

/-- `fixed8x1`: −12.8 … 12.7. -/
def fixed8x1 : FxTy := ⟨true, 8, 1, by decide⟩
/-- `ufixed8x2`: 0 … 2.55. -/
def ufixed8x2 : FxTy := ⟨false, 8, 2, by decide⟩
/-- `ufixed16x2`: 0 … 655.35. -/
def ufixed16x2 : FxTy := ⟨false, 16, 2, by decide⟩
/-- `fixed16x2`: −327.68 … 327.67. -/
def fixed16x2 : FxTy := ⟨true, 16, 2, by decide⟩
/-- `fixed8x3`: −0.128 … 0.127. -/
def fixed8x3 : FxTy := ⟨true, 8, 3, by decide⟩
/-- `ufixed8x3`: 0 … 0.255. -/
def ufixed8x3 : FxTy := ⟨false, 8, 3, by decide⟩
/-- `ufixed8x4`: 0 … 0.0255. -/
def ufixed8x4 : FxTy := ⟨false, 8, 4, by decide⟩

/-- solc's scanner bounds: `fixed8x0` and `ufixed256x80` are types,
`fixed7x8`, `fixed264x1` and `fixed8x81` are not (they are identifiers). -/
example : (FxTy.mk? true 8 0).isSome ∧ (FxTy.mk? false 256 80).isSome ∧
    (FxTy.mk? true 7 8).isNone ∧ (FxTy.mk? true 264 1).isNone ∧
    (FxTy.mk? true 8 81).isNone := by
  decide

/-- The upstream literal tests (`types/rational_number_literal_to_fixed_implicit.sol`,
`parsing/declaring_fixed_literal_variables.sol`): `fixed8x1` holds `-12.8`
and `12.7`, `ufixed8x2` holds `2.55`, `fixed40x40` does not hold `3.14`. -/
example : (ofLiteral? fixed8x1 (-128) 10).isSome ∧ (ofLiteral? fixed8x1 127 10).isSome ∧
    (ofLiteral? ufixed8x2 255 100).isSome ∧ (ofLiteral? fixed8x1 128 10).isNone ∧
    (ofLiteral? ⟨true, 40, 40, by decide⟩ 314 100).isNone := by
  decide +kernel

/-- `ufixed8x1(1/3)` folds to `0.3`; `ufixed8x1(100.5)` is a compile error,
where solc's type checker admits it. -/
example : (explicitConst? ⟨false, 8, 1, by decide⟩ 1 3).map Subtype.val = some 3 ∧
    (explicitConst? ⟨false, 8, 1, by decide⟩ 201 2).isNone := by
  decide

/-- solc's implicit fixed-to-fixed test accepts lossy conversions:
`fixed8x3 → ufixed8x3` (whose integer parts are both `0`) loses `-0.128`, and
`ufixed8x3 → ufixed8x4` loses `0.255`; the implicit test (`FxTy.implicitOK`, Q1) refuses both. -/
theorem solc_lossy :
    FxTy.solcImplicit fixed8x3 ufixed8x3 = true ∧ FxTy.subsumes fixed8x3 ufixed8x3 = false ∧
    FxTy.solcImplicit ufixed8x3 ufixed8x4 = true ∧ FxTy.subsumes ufixed8x3 ufixed8x4 = false := by
  decide +kernel

/-- Division truncates toward zero: `1.00 / 3.00 = 0.33` and
`-1.00 / 3.00 = -0.33` at two digits. -/
example : (div .checked (⟨100, by decide⟩ : Fx ufixed16x2) ⟨300, by decide⟩).toOption.map
      Subtype.val = some 33 ∧
    (div .checked (⟨-100, by decide⟩ : Fx fixed16x2) ⟨300, by decide⟩).toOption.map
      Subtype.val = some (-33) := by
  decide

/-- `-(-12.8)` overflows at `fixed8x1`; unchecked it wraps back to `-12.8`. -/
example : (neg .checked (⟨-128, by decide⟩ : Fx fixed8x1)).toOption.isNone ∧
    (neg .unchecked (⟨-128, by decide⟩ : Fx fixed8x1)).toOption.map Subtype.val =
      some (-128) := by
  decide

/-- At `ufixed16x2`, `2.55 * 2.00 = 5.10`; `255.00 * 3.00` overflows, and
unchecked it wraps `76500` to `76500 - 65536`. -/
example : (mul .checked (⟨255, by decide⟩ : Fx ufixed16x2) ⟨200, by decide⟩).toOption.map
      Subtype.val = some 510 ∧
    (mul .checked (⟨25500, by decide⟩ : Fx ufixed16x2) ⟨300, by decide⟩).toOption.isNone ∧
    (mul .unchecked (⟨25500, by decide⟩ : Fx ufixed16x2) ⟨300, by decide⟩).toOption.map
      Subtype.val = some (76500 - 65536) := by
  decide

/-- `%` keeps the dividend's sign: `-3.50 % 1.00 = -0.50`. -/
example : (mod .checked (⟨-350, by decide⟩ : Fx fixed16x2) ⟨100, by decide⟩).toOption.map
      Subtype.val = some (-50) := by
  decide

end Fx

end Solidity.Language.FixedPoint
