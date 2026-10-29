import Solidity.Source.Syntax

/-!
# Compile-time constants (S01)

solc evaluates literal expressions exactly, as rational numbers
(`RationalNumberType`), before any conversion; a constant meets a type only
when it is converted implicitly or explicitly, and an out-of-range constant
is a compile error, never a wrapped value.  This module defines that
evaluation over S00's syntax (`Syn .expr`):

- `Q`: exact rationals (numerator, positive denominator), with `Q.Eqv` the
  equality of the denoted numbers;
- `NumLit.value` and `Denom.factor`: a literal's value, with its unit;
- `Syn.const`: the constant a literal expression denotes (`none` when it is
  not a compile-time number: a variable, a call, a division by zero, an
  exponent or shift beyond solc's bounds, a bitwise operation or shift on a
  non-integer);
- `Q.FitsInt`, `Q.toFixed?` and `Q.fitsBytes`: the implicit conversions of a
  constant (`Solidity/Source/Types.lean` uses them).

Bitwise operations on negative integers are two's complement of unbounded
width, as solc's `RationalNumberType` computes them (`Int.bitAnd` …).  The
fixed-point readings follow the second-round decisions
(`docs/solidity-scope.md`): a constant converts implicitly to `fixedMxN` only
exactly and in range; explicitly it is truncated toward zero at `N` digits,
and out of range it is a compile error.
-/

namespace Solidity.Source

/-- An exact rational: `num / den` with `den > 0` (not necessarily reduced). -/
structure Q where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

namespace Q

/-- The integer `k`. -/
def ofInt (k : Int) : Q := ⟨k, 1, by decide⟩

/-- Equality of the denoted numbers. -/
def Eqv (a b : Q) : Prop := a.num * b.den = b.num * a.den

instance (a b : Q) : Decidable (a.Eqv b) := inferInstanceAs (Decidable (_ = _))

def add (a b : Q) : Q := ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩
def neg (a : Q) : Q := ⟨-a.num, a.den, a.den_pos⟩
def sub (a b : Q) : Q := a.add b.neg
def mul (a b : Q) : Q := ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- `a / b`; `none` when `b` is zero (a compile error). -/
def div (a b : Q) : Option Q :=
  if h : b.num = 0 then none
  else Option.some ⟨a.num * b.den * b.num.sign, a.den * b.num.natAbs,
    Nat.mul_pos a.den_pos (Int.natAbs_pos.2 h)⟩

/-- Whether the number is an integer. -/
def isInt (a : Q) : Bool := a.num % a.den == 0

/-- The integer an integral number denotes. -/
def toInt (a : Q) : Int := a.num / a.den

/-- Truncation toward zero. -/
def trunc (a : Q) : Int := a.num.tdiv a.den

/-- `a % b = a - b · trunc(a / b)`, solc's rational remainder; `none` when
`b` is zero. -/
def mod (a b : Q) : Option Q := (a.div b).map fun q => a.sub (b.mul (ofInt q.trunc))

/-- The number of bits of `n`, capped at 4200 (beyond solc's bound):
structural, so it reduces in proofs. -/
def bitLen (n : Nat) : Nat := go 4200 n
where
  go : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, n => if n = 0 then 0 else 1 + go fuel (n / 2)

/-- The reduced form: numerator and denominator divided by their gcd. -/
def reduce (a : Q) : Q :=
  ⟨a.num / (Nat.gcd a.num.natAbs a.den : Int), a.den / Nat.gcd a.num.natAbs a.den,
    Nat.div_pos (Nat.le_of_dvd a.den_pos (Nat.gcd_dvd_right _ _)) (Nat.gcd_pos_of_pos_right _ a.den_pos)⟩

/-- solc's bound on exact constants: a result whose reduced numerator or
denominator has its most significant bit beyond position 4096 (more than
4097 bits) is a compile error ("Precision of rational constants is limited
to 4096 bits"). -/
def maxBits : Nat := 4096

/-- The bound, checked on the reduced result. -/
def bounded (a : Q) : Option Q :=
  let r := a.reduce
  if bitLen r.num.natAbs ≤ maxBits + 1 ∧ bitLen r.den ≤ maxBits + 1 then Option.some r else none

/-- `a ** k` for an integer exponent: bases `0` and `±1` always fold (a
zero base with a negative exponent divides by zero); otherwise `none` when
the result would exceed `maxBits` (solc's `fitsPrecisionExp`). -/
def pow (a : Q) (k : Int) : Option Q :=
  let r := a.reduce
  if r.den = 1 ∧ r.num.natAbs ≤ 1 then
    if 0 ≤ k then Option.some ⟨r.num ^ k.toNat, 1, by decide⟩
    else if r.num = 0 then none else Option.some ⟨r.num ^ k.natAbs, 1, by decide⟩
  else if bitLen r.num.natAbs * k.natAbs > maxBits ∨ bitLen r.den * k.natAbs > maxBits then none
  else if 0 ≤ k then bounded ⟨r.num ^ k.toNat, r.den ^ k.toNat, Nat.pow_pos r.den_pos⟩
  else ((ofInt 1).div ⟨r.num ^ k.natAbs, r.den ^ k.natAbs, Nat.pow_pos r.den_pos⟩).bind bounded

end Q

/-! ## Two's-complement bitwise operations on unbounded integers -/

/-- `~a = -a - 1`. -/
def Int.bitNot (a : Int) : Int := -a - 1

/-- `a & b`, two's complement. -/
def Int.bitAnd : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (b &&& a))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

/-- `a | b`, two's complement. -/
def Int.bitOr : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b ^^^ (b &&& a))
  | .negSucc a, .ofNat b => .negSucc (a ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

/-- `a ^ b`, two's complement. -/
def Int.bitXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-! ## Literals -/

/-- The value of a number literal. -/
def NumLit.value : NumLit → Q
  | .dec m f e =>
    if 0 ≤ e then ⟨m * 10 ^ e.toNat, 10 ^ f, Nat.pow_pos (by decide)⟩
    else ⟨m, 10 ^ (f + e.natAbs), Nat.pow_pos (by decide)⟩
  | .hex ds _ => Q.ofInt (ds.foldl (fun acc d => acc * 16 + d.val) 0)

/-- The factor of a unit: `wei`/`seconds` 1, `gwei` 10⁹, `ether` 10¹⁸, and
the time units in seconds (`years`, rejected by S00, is 365 days). -/
def Denom.factor : Denom → Nat
  | .wei => 1
  | .gwei => 10 ^ 9
  | .ether => 10 ^ 18
  | .seconds => 1
  | .minutes => 60
  | .hours => 3600
  | .days => 86400
  | .weeks => 604800
  | .years => 31536000

/-- An integral constant, or `none`. -/
def Q.int? (a : Q) : Option Int := if a.isInt then Option.some a.toInt else none

/-- Beyond this right shift, a constant is `0` or `-1` (avoiding the
computation of a huge power). -/
def maxShift : Nat := 4097

/-- **The constant a literal expression denotes**: number literals, units
(on decimal literals only: solc rejects a unit on a hexadecimal number),
parentheses, unary `-`/`~`, `+ - * / % **`, shifts and bitwise operations,
folded exactly and bounded as solc bounds them; anything else is not a
compile-time number. -/
def Syn.const : {c : Cat} → Syn c → Option Q
  | _, .lit (.num n) => Option.some n.value
  | _, .litUnit (.dec m f e) u => Option.some ((NumLit.dec m f e).value.mul (Q.ofInt u.factor))
  | _, .tuple (.some e) .nil => e.const
  | _, .unaryPrefix .neg e => e.const.map Q.neg
  | _, .unaryPrefix .bitNot e => do
      let k ← (← e.const).int?
      pure (Q.ofInt (Int.bitNot k))
  | _, .addSub .add a b => do ((← a.const).add (← b.const)).bounded
  | _, .addSub .sub a b => do ((← a.const).sub (← b.const)).bounded
  | _, .mulDivMod .mul a b => do ((← a.const).mul (← b.const)).bounded
  | _, .mulDivMod .div a b => do (← (← a.const).div (← b.const)).bounded
  | _, .mulDivMod .mod a b => do (← (← a.const).mod (← b.const)).bounded
  | _, .exp a b => do
      let k ← (← b.const).int?
      (← a.const).pow k
  | _, .shift .shl a b => do
      let x ← (← a.const).int?
      let y ← (← b.const).int?
      if x = 0 ∧ 0 ≤ y then pure (Q.ofInt 0)
      else if 0 ≤ y ∧ Q.bitLen x.natAbs + y.toNat ≤ Q.maxBits + 1 then pure (Q.ofInt (x * 2 ^ y.toNat))
      else Option.none
  | _, .shift .sar a b => do
      let x ← (← a.const).int?
      let y ← (← b.const).int?
      if 0 ≤ y then pure (Q.ofInt (if y.toNat ≤ maxShift then x.fdiv (2 ^ y.toNat) else if x < 0 then -1 else 0))
      else Option.none
  | _, .bitAnd a b => do
      pure (Q.ofInt (Int.bitAnd (← (← a.const).int?) (← (← b.const).int?)))
  | _, .bitOr a b => do
      pure (Q.ofInt (Int.bitOr (← (← a.const).int?) (← (← b.const).int?)))
  | _, .bitXor a b => do
      pure (Q.ofInt (Int.bitXor (← (← a.const).int?) (← (← b.const).int?)))
  | _, _ => Option.none

/-! ## Conversions of constants -/

/-- An integer type: signedness and a width that is a multiple of 8 in
`8 … 256`. -/
structure IntTy where
  signed : Bool
  bits : Nat
  valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256
  deriving DecidableEq, Repr

/-- The least value of an integer type.  Bounds are `Nat` powers cast to
`Int`, which reduce by literal arithmetic. -/
def IntTy.lo (t : IntTy) : Int := if t.signed then -((2 ^ (t.bits - 1) : Nat) : Int) else 0

/-- The greatest value of an integer type. -/
def IntTy.hi (t : IntTy) : Int :=
  if t.signed then ((2 ^ (t.bits - 1) - 1 : Nat) : Int) else ((2 ^ t.bits - 1 : Nat) : Int)

/-- A fixed-point type `fixedMxN`/`ufixedMxN` inside solc's bounds; its
fields are those of the fixed-point reference semantics' `FxTy`
(`docs/feature-work/fixed-point-semantics.md`, on its own branch), to be
identified with it when that module is integrated. -/
structure FixTy where
  signed : Bool
  bits : Nat
  digits : Nat
  valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 ∧ digits ≤ 80
  deriving DecidableEq, Repr

/-- `10^N`. -/
def FixTy.scale (t : FixTy) : Int := ((10 ^ t.digits : Nat) : Int)
/-- The least scaled integer. -/
def FixTy.lo (t : FixTy) : Int := if t.signed then -((2 ^ (t.bits - 1) : Nat) : Int) else 0
/-- The greatest scaled integer. -/
def FixTy.hi (t : FixTy) : Int :=
  if t.signed then ((2 ^ (t.bits - 1) - 1 : Nat) : Int) else ((2 ^ t.bits - 1 : Nat) : Int)

/-- An integral constant fits an integer type (an implicit conversion). -/
def Q.FitsInt (a : Q) (t : IntTy) : Prop := a.isInt = true ∧ t.lo ≤ a.toInt ∧ a.toInt ≤ t.hi

instance (a : Q) (t : IntTy) : Decidable (a.FitsInt t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Implicit conversion of a constant to a fixed-point type**: exact at `N`
digits and in range, the scaled integer it then has. -/
def Q.toFixed? (a : Q) (t : FixTy) : Option Int :=
  if (a.num * t.scale) % a.den = 0 then
    let v := (a.num * t.scale) / a.den
    if t.lo ≤ v ∧ v ≤ t.hi then Option.some v else none
  else none

/-- **Explicit conversion of a constant to a fixed-point type**: truncated
toward zero at `N` digits; out of range it is a compile error (`none`). -/
def Q.toFixedExplicit? (a : Q) (t : FixTy) : Option Int :=
  let v := (a.num * t.scale).tdiv a.den
  if t.lo ≤ v ∧ v ≤ t.hi then Option.some v else none

/-- **Explicit conversion of a constant to an integer type**: an integral
constant in range (solc rejects a non-integral or out-of-range constant). -/
def Q.toIntExplicit? (a : Q) (t : IntTy) : Option Int :=
  if a.FitsInt t then Option.some a.toInt else none

/-- A hexadecimal or decimal constant converts implicitly to `bytesN` only
when it is zero, or a hexadecimal literal of exactly `2N` digits (solc). -/
def NumLit.fitsBytes (n : NumLit) (len : Nat) : Bool :=
  match n with
  | .hex ds _ => ds.length == 2 * len || n.value.num == 0
  | .dec _ _ _ => n.value.num == 0

/-! ## Laws -/

theorem Q.ofInt_isInt (k : Int) : (Q.ofInt k).isInt = true := by
  simp only [Q.ofInt, Q.isInt, Int.natCast_one, Int.emod_one, beq_self_eq_true]

theorem Q.ofInt_toInt (k : Int) : (Q.ofInt k).toInt = k := by
  simp only [Q.ofInt, Q.toInt, Int.natCast_one, Int.ediv_one]

theorem Q.int?_ofInt (k : Int) : (Q.ofInt k).int? = Option.some k := by
  simp only [Q.int?, Q.ofInt_isInt, if_true, Q.ofInt_toInt]

/-- A constant converted implicitly to a fixed-point type denotes it
exactly: the scaled integer over `10^N` is the constant. -/
theorem Q.toFixed?_exact {a : Q} {t : FixTy} {v : Int} (h : a.toFixed? t = Option.some v) :
    v * a.den = a.num * t.scale := by
  simp only [Q.toFixed?] at h
  split at h
  · rename_i hm
    split at h
    · cases h
      exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hm)
    · cases h
  · cases h

/-- The implicit fixed-point conversion is in range. -/
theorem Q.toFixed?_inRange {a : Q} {t : FixTy} {v : Int} (h : a.toFixed? t = Option.some v) :
    t.lo ≤ v ∧ v ≤ t.hi := by
  simp only [Q.toFixed?] at h
  split at h
  · split at h
    · rename_i hr
      cases h
      exact hr
    · cases h
  · cases h

/-- An implicit conversion is an explicit one with the same value: the
exact case of truncation. -/
theorem Q.toFixedExplicit?_of_toFixed? {a : Q} {t : FixTy} {v : Int}
    (h : a.toFixed? t = Option.some v) : a.toFixedExplicit? t = Option.some v := by
  have he := Q.toFixed?_exact h
  have hr := Q.toFixed?_inRange h
  have hd : (a.den : Int) ≠ 0 := Int.ofNat_ne_zero.2 (Nat.pos_iff_ne_zero.1 a.den_pos)
  have hv : (a.num * t.scale).tdiv a.den = v := by
    rw [← he, Int.mul_tdiv_cancel _ hd]
  simp only [Q.toFixedExplicit?, hv, hr, and_self, if_true]

/-- An out-of-range constant has no explicit conversion: a compile error. -/
theorem Q.toFixedExplicit?_none {a : Q} {t : FixTy}
    (h : (a.num * t.scale).tdiv a.den < t.lo ∨ t.hi < (a.num * t.scale).tdiv a.den) :
    a.toFixedExplicit? t = none := by
  simp only [Q.toFixedExplicit?]
  split
  · rename_i hr; omega
  · rfl

end Solidity.Source
