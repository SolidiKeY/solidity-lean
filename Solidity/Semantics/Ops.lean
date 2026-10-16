import Solidity.Semantics.Value

/-!
# Operators on typed values

The operators at their operand types (`docs/intrinsic.md`, M4a): a typed
operator takes values of its operand type and gives one of its result type
(`BinOp.ret`, `UnOp.ret`), or `none` where it reverts (a result out of range,
a zero divisor, a negative exponent).  Arithmetic is on `Int` (`arithInt`,
the bounds `Semantics.uintBound`/`intBound`), and the range check is
`PrimTy.ofInt?`; so the kernel never unfolds `Nat.land` on a `uint`
(56642ee).  `-x` is accepted at `int` only (`UnOp.accepts`), as solc
accepts it.
-/

namespace Solidity

namespace Semantics

/-- `2^256`, the exclusive upper bound of `uint256` (cast from `Nat`,
where kernel arithmetic on the literal is fast). -/
def uintBound : Int := ((2 ^ 256 : Nat) : Int)

/-- `2^255`, the exclusive upper bound (and negated inclusive lower
bound) of `int256`. -/
def intBound : Int := ((2 ^ 255 : Nat) : Int)

/-- `&&&`, `|||` or `^^^` on two `uint` words, behind a match on the operands:
the kernel meets `Nat.land` only on numerals, where it computes it, and never
unfolds it (well-founded recursion, a deep-recursion error), even when an
operand is still a read of the state.  A negative operand, which `uint`
rules out, gives `0`. -/
def uintBitwise (f : Nat → Nat → Nat) : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (f a b)
  | _, _ => 0

theorem uintBitwise_natCast (f : Nat → Nat → Nat) (a b : Nat) :
    uintBitwise f (a : Int) (b : Int) = ((f a b : Nat) : Int) := rfl

end Semantics

namespace BinOp

/-- An arithmetic operator on integers, before the range check: `none`
where it reverts. -/
def arithInt : BinOp → Int → Int → Option Int
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .pow, x, y => if y < 0 then none else some (x ^ y.toNat)
  | .div, x, y => if y = 0 then none else some (Int.tdiv x y)
  | .mod, x, y => if y = 0 then none else some (Int.tmod x y)
  | .band, x, y => some (Semantics.uintBitwise (· &&& ·) x y)
  | .bor, x, y => some (Semantics.uintBitwise (· ||| ·) x y)
  | .bxor, x, y => some (Semantics.uintBitwise (· ^^^ ·) x y)
  | .shl, a, n => some (if n < 256 then a * 2 ^ n.toNat % Semantics.uintBound else 0)
  | .shr, a, n => some (if n < 256 then a / 2 ^ n.toNat else 0)
  | .addW, x, y => some ((x + y) % Semantics.uintBound)
  | .subW, x, y => some ((x - y) % Semantics.uintBound)
  | .mulW, x, y => some (x * y % Semantics.uintBound)
  | .powW, x, y => if y < 0 then none else some (x ^ y.toNat % Semantics.uintBound)
  | .lt, _, _ | .gt, _, _ | .le, _, _ | .ge, _, _ | .eqB, _, _ | .neB, _, _ | .and, _, _
  | .or, _, _ => none

/-- An operator at a numeric type, on the integers its operands hold:
`&&` and `||` take no number (`accepts`). -/
def evalNum (p : PrimTy) (hp : p.isNumeric = true) (x y : Int) :
    (op : BinOp) → op.accepts p = true → Option (op.ret p).Denote
  | .add, _ => (arithInt .add x y).bind p.ofInt?
  | .sub, _ => (arithInt .sub x y).bind p.ofInt?
  | .mul, _ => (arithInt .mul x y).bind p.ofInt?
  | .pow, _ => (arithInt .pow x y).bind p.ofInt?
  | .div, _ => (arithInt .div x y).bind p.ofInt?
  | .mod, _ => (arithInt .mod x y).bind p.ofInt?
  | .band, _ => (arithInt .band x y).bind p.ofInt?
  | .bor, _ => (arithInt .bor x y).bind p.ofInt?
  | .bxor, _ => (arithInt .bxor x y).bind p.ofInt?
  | .shl, _ => (arithInt .shl x y).bind p.ofInt?
  | .shr, _ => (arithInt .shr x y).bind p.ofInt?
  | .addW, _ => (arithInt .addW x y).bind p.ofInt?
  | .subW, _ => (arithInt .subW x y).bind p.ofInt?
  | .mulW, _ => (arithInt .mulW x y).bind p.ofInt?
  | .powW, _ => (arithInt .powW x y).bind p.ofInt?
  | .lt, _ => some (decide (x < y))
  | .gt, _ => some (decide (y < x))
  | .le, _ => some (decide (x ≤ y))
  | .ge, _ => some (decide (y ≤ x))
  | .eqB, _ => some (decide (x = y))
  | .neB, _ => some (!decide (x = y))
  | .and, h => absurd h (by cases p <;> simp_all [BinOp.accepts, PrimTy.isNumeric])
  | .or, h => absurd h (by cases p <;> simp_all [BinOp.accepts, PrimTy.isNumeric])

/-- An operator at `bool`: only `==`, `!=`, `&&` and `||` take one
(`accepts`). -/
def evalBool (a b : Bool) : (op : BinOp) → op.accepts .bool = true → Option (op.ret .bool).Denote
  | .eqB, _ => some (decide (a = b))
  | .neB, _ => some (!decide (a = b))
  | .and, _ => some (a && b)
  | .or, _ => some (a || b)
  | .add, h | .sub, h | .mul, h | .pow, h | .div, h | .mod, h | .band, h | .bor, h | .bxor, h
  | .shl, h | .shr, h | .addW, h | .subW, h | .mulW, h | .powW, h | .lt, h | .gt, h | .le, h
  | .ge, h => absurd h (by decide)

/-- `a ⊕ b` on typed values, at a type the operator takes: `none` where it
reverts. -/
def evalT (op : BinOp) : {p : PrimTy} → op.accepts p = true → p.Denote → p.Denote →
    Option (op.ret p).Denote
  | .bool, h, a, b => evalBool a b op h
  | .uint, h, a, b => evalNum .uint rfl a.1 b.1 op h
  | .int, h, a, b => evalNum .int rfl a.1 b.1 op h

end BinOp

namespace ModOp

/-- `addmod`/`mulmod` compute before the final reduction, without word wrapping. -/
def wide : ModOp → Int → Int → Int
  | .addmod, x, y => x + y
  | .mulmod, x, y => x * y

/-- Solidity's modular builtin: a zero modulus fails, as division by zero does.
Only the final remainder is converted back to a `uint256`. -/
def evalT (op : ModOp) (x y k : PrimTy.uint.Denote) : Option PrimTy.uint.Denote :=
  if k.val = 0 then none else PrimTy.uint.ofInt? (op.wide x.val y.val % k.val)

/-- A nonzero unsigned modulus puts the wide remainder back in range. -/
theorem remainder_inRange (op : ModOp) (x y k : PrimTy.uint.Denote)
    (hk : k.val ≠ 0) : PrimTy.uint.inRange (op.wide x.val y.val % k.val) = true := by
  have h : PrimTy.uint.inRange k.val = true := k.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h ⊢
  exact ⟨Int.emod_nonneg _ hk, Int.lt_trans (Int.emod_lt_of_pos _ (by omega)) h.2⟩

end ModOp

namespace UnOp

/-- `⊖ a` on a typed value, at a type the operator takes: `none` where it
reverts. -/
def evalT : (op : UnOp) → {p : PrimTy} → op.accepts p = true → p.Denote → Option (op.ret p).Denote
  | .neg, .int, _, a => PrimTy.int.ofInt? (-a.1)
  | .not, .bool, _, a => some (!a)
  | .bnot, .uint, _, a => PrimTy.uint.ofInt? (Semantics.uintBound - 1 - a.1)
  | .neg, .uint, h, _ | .neg, .bool, h, _ | .not, .uint, h, _ | .not, .int, h, _
  | .bnot, .bool, h, _ | .bnot, .int, h, _ => absurd h (by decide)

end UnOp

end Solidity
