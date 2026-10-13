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

/-- An integer at a type, range-checked: `none` outside the range, and at
`bool`. -/
def PrimTy.ofInt? (p : PrimTy) (n : Int) : Option p.Denote := PrimTy.ofValue? p (.int n)

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

/-- An operator at a numeric type, on the integers its operands hold. -/
def evalNum (p : PrimTy) (x y : Int) : (op : BinOp) → Option (op.ret p).Denote
  | .add => (arithInt .add x y).bind p.ofInt?
  | .sub => (arithInt .sub x y).bind p.ofInt?
  | .mul => (arithInt .mul x y).bind p.ofInt?
  | .pow => (arithInt .pow x y).bind p.ofInt?
  | .div => (arithInt .div x y).bind p.ofInt?
  | .mod => (arithInt .mod x y).bind p.ofInt?
  | .band => (arithInt .band x y).bind p.ofInt?
  | .bor => (arithInt .bor x y).bind p.ofInt?
  | .bxor => (arithInt .bxor x y).bind p.ofInt?
  | .shl => (arithInt .shl x y).bind p.ofInt?
  | .shr => (arithInt .shr x y).bind p.ofInt?
  | .addW => (arithInt .addW x y).bind p.ofInt?
  | .subW => (arithInt .subW x y).bind p.ofInt?
  | .mulW => (arithInt .mulW x y).bind p.ofInt?
  | .powW => (arithInt .powW x y).bind p.ofInt?
  | .lt => some (decide (x < y))
  | .gt => some (decide (y < x))
  | .le => some (decide (x ≤ y))
  | .ge => some (decide (y ≤ x))
  | .eqB => some (decide (x = y))
  | .neB => some (!decide (x = y))
  | .and => none
  | .or => none

/-- An operator at `bool`. -/
def evalBool (a b : Bool) : (op : BinOp) → Option (op.ret .bool).Denote
  | .eqB => some (decide (a = b))
  | .neB => some (!decide (a = b))
  | .and => some (a && b)
  | .or => some (a || b)
  | .add | .sub | .mul | .pow | .div | .mod | .band | .bor | .bxor | .shl | .shr | .addW
  | .subW | .mulW | .powW => none
  | .lt | .gt | .le | .ge => none

/-- `a ⊕ b` on typed values: `none` where it reverts. -/
def evalT (op : BinOp) : {p : PrimTy} → p.Denote → p.Denote → Option (op.ret p).Denote
  | .bool, a, b => evalBool a b op
  | .uint, a, b => evalNum .uint a.1 b.1 op
  | .int, a, b => evalNum .int a.1 b.1 op

end BinOp

namespace UnOp

/-- `⊖ a` on a typed value: `none` where it reverts, and at an operand type
the operator does not accept. -/
def evalT : (op : UnOp) → {p : PrimTy} → p.Denote → Option (op.ret p).Denote
  | .neg, .int, a => PrimTy.int.ofInt? (-a.1)
  | .neg, .uint, _ | .neg, .bool, _ => none
  | .not, .bool, a => some (!a)
  | .not, .uint, _ | .not, .int, _ => none
  | .bnot, .uint, a => PrimTy.uint.ofInt? (Semantics.uintBound - 1 - a.1)
  | .bnot, .bool, _ | .bnot, .int, _ => none

end UnOp

end Solidity
