import Solidity.Semantics.Core.Value

/-!
# Operators on typed values

The operators at their operand types (`docs/intrinsic.md`, M4a): a typed
operator takes values of its operand type and gives one of its result type
(`BinOp.ret`, `UnOp.ret`), or `none` where it reverts (a result out of range,
a zero divisor, a negative exponent).  Arithmetic is on `Int`, as the untyped
`applyBinOp` computes it, and the range check is `PrimTy.ofInt?`, which reads
`checkArith`'s bounds; so the kernel meets the same `Int` terms as before
(56642ee).

`BinOp.evalT_erase` and `UnOp.evalT_erase` are the agreement with
`evalBinop` and `applyUnOp`/`unopCheck`: on an operand type the operator
accepts, the untyped operator is the typed one erased, so it is never stuck
(`asInt`/`asBool`, `checkArith`'s junk arms).  `-x` is accepted at `int`
only (`UnOp.accepts`), as solc accepts it.
-/

namespace Solidity

open Core (toRes)

/-- An integer at a type, range-checked as `checkArith` checks it: `none`
outside the range, and at `bool`. -/
def PrimTy.ofInt? (p : PrimTy) (n : Int) : Option p.Denote := PrimTy.ofValue? p (.int n)

/-- `checkArith` is `ofInt?` erased, at a numeric type. -/
theorem PrimTy.checkArith_ofInt {p : PrimTy} (hp : p.isNumeric = true) (n : Int) :
    Semantics.checkArith (.prim p) (.int n) = toRes PrimTy.erase (p.ofInt? n) := by
  cases p with
  | bool => cases hp
  | uint =>
    simp only [Semantics.checkArith, PrimTy.ofInt?, PrimTy.ofValue?, PrimTy.inRange,
      Semantics.uintBound, decide_eq_true_eq]
    by_cases hb : 0 ≤ n ∧ n < ((2 ^ 256 : Nat) : Int)
    · rw [if_pos hb, dif_pos hb]; rfl
    · rw [if_neg hb, dif_neg hb]; rfl
  | int =>
    simp only [Semantics.checkArith, PrimTy.ofInt?, PrimTy.ofValue?, PrimTy.inRange,
      Semantics.intBound, decide_eq_true_eq]
    by_cases hb : -((2 ^ 255 : Nat) : Int) ≤ n ∧ n < ((2 ^ 255 : Nat) : Int)
    · rw [if_pos hb, dif_pos hb]; rfl
    · rw [if_neg hb, dif_neg hb]; rfl

namespace BinOp

/-- An arithmetic operator on integers, before the range check
(`applyBinOp`): `none` where it reverts. -/
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

/-- `applyBinOp` on two integers is `arithInt`, at an arithmetic operator. -/
theorem applyBinOp_int {op : BinOp} (hA : op.isArith = true) (x y : Int) :
    Semantics.applyBinOp op (.int x) (.int y) = toRes Semantics.Value.int (arithInt op x y) := by
  cases op <;> simp only [isArith, Bool.false_eq_true] at hA <;>
    simp only [Semantics.applyBinOp, arithInt, Semantics.Value.asInt, bind, Except.bind] <;>
    first | rfl | (split <;> rfl)

/-- An arithmetic operator: `applyBinOp`, then the range check. -/
theorem evalBinop_arith {op : BinOp} (hA : op.isArith = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : Int) :
    evalBinop op p (.int x) (.ok (.int y)) =
      toRes PrimTy.erase ((arithInt op x y).bind p.ofInt?) := by
  have hb : evalBinop op p (.int x) (.ok (.int y)) =
      Except.bind (Semantics.applyBinOp op (.int x) (.int y)) (Semantics.checkArith (.prim p)) := by
    cases op <;> simp only [isArith, Bool.false_eq_true] at hA <;> rfl
  rw [hb, applyBinOp_int hA]
  cases arithInt op x y with
  | none => rfl
  | some n => exact PrimTy.checkArith_ofInt hp n

/-- **`evalBinop` is `evalT` erased**, at an operand type the operator
accepts: the untyped operator is never stuck there. -/
theorem evalT_erase (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (a b : p.Denote) :
    evalBinop op p (PrimTy.erase a) (.ok (PrimTy.erase b)) = toRes PrimTy.erase (op.evalT a b) := by
  cases p <;> cases op <;> (first | exact absurd h (by decide) | skip)
  all_goals first
    | exact evalBinop_arith rfl rfl a.1 b.1
    | rfl
    | (cases a <;> rfl)
    | (simp only [evalBinop, Semantics.applyBinOp, Semantics.checkArith, evalT, evalNum,
        evalBool, toRes, bind, Except.bind, PrimTy.erase, Semantics.PrimVal.int.injEq,
        Semantics.PrimVal.bool.injEq] <;> rfl)

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

/-- **`applyUnOp` then `unopCheck` is `evalT` erased**, at an operand type the
operator accepts. -/
theorem evalT_erase (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (a : p.Denote) :
    (do unopCheck op p (← Semantics.applyUnOp op (PrimTy.erase a))) =
      toRes PrimTy.erase (op.evalT a) := by
  cases op <;> cases p <;> first | exact absurd h (by decide) | skip
  · exact PrimTy.checkArith_ofInt (p := .int) rfl _
  · rfl
  · have hx := a.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at hx
    have h' : PrimTy.uint.inRange (Semantics.uintBound - 1 - a.1) = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq, Semantics.uintBound]
      omega
    simp only [evalT, PrimTy.ofInt?, PrimTy.ofValue?, dif_pos h']
    rfl

end UnOp

end Solidity
