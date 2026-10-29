import Solidity.Source.Observe
import Solidity.Source.Resolved

/-!
# Runtime values and their operations (S02)

The values S02's expression semantics computes, intrinsic in S01's static
types (`STy`), and the pure operations on them:

- `RVal D τ`: a value of an expression of type `τ`.  A value or reference
  type's value is S04.01's `Val D τ`; a constant (`.rational q`) and a string
  literal (`.stringLit bs`) carry no run-time data beyond their type, so their
  values are `const q` and `strLit bs`; a tuple is its components;
- `Halt`: how an evaluation stops early: a revert with its exact data
  (`Panic(uint256)` codes included, G01 Q5), a stuck state (a run-time type
  mismatch that well-formed programs never reach), or the end of the
  horizon (`timeout`, never a failure the source allows: the semantics is the
  family over every horizon);
- the arithmetic of solc 0.8: checked operations panic with `0x11` out of
  range and wrap inside `unchecked` (`IntTy.wrap`, `IntTy.wrap_mem`),
  division and modulo by zero panic with `0x12` in both modes, `/` and `%`
  truncate toward zero; fixed point by the second-round decisions (exact
  product and quotient truncated toward zero, `-x` on `ufixed` panics unless
  `x = 0`);
- shifts and powers by an unsigned amount, without computing a power beyond
  the type's width; bitwise operations in two's complement and bytewise on
  `bytesN`;
- implicit and explicit conversions between value types (`convVal`,
  `convExplicitVal`): integers by value, explicit integer conversions by bit
  pattern, enums from integers with `Panic(0x21)` out of range, fixed point
  rescaled and truncated toward zero then wrapped.

Reference conversions (copies, allocation) need the state and are in
`Solidity/Source/Eval.lean`.
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes)

mutual

/-- `STy.same` is equality: soundness. -/
theorem STy.eq_of_same : (a b : STy) → STy.same a b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp_all [STy.same] <;>
      first
      | exact STy.eq_of_same _ _ h.1.2
      | exact ⟨STy.eq_of_same _ _ h.1, STy.eq_of_same _ _ h.2⟩
      | exact ⟨STy.eq_of_sameList _ _ h.1.1.2, STy.eq_of_sameList _ _ h.1.2⟩
      | exact STy.eq_of_sameList _ _ h

theorem STy.eq_of_sameList : (a b : List STy) → STy.sameList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [STy.sameList, Bool.and_eq_true] at h
    rw [STy.eq_of_same x y h.1, STy.eq_of_sameList xs ys h.2]
  | [], _ :: _, h => by simp [STy.sameList] at h
  | _ :: _, [], h => by simp [STy.sameList] at h

end

mutual

/-- `STy.same` is reflexive. -/
theorem STy.same_refl : (a : STy) → STy.same a a = true
  | .array l t n => by simp only [STy.same, beq_self_eq_true, STy.same_refl t, Bool.and_self]
  | .mapping k v => by simp only [STy.same, STy.same_refl k, STy.same_refl v, Bool.and_self]
  | .fn e ps rs m => by
    simp only [STy.same, beq_self_eq_true, STy.sameList_refl ps, STy.sameList_refl rs, Bool.and_self]
  | .tuple ts => by simp only [STy.same, STy.sameList_refl ts]
  | .int _ | .bool | .address _ | .fixedBytes _ _ | .fixed _ | .enum _ | .udvt _ | .contract _
  | .bytes _ | .string _ | .struct _ _ | .rational _ | .hexConst _ _ | .stringLit _ => by
    simp only [STy.same, beq_self_eq_true, Bool.and_self]

theorem STy.sameList_refl : (a : List STy) → STy.sameList a a = true
  | [] => rfl
  | x :: xs => by simp only [STy.sameList, STy.same_refl x, STy.sameList_refl xs, Bool.and_self]

end

/-- Decidable equality of types, by `STy.same`. -/
instance : DecidableEq STy := fun a b =>
  if h : STy.same a b = true then isTrue (STy.eq_of_same a b h)
  else isFalse (fun e => h (e ▸ STy.same_refl a))

/-- How an evaluation stops early. -/
inductive Halt where
  /-- A revert with its data (`panicData`, `errorData`, a custom error). -/
  | revert (data : Bytes)
  /-- A run-time type mismatch; a well-formed program never reaches one. -/
  | stuck (why : String)
  /-- The horizon ended before the evaluation did. -/
  | timeout
  deriving DecidableEq, Repr

/-- A pure step's result. -/
abbrev R (α : Type) := Except Halt α

/-- A panic with its code. -/
def panic {α : Type} (c : PanicCode) : R α := .error (.revert (panicData c))

/-- A stuck state. -/
def stuck {α : Type} (why : String) : R α := .error (.stuck why)

mutual

/-- **Run-time values** of expressions of type `τ`. -/
inductive RVal (D : Layout) : STy → Type where
  | val {τ : STy} (v : Val D τ) : RVal D τ
  /-- A constant: its value is its type's rational. -/
  | const (q : Q) : RVal D (.rational q)
  /-- A string literal: its bytes are its type's. -/
  | strLit (bs : List UInt8) : RVal D (.stringLit bs)
  /-- A hexadecimal literal: its value is its type's. -/
  | hex (q : Q) (len : Nat) : RVal D (.hexConst q len)
  | tuple {τs : List STy} (vs : RVals D τs) : RVal D (.tuple τs)

/-- Values of a list of types. -/
inductive RVals (D : Layout) : List STy → Type where
  | nil : RVals D []
  | cons {τ : STy} {τs : List STy} : RVal D τ → RVals D τs → RVals D (τ :: τs)

end

/-- The empty tuple, the value of a statement-like expression. -/
def RVal.unit {D : Layout} : RVal D (.tuple []) := .tuple .nil

/-- The `Val` of a value, or stuck. -/
def RVal.get {D : Layout} {τ : STy} : RVal D τ → R (Val D τ)
  | .val v => pure v
  | _ => stuck "not a plain value"

/-! ## Ranges and wrapping -/

/-- The low and high bound of `bits`-bit integers, signed or not (the bounds
of `IntTy` and of `FixTy`'s scaled values). -/
def bitsLo (s : Bool) (b : Nat) : Int := if s then -((2 ^ (b - 1) : Nat) : Int) else 0
def bitsHi (s : Bool) (b : Nat) : Int :=
  if s then ((2 ^ (b - 1) - 1 : Nat) : Int) else ((2 ^ b - 1 : Nat) : Int)

/-- Two's-complement wrapping into `bits` bits. -/
def wrapBits (s : Bool) (b : Nat) (v : Int) : Int :=
  let m : Int := ((2 ^ b : Nat) : Int)
  let r := v % m
  if s ∧ bitsHi s b < r then r - m else r

theorem two_pow_succ_pred {b : Nat} (hb : 1 ≤ b) : 2 ^ b = 2 * 2 ^ (b - 1) := by
  have e : b = (b - 1) + 1 := by omega
  conv => lhs; rw [e]
  rw [Nat.pow_succ, Nat.mul_comm]

/-- **Wrapping lands in range.** -/
theorem wrapBits_mem (s : Bool) {b : Nat} (hb : 1 ≤ b) (v : Int) :
    bitsLo s b ≤ wrapBits s b v ∧ wrapBits s b v ≤ bitsHi s b := by
  have hm := two_pow_succ_pred hb
  have hp : 1 ≤ 2 ^ (b - 1) := Nat.one_le_two_pow
  have hmpos : (0 : Int) < ((2 ^ b : Nat) : Int) := by omega
  have h0 : 0 ≤ v % ((2 ^ b : Nat) : Int) := Int.emod_nonneg _ (by omega)
  have h1 : v % ((2 ^ b : Nat) : Int) < ((2 ^ b : Nat) : Int) := Int.emod_lt_of_pos _ hmpos
  have hpm : ((2 ^ b : Nat) : Int) = 2 * ((2 ^ (b - 1) : Nat) : Int) := by rw [hm]; push_cast; rfl
  cases s
  · simp only [wrapBits, bitsLo, bitsHi, Bool.false_eq_true, false_and, if_false]
    omega
  · simp only [wrapBits, bitsLo, bitsHi, true_and, if_true]
    have hc : ((2 ^ (b - 1) - 1 : Nat) : Int) = ((2 ^ (b - 1) : Nat) : Int) - 1 := by omega
    rw [hc]
    split <;> omega

theorem IntTy.bits_pos (t : IntTy) : 1 ≤ t.bits := by have := t.valid; omega
theorem FixTy.bits_pos (t : FixTy) : 1 ≤ t.bits := by have := t.valid; omega

/-- Wrapping into an integer type. -/
def IntTy.wrap (t : IntTy) (v : Int) : Int := wrapBits t.signed t.bits v

theorem IntTy.wrap_mem (t : IntTy) (v : Int) : t.lo ≤ t.wrap v ∧ t.wrap v ≤ t.hi :=
  wrapBits_mem t.signed t.bits_pos v

/-- Wrapping a scaled fixed-point value into its type. -/
def FixTy.wrap (t : FixTy) (v : Int) : Int := wrapBits t.signed t.bits v

theorem FixTy.wrap_mem (t : FixTy) (v : Int) : t.lo ≤ t.wrap v ∧ t.wrap v ≤ t.hi :=
  wrapBits_mem t.signed t.bits_pos v

variable {D : Layout}

/-- An integer result: in range as is; out of range a `Panic(0x11)` when
checked, wrapped when not. -/
def intRes (t : IntTy) (checked : Bool) (v : Int) : R (Val D (.int t)) :=
  if h : t.lo ≤ v ∧ v ≤ t.hi then pure (.int v h)
  else if checked then panic .arithmetic else pure (.int (t.wrap v) (t.wrap_mem v))

/-- An integer wrapped (explicit conversions, shifts, bitwise operations). -/
def intWrap (t : IntTy) (v : Int) : Val D (.int t) := .int (t.wrap v) (t.wrap_mem v)

/-- A fixed-point result, as `intRes`. -/
def fixRes (t : FixTy) (checked : Bool) (v : Int) : R (Val D (.fixed t)) :=
  if h : t.lo ≤ v ∧ v ≤ t.hi then pure (.fixed v h)
  else if checked then panic .arithmetic else pure (.fixed (t.wrap v) (t.wrap_mem v))

/-- A fixed-point value wrapped. -/
def fixWrap (t : FixTy) (v : Int) : Val D (.fixed t) := .fixed (t.wrap v) (t.wrap_mem v)

/-- An integer in range, or stuck. -/
def mkInt (t : IntTy) (v : Int) : R (Val D (.int t)) :=
  if h : t.lo ≤ v ∧ v ≤ t.hi then pure (.int v h) else stuck "integer out of range"

/-- A fixed-point value in range, or stuck. -/
def mkFix (t : FixTy) (v : Int) : R (Val D (.fixed t)) :=
  if h : t.lo ≤ v ∧ v ≤ t.hi then pure (.fixed v h) else stuck "fixed point out of range"

/-- `n` bytes, from a list of any length (cut or padded on the right). -/
def fitBytes (n : Nat) (bs : List UInt8) : List UInt8 := (bs ++ List.replicate n 0).take n

theorem fitBytes_length (n : Nat) (bs : List UInt8) : (fitBytes n bs).length = n := by
  simp only [fitBytes, List.length_take, List.length_append, List.length_replicate]
  omega

/-- A `bytesN` value from any bytes (cut or right-padded). -/
def mkBytes {n : Nat} {h : 1 ≤ n ∧ n ≤ 32} (bs : List UInt8) : Val D (.fixedBytes n h) :=
  .fixedBytes (fitBytes n bs) (fitBytes_length n bs)

/-- The bytes of a `bytesN` value as an unsigned big-endian number. -/
def bytesNat (bs : List UInt8) : Nat := beValue bs

/-- `n` big-endian bytes of a number (modulo `256^n`). -/
def natBytes (n v : Nat) : List UInt8 := beBytes n v

/-! ## Integer and fixed-point arithmetic -/

/-- `x ^ k mod 2^bits` without computing `x ^ k` (square and multiply over
the bits of `k`). -/
def powMod (x : Int) (k : Nat) (m : Nat) : Int :=
  go 300 x k 1
where
  go : Nat → Int → Nat → Int → Int
    | 0, _, _, acc => acc
    | f + 1, b, e, acc =>
      if e = 0 then acc
      else go f ((b * b) % m) (e / 2) (if e % 2 = 1 then (acc * b) % m else acc)

/-- `x ^ k` at an integer type: the exact power when it is small enough to
compute, checked or wrapped as `intRes`; a base of absolute value at least 2
with an exponent beyond the width is out of range of every type. -/
def intPow (t : IntTy) (checked : Bool) (x : Int) (k : Nat) : R (Val D (.int t)) :=
  if x = 0 ∨ x = 1 ∨ k ≤ t.bits then intRes t checked (x ^ k)
  else if x = -1 then intRes t checked (if k % 2 = 0 then 1 else -1)
  else if checked then panic .arithmetic
  else pure (intWrap t (powMod x k (2 ^ t.bits)))

/-- An arithmetic or bitwise operation on two integers of type `t`. -/
def intBin (t : IntTy) (checked : Bool) (op : BinOp) (x y : Int) : R (Val D (.int t)) :=
  match op with
  | .add => intRes t checked (x + y)
  | .sub => intRes t checked (x - y)
  | .mul => intRes t checked (x * y)
  | .div => if y = 0 then panic .divZero else intRes t checked (x.tdiv y)
  | .mod => if y = 0 then panic .divZero else intRes t checked (x.tmod y)
  | .bitAnd => pure (intWrap t (Int.bitAnd x y))
  | .bitOr => pure (intWrap t (Int.bitOr x y))
  | .bitXor => pure (intWrap t (Int.bitXor x y))
  | _ => stuck "not an integer operation"

/-- An arithmetic operation on two scaled fixed-point values of type `t`:
`*` and `/` exact, then truncated toward zero (second round). -/
def fixBin (t : FixTy) (checked : Bool) (op : BinOp) (x y : Int) : R (Val D (.fixed t)) :=
  match op with
  | .add => fixRes t checked (x + y)
  | .sub => fixRes t checked (x - y)
  | .mul => fixRes t checked ((x * y).tdiv t.scale)
  | .div => if y = 0 then panic .divZero else fixRes t checked ((x * t.scale).tdiv y)
  | .mod => if y = 0 then panic .divZero else fixRes t checked (x.tmod y)
  | _ => stuck "not a fixed-point operation"

/-- Bytewise operations on `bytesN`. -/
def bytesBin (op : BinOp) (xs ys : List UInt8) : R (List UInt8) :=
  match op with
  | .bitAnd => pure (List.zipWith (· &&& ·) xs ys)
  | .bitOr => pure (List.zipWith (· ||| ·) xs ys)
  | .bitXor => pure (List.zipWith (· ^^^ ·) xs ys)
  | _ => stuck "not a bytes operation"

/-- **A binary operation** at one type (`+ - * / % & | ^`, and `&&`/`||`
on evaluated operands). -/
def binVal (checked : Bool) (op : BinOp) : {τ : STy} → Val D τ → Val D τ → R (Val D τ)
  | .int t, .int x _, .int y _ => intBin t checked op x y
  | .fixed t, .fixed x _, .fixed y _ => fixBin t checked op x y
  | .fixedBytes n h, .fixedBytes xs _, .fixedBytes ys _ => do
    let zs ← bytesBin op xs ys
    pure (mkBytes (n := n) (h := h) zs)
  | .bool, .bool a, .bool b =>
    match op with
    | .and => pure (.bool (a && b))
    | .or => pure (.bool (a || b))
    | _ => stuck "not a boolean operation"
  | _, _, _ => stuck "operands of a binary operation"

/-- The order key of an ordered or comparable value. -/
def Val.key {τ : STy} : Val D τ → Option Int
  | .int v _ | .fixed v _ => some v
  | .bool b => some (if b then 1 else 0)
  | .address a | .contract a => some a.val
  | .fixedBytes bs _ => some (bytesNat bs)
  | .enum i => some i.val
  | .udvt v => v.key
  | .externalFn a sel _ => some (a.val * 2 ^ 32 + bytesNat sel)
  | _ => none

/-- **A comparison** (`< > <= >= == !=`). -/
def cmpVal {τ : STy} (op : BinOp) (a b : Val D τ) : R Bool :=
  match a.key, b.key with
  | some x, some y =>
    match op with
    | .lt => pure (decide (x < y)) | .gt => pure (decide (y < x))
    | .le => pure (decide (x ≤ y)) | .ge => pure (decide (y ≤ x))
    | .eq => pure (decide (x = y)) | .ne => pure (decide (x ≠ y))
    | _ => stuck "not a comparison"
  | _, _ => stuck "values without order"

/-- The comparison of two constants. -/
def cmpConst (op : BinOp) (a b : Q) : R Bool :=
  let x := a.num * b.den
  let y := b.num * a.den
  match op with
  | .lt => pure (decide (x < y)) | .gt => pure (decide (y < x))
  | .le => pure (decide (x ≤ y)) | .ge => pure (decide (y ≤ x))
  | .eq => pure (decide (x = y)) | .ne => pure (decide (x ≠ y))
  | _ => stuck "not a comparison"

/-- A shift amount or exponent: an unsigned integer, or a constant. -/
def RVal.amount {σ : STy} : RVal D σ → R Nat
  | .val (.int v _) => pure v.toNat
  | .const q | .hex q _ => pure q.toInt.toNat
  | _ => stuck "not an amount"

/-- **Shifts and powers**: `<<` wraps, `>>` is arithmetic on signed
integers, `**` checked or wrapped; on `bytesN`, shifts of the bit pattern. -/
def shiftVal (checked : Bool) (op : BinOp) (k : Nat) : {τ : STy} → Val D τ → R (Val D τ)
  | .int t, .int x _ =>
    match op with
    | .shl => pure (intWrap t (if k ≥ t.bits then 0 else x * 2 ^ k))
    | .sar | .shr =>
      if t.signed ∧ op = .sar then
        pure (intWrap t (if k ≥ t.bits then (if x < 0 then -1 else 0) else x / ((2 ^ k : Nat) : Int)))
      else
        let u := (wrapBits false t.bits x).toNat
        pure (intWrap t (if k ≥ t.bits then 0 else ((u / 2 ^ k : Nat) : Int)))
    | .exp => intPow t checked x k
    | _ => stuck "not a shift"
  | .fixedBytes n h, .fixedBytes bs _ =>
    let w := 8 * n
    let u := bytesNat bs
    match op with
    | .shl => pure (mkBytes (n := n) (h := h) (natBytes n (if k ≥ w then 0 else u * 2 ^ k % 2 ^ w)))
    | .shr | .sar => pure (mkBytes (n := n) (h := h) (natBytes n (if k ≥ w then 0 else u / 2 ^ k)))
    | _ => stuck "not a bytes shift"
  | _, _ => stuck "shift operand"

/-- **Unary operators**: `-` (checked; on `ufixed` a panic unless zero),
`!`, `~`. -/
def unaryVal (checked : Bool) (op : PrefixOp) : {τ : STy} → Val D τ → R (Val D τ)
  | .int t, .int x _ =>
    match op with
    | .neg => intRes t checked (-x)
    | .bitNot => pure (intWrap t (Int.bitNot x))
    | _ => stuck "integer unary"
  | .fixed t, .fixed x _ =>
    match op with
    | .neg => fixRes t checked (-x)
    | _ => stuck "fixed unary"
  | .bool, .bool b =>
    match op with
    | .not => pure (.bool !b)
    | _ => stuck "boolean unary"
  | .fixedBytes n h, .fixedBytes bs _ =>
    match op with
    | .bitNot => pure (mkBytes (n := n) (h := h) (bs.map (~~~ ·)))
    | _ => stuck "bytes unary"
  | _, _ => stuck "unary operand"

/-- `x + 1` or `x - 1` at a numeric type (fixed point: the value 1). -/
def incDecVal (checked inc : Bool) : {τ : STy} → Val D τ → R (Val D τ)
  | .int t, .int x _ => intRes t checked (if inc then x + 1 else x - 1)
  | .fixed t, .fixed x _ => fixRes t checked (if inc then x + t.scale else x - t.scale)
  | _, _ => stuck "increment operand"

/-! ## Conversions of values -/

/-- A constant at an integer or fixed-point type (implicit: exact). -/
def constVal (q : Q) : (τ : STy) → R (Val D τ)
  | .int t => if q.isInt then mkInt t q.toInt else stuck "fractional constant at an integer type"
  | .fixed f =>
    match q.toFixed? f with
    | some v => mkFix f v
    | none => stuck "constant not exact at a fixed-point type"
  | .fixedBytes n h => if q.num = 0 then pure (mkBytes (n := n) (h := h) []) else stuck "constant at bytes"
  | _ => stuck "constant at a non-numeric type"

/-- **An implicit conversion of a value-type value** (`STy.implicit`):
integers and addresses by value, a fixed-point value rescaled to more
digits, `bytesN` padded on the right, a contract to its base by address. -/
def convVal : {σ : STy} → (τ : STy) → Val D σ → R (Val D τ)
  | .int _, .int t', .int x _ => mkInt t' x
  | .int _, .fixed f, .int x _ => mkFix f (x * f.scale)
  | .fixed f, .fixed f', .fixed x _ => mkFix f' (x * ((10 ^ (f'.digits - f.digits) : Nat) : Int))
  | .bool, .bool, v => pure v
  | .address _, .address _, .address a => pure (.address a)
  | .fixedBytes _ _, .fixedBytes m h, .fixedBytes bs _ => pure (mkBytes (n := m) (h := h) bs)
  | .enum _, .enum d', .enum i => if h : i.val < D.enumSize d' then pure (.enum ⟨i.val, h⟩) else stuck "enum"
  | .udvt d, .udvt d', v => if h : d = d' then pure (h ▸ v) else stuck "user-defined value type"
  | .contract _, .contract _, .contract a => pure (.contract a)
  | σ, τ, v => if h : σ = τ then pure (h ▸ v) else stuck "implicit conversion of a value"

/-- The value of an enum from an integer: `Panic(0x21)` out of range. -/
def enumOfInt (d : DeclName) (x : Int) : R (Val D (.enum d)) :=
  if h : 0 ≤ x ∧ x.toNat < D.enumSize d then pure (.enum ⟨x.toNat, h.2⟩) else panic .enumConv

/-- **An explicit conversion of a value-type value** (`STy.explicit`): by
bit pattern between integers (wrapping), integers and `bytesN` of one
width, `uint160`, `bytes20` and addresses; `bytesN` cut or padded on the
right; enums from integers with `Panic(0x21)`; fixed point rescaled,
truncated toward zero and wrapped (second round). -/
def convExplicitVal : {σ : STy} → (τ : STy) → Val D σ → R (Val D τ)
  | .int _, .int t', .int x _ => pure (intWrap t' x)
  | .int a, .fixedBytes n h, .int x _ =>
    pure (mkBytes (n := n) (h := h) (natBytes n (wrapBits false a.bits x).toNat))
  | .fixedBytes _ _, .int t, .fixedBytes bs _ => pure (intWrap t (bytesNat bs))
  | .int _, .address _, .int x _ => pure (.address ⟨(wrapBits false 160 x).toNat % 2 ^ 160, Nat.mod_lt _ (by decide)⟩)
  | .address _, .int t, .address a => pure (intWrap t a.val)
  | .fixedBytes _ _, .address _, .fixedBytes bs _ => pure (.address ⟨bytesNat bs % 2 ^ 160, Nat.mod_lt _ (by decide)⟩)
  | .address _, .fixedBytes n h, .address a => pure (mkBytes (n := n) (h := h) (natBytes 20 a.val))
  | .fixedBytes _ _, .fixedBytes m h, .fixedBytes bs _ => pure (mkBytes (n := m) (h := h) bs)
  | .address _, .address _, .address a => pure (.address a)
  | .contract _, .address _, .contract a => pure (.address a)
  | .address _, .contract _, .address a => pure (.contract a)
  | .int _, .enum d, .int x _ => enumOfInt d x
  | .enum _, .int t, .enum i => pure (intWrap t i.val)
  | .fixed f, .fixed f', .fixed x _ =>
    pure (fixWrap f' (if f.digits ≤ f'.digits then x * ((10 ^ (f'.digits - f.digits) : Nat) : Int)
      else x.tdiv ((10 ^ (f.digits - f'.digits) : Nat) : Int)))
  | .fixed f, .int t, .fixed x _ => pure (intWrap t (x.tdiv f.scale))
  | .int _, .fixed f, .int x _ => pure (fixWrap f (x * f.scale))
  | .fixed f, .fixedBytes n h, .fixed x _ =>
    pure (mkBytes (n := n) (h := h) (natBytes n (wrapBits false f.bits x).toNat))
  | .fixedBytes _ _, .fixed f, .fixedBytes bs _ => pure (fixWrap f (bytesNat bs))
  | σ, τ, v => convVal (σ := σ) τ v

/-- An explicit conversion of a constant (`T(c)`). -/
def constExplicit (q : Q) : (τ : STy) → R (Val D τ)
  | .int t =>
    match q.toIntExplicit? t with
    | some v => mkInt t v
    | none => stuck "constant explicit integer"
  | .fixed f =>
    match q.toFixedExplicit? f with
    | some v => mkFix f v
    | none => stuck "constant explicit fixed point"
  | .address _ => pure (.address ⟨q.toInt.toNat % 2 ^ 160, Nat.mod_lt _ (by decide)⟩)
  | .enum d => enumOfInt d q.toInt
  | .fixedBytes n h => pure (mkBytes (n := n) (h := h) (natBytes n q.toInt.toNat))
  | τ => constVal q τ

/-! ## Laws -/

/-- A checked operation out of range panics with `0x11`. -/
theorem intRes_overflow (t : IntTy) (v : Int) (h : ¬ (t.lo ≤ v ∧ v ≤ t.hi)) :
    intRes (D := D) t true v = panic .arithmetic := by
  simp only [intRes, h, dif_neg, not_false_eq_true, if_true]

/-- An unchecked operation wraps. -/
theorem intRes_unchecked (t : IntTy) (v : Int) :
    ∃ h, intRes (D := D) t false v = pure (.int (if t.lo ≤ v ∧ v ≤ t.hi then v else t.wrap v) h) := by
  by_cases hv : t.lo ≤ v ∧ v ≤ t.hi
  · exact ⟨by simp only [hv, and_self, if_true], by simp only [intRes, hv, and_self, dif_pos, if_true]⟩
  · exact ⟨by simp only [hv, if_false]; exact t.wrap_mem v, by
      simp only [intRes, hv, dif_neg, not_false_eq_true, Bool.false_eq_true, if_false]⟩

/-- Division by zero panics with `0x12`, checked or not. -/
theorem intBin_divZero (t : IntTy) (c : Bool) (x : Int) :
    intBin (D := D) t c BinOp.div x 0 = panic .divZero := by
  simp only [intBin, if_true]

end Solidity.Source
