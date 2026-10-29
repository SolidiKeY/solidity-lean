import Solidity.Roadmap.Evm
import Solidity.Hashes

/-!
# Bytes, prime fields and elliptic curves for the Osaka precompiles

The arithmetic the computed precompiles of `Solidity/Precompiles/` share,
written as `Solidity/Hashes.lean` and `Solidity/Secp256k1.lean` are: over
`Nat` and `Fin p`, every recursion structural or fuelled by a bit count, so
that `#guard` evaluates each precompile on the EIPs' vectors.

- **Bytes.**  A precompile reads its input as the execution specification's
  `buffer_read` does: zero bytes past the end (`readPad`, `readNat`), and
  writes fixed-width big-endian words (`toBE`).  `words` is the
  `ceil32(len) / 32` of the linear gas formulas.
- **Fields.**  `FieldOps` is the arithmetic a curve formula uses; `Fin p`
  (with Fermat inversion, `p` prime at every use) and `Fp2 p` (`u² = -1`,
  BN254's and BLS12-381's quadratic extension) are its instances.  No field
  law is proved or assumed: the formulas are evaluated, not reasoned about.
- **Curves.**  `Pt` is an affine point or infinity of a short Weierstrass
  curve `y² = x³ + a·x + b` (`Curve`); `add`, `double`, `neg` and `mul` are
  the textbook affine formulas, total on every input.  An *input* point is
  validated when it is decoded (each precompile's `decode*` returns the
  point with its curve equation, or fails), so the precompiles' failure
  cases are the decoding failures (and, for point evaluation, a proof that
  does not verify); results are computed totally.
-/

namespace Solidity.Precompiles

open Solidity.Roadmap.Evm (Bytes)

/-! ## Bytes -/

/-- The 32-byte words an input of `n` bytes occupies, rounded up
(`ceil32(n) // 32`). -/
def words (n : Nat) : Nat := (n + 31) / 32

/-- `len` bytes of `d` from `start`, zero past its end: the execution
specification's `buffer_read`. -/
def readPad (d : Bytes) (start len : Nat) : List Nat :=
  let s := ((d.drop start).take len).map UInt8.toNat
  s ++ List.replicate (len - s.length) 0

/-- Big-endian bytes as a number. -/
def ofBE (bs : List Nat) : Nat := Hashes.ofBytes bs

/-- The big-endian number in `len` bytes of `d` from `start`, zero-padded. -/
def readNat (d : Bytes) (start len : Nat) : Nat := ofBE (readPad d start len)

/-- `n` as exactly `k` big-endian bytes (its low `8·k` bits). -/
def toBE (k n : Nat) : Bytes := (Hashes.beBytes k n).map Nat.toUInt8

/-- The 32-byte word of `n`. -/
def word (n : Nat) : Bytes := toBE 32 n

theorem readPad_length (d : Bytes) (start len : Nat) : (readPad d start len).length = len := by
  simp only [readPad, List.length_append, List.length_map, List.length_take, List.length_drop,
    List.length_replicate]
  omega

theorem toBE_length (k n : Nat) : (toBE k n).length = k := by
  simp only [toBE, Hashes.beBytes, List.length_map, List.length_reverse, List.length_range]

/-- The number of bits of `n` (`0` has none): Python's `int.bit_length`. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- `b ^ e % m` by binary exponentiation over the bits of `e`. -/
def powMod (b e m : Nat) : Nat :=
  go (bitLength e) (b % m) e (1 % m)
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, _, r => r
    | k + 1, b, e, r =>
      if e = 0 then r else go k (b * b % m) (e / 2) (if e % 2 = 1 then r * b % m else r)

#guard powMod 3 200 1000003 == 3 ^ 200 % 1000003
#guard powMod 0 0 7 == 1
#guard powMod 5 3 1 == 0

/-! ## Fields -/

/-- The arithmetic a curve formula uses.  `inv 0` is unspecified (`0` in
the instances); no formula below divides by zero on a valid input. -/
class FieldOps (α : Type) extends Add α, Sub α, Mul α, Neg α, BEq α where
  zero : α
  one : α
  inv : α → α
  ofNat : Nat → α

/-- Integers modulo `p`, inverted by Fermat (`a ^ (p - 2)`): a field at every
prime `p`, which is how every precompile uses it. -/
instance finFieldOps (p : Nat) [NeZero p] : FieldOps (Fin p) where
  zero := Fin.ofNat p 0
  one := Fin.ofNat p 1
  inv a := Fin.ofNat p (powMod a.val (p - 2) p)
  ofNat n := Fin.ofNat p n

/-- The quadratic extension `Fp[u] / (u² + 1)`, BN254's and BLS12-381's
`Fp2`: `re + im·u`. -/
structure Fp2 (p : Nat) where
  re : Fin p
  im : Fin p
  deriving DecidableEq, Repr

namespace Fp2

variable {p : Nat} [NeZero p]

/-- The conjugate `re - im·u`, the Frobenius map of `Fp2`. -/
def conj (a : Fp2 p) : Fp2 p := ⟨a.re, -a.im⟩

/-- `a · c` for `c` in the base field. -/
def scale (c : Fin p) (a : Fp2 p) : Fp2 p := ⟨c * a.re, c * a.im⟩

instance : FieldOps (Fp2 p) where
  add a b := ⟨a.re + b.re, a.im + b.im⟩
  sub a b := ⟨a.re - b.re, a.im - b.im⟩
  mul a b := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
  neg a := ⟨-a.re, -a.im⟩
  zero := ⟨Fin.ofNat p 0, Fin.ofNat p 0⟩
  one := ⟨Fin.ofNat p 1, Fin.ofNat p 0⟩
  inv a :=
    let n : Fin p := FieldOps.inv (a.re * a.re + a.im * a.im)
    ⟨a.re * n, -(a.im * n)⟩
  ofNat n := ⟨Fin.ofNat p n, Fin.ofNat p 0⟩

end Fp2

namespace FieldOps

variable {α : Type} [FieldOps α]

/-- `a ^ e` by square-and-multiply over the bits of `e`. -/
def pow (a : α) (e : Nat) : α :=
  go (bitLength e) a e FieldOps.one
where
  go : Nat → α → Nat → α → α
    | 0, _, _, r => r
    | k + 1, a, e, r => if e = 0 then r else go k (a * a) (e / 2) (if e % 2 = 1 then r * a else r)

end FieldOps

/-! ## Short Weierstrass curves -/

/-- The curve `y² = x³ + a·x + b` over `α`. -/
structure Curve (α : Type) where
  a : α
  b : α

/-- A point of a curve: affine coordinates, or the point at infinity. -/
inductive Pt (α : Type) where
  | inf
  | aff (x y : α)
  deriving DecidableEq, Repr

namespace Curve

variable {α : Type} [FieldOps α]

/-- The curve equation (infinity is on every curve). -/
def onCurve (C : Curve α) : Pt α → Bool
  | .inf => true
  | .aff x y => y * y == x * x * x + C.a * x + C.b

/-- The opposite point. -/
def neg : Pt α → Pt α
  | .inf => .inf
  | .aff x y => .aff x (-y)

/-- The tangent rule: `2·P`. -/
def double (C : Curve α) : Pt α → Pt α
  | .inf => .inf
  | .aff x y =>
    if y == FieldOps.zero then .inf else
      let l := (FieldOps.ofNat 3 * x * x + C.a) * FieldOps.inv (FieldOps.ofNat 2 * y)
      let x₃ := l * l - x - x
      .aff x₃ (l * (x - x₃) - y)

/-- The chord rule: `P + Q`, with the doubling, opposite and infinity
cases. -/
def add (C : Curve α) : Pt α → Pt α → Pt α
  | .inf, q => q
  | p@(.aff _ _), .inf => p
  | .aff x₁ y₁, .aff x₂ y₂ =>
    if x₁ == x₂ then
      if y₁ == y₂ then C.double (.aff x₁ y₁) else .inf
    else
      let l := (y₂ - y₁) * FieldOps.inv (x₂ - x₁)
      let x₃ := l * l - x₁ - x₂
      .aff x₃ (l * (x₁ - x₃) - y₁)

/-- `k·P` by double-and-add over the bits of `k`. -/
def mul (C : Curve α) (k : Nat) (p : Pt α) : Pt α :=
  go (bitLength k) k p .inf
where
  go : Nat → Nat → Pt α → Pt α → Pt α
    | 0, _, _, r => r
    | n + 1, k, p, r =>
      if k = 0 then r else go n (k / 2) (C.double p) (if k % 2 = 1 then C.add r p else r)

end Curve

/-! ## Test vectors -/

/-- The consecutive blocks of `n` elements of `d` (a shorter last block
included). -/
def chunks {α : Type} (n : Nat) (d : List α) : List (List α) :=
  go d.length d
where
  go : Nat → List α → List (List α)
    | 0, _ => []
    | k + 1, d => if d.isEmpty then [] else d.take n :: go k (d.drop n)

/-- A list maps to `none` exactly when some element does. -/
theorem mapM_eq_none_iff {α β : Type} (f : α → Option β) (l : List α) :
    l.mapM f = none ↔ ∃ a ∈ l, f a = none := by
  induction l with
  | nil => simp only [List.mapM_nil, Option.pure_def, reduceCtorEq, List.not_mem_nil, false_and,
      exists_false]
  | cons a l ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, List.mem_cons, exists_eq_or_imp]
    cases h : f a with
    | none => simp only [Option.bind_none, true_or]
    | some b =>
      simp only [Option.bind_some, reduceCtorEq, false_or, ← ih]
      cases l.mapM f <;> simp only [Option.bind_none, Option.bind_some, reduceCtorEq]

/-- The bytes of a hexadecimal string (two digits each, no prefix), for
test vectors. -/
def ofHex (s : String) : Bytes :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
  (chunks 2 s.toList).map fun ds => (ds.foldl (fun n c => 16 * n + digit c) 0).toUInt8

end Solidity.Precompiles
