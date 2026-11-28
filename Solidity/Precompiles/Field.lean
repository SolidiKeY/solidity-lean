import Solidity.Roadmap.Evm
import Solidity.Hashes

namespace Solidity.Precompiles

open Solidity.Roadmap.Evm (Bytes)

def words (n : Nat) : Nat := (n + 31) / 32

def readPad (d : Bytes) (start len : Nat) : List Nat :=
  let s := ((d.drop start).take len).map UInt8.toNat
  s ++ List.replicate (len - s.length) 0

def ofBE (bs : List Nat) : Nat := Hashes.ofBytes bs

def readNat (d : Bytes) (start len : Nat) : Nat := ofBE (readPad d start len)

def toBE (k n : Nat) : Bytes := (Hashes.beBytes k n).map Nat.toUInt8

def word (n : Nat) : Bytes := toBE 32 n

theorem readPad_length (d : Bytes) (start len : Nat) : (readPad d start len).length = len := by
  simp only [readPad, List.length_append, List.length_map, List.length_take, List.length_drop,
    List.length_replicate]
  omega

theorem toBE_length (k n : Nat) : (toBE k n).length = k := by
  simp only [toBE, Hashes.beBytes, List.length_map, List.length_reverse, List.length_range]

def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

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

class FieldOps (α : Type) extends Add α, Sub α, Mul α, Neg α, BEq α where
  zero : α
  one : α
  inv : α → α
  ofNat : Nat → α

instance finFieldOps (p : Nat) [NeZero p] : FieldOps (Fin p) where
  zero := Fin.ofNat p 0
  one := Fin.ofNat p 1
  inv a := Fin.ofNat p (powMod a.val (p - 2) p)
  ofNat n := Fin.ofNat p n

structure Fp2 (p : Nat) where
  re : Fin p
  im : Fin p
  deriving DecidableEq, Repr

namespace Fp2

variable {p : Nat} [NeZero p]

def conj (a : Fp2 p) : Fp2 p := ⟨a.re, -a.im⟩

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

def pow (a : α) (e : Nat) : α :=
  go (bitLength e) a e FieldOps.one
where
  go : Nat → α → Nat → α → α
    | 0, _, _, r => r
    | k + 1, a, e, r => if e = 0 then r else go k (a * a) (e / 2) (if e % 2 = 1 then r * a else r)

end FieldOps

structure Curve (α : Type) where
  a : α
  b : α

inductive Pt (α : Type) where
  | inf
  | aff (x y : α)
  deriving DecidableEq, Repr

namespace Curve

variable {α : Type} [FieldOps α]

def onCurve (C : Curve α) : Pt α → Bool
  | .inf => true
  | .aff x y => y * y == x * x * x + C.a * x + C.b

example (C : Curve α) : C.onCurve .inf = true := rfl

def neg : Pt α → Pt α
  | .inf => .inf
  | .aff x y => .aff x (-y)

def double (C : Curve α) : Pt α → Pt α
  | .inf => .inf
  | .aff x y =>
    if y == FieldOps.zero then .inf else
      let l := (FieldOps.ofNat 3 * x * x + C.a) * FieldOps.inv (FieldOps.ofNat 2 * y)
      let x₃ := l * l - x - x
      .aff x₃ (l * (x - x₃) - y)

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

def mul (C : Curve α) (k : Nat) (p : Pt α) : Pt α :=
  go (bitLength k) k p .inf
where
  go : Nat → Nat → Pt α → Pt α → Pt α
    | 0, _, _, r => r
    | n + 1, k, p, r =>
      if k = 0 then r else go n (k / 2) (C.double p) (if k % 2 = 1 then C.add r p else r)

end Curve

def chunks {α : Type} (n : Nat) (d : List α) : List (List α) :=
  go d.length d
where
  go : Nat → List α → List (List α)
    | 0, _ => []
    | k + 1, d => if d.isEmpty then [] else d.take n :: go k (d.drop n)

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

structure HexInput where
  text : String
  evenLength : text.length % 2 = 0
  digits : ∀ c ∈ text.toList,
    c.isDigit = true ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

def ofHex (s : String) : Bytes :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
  (chunks 2 s.toList).map fun ds => (ds.foldl (fun n c => 16 * n + digit c) 0).toUInt8

end Solidity.Precompiles
