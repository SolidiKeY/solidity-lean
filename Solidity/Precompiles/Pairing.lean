import Solidity.Precompiles.Field

namespace Solidity.Precompiles

structure Fp12 (p : Nat) where
  c : Vector (Fin p) 12
  deriving DecidableEq

namespace Fp12

variable {p : Nat} [NeZero p]

def ofFn (v : Fin 12 → Fin p) : Fp12 p := ⟨Vector.ofFn v⟩

def const (a : Fin p) : Fp12 p := ofFn fun i => if i.val = 0 then a else 0

def one : Fp12 p := const 1

def lift (a b : Fin p) : Fp12 p := ofFn fun i => if i.val = 0 then a else if i.val = 6 then b else 0

def monomial (k : Nat) : Fp12 p := ofFn fun i => if i.val = k then 1 else 0

example (k : Fin 12) :
    (monomial (p := p) k.val).c[k.val] = (1 : Fin p) := by
  simp [monomial, ofFn]

def add (a b : Fp12 p) : Fp12 p := ofFn fun i => a.c[i] + b.c[i]

def sub (a b : Fp12 p) : Fp12 p := ofFn fun i => a.c[i] - b.c[i]

def mul (k₆ k₀ : Nat) (a b : Fp12 p) : Fp12 p :=
  let raw : Array Nat := (List.range 23).toArray.map fun j =>
    (List.finRange 12).foldl (fun s (i : Fin 12) =>
      if h : i.val ≤ j ∧ j - i.val < 12 then s + a.c[i].val * b.c[j - i.val].val else s) 0
  let red := (List.range 11).foldl (fun (r : Array Nat) t =>
      let j := 22 - t
      let x := r.getD j 0 % p
      (r.modify (j - 6) (· + k₆ * x)).modify (j - 12) (· + k₀ * x)) raw
  ofFn fun i => Fin.ofNat p (red.getD i.val 0)

def pow (k₆ k₀ : Nat) (a : Fp12 p) (e : Nat) : Fp12 p :=
  go (bitLength e) a e one
where
  go : Nat → Fp12 p → Nat → Fp12 p → Fp12 p
    | 0, _, _, r => r
    | n + 1, a, e, r =>
      if e = 0 then r else go n (mul k₆ k₀ a a) (e / 2) (if e % 2 = 1 then mul k₆ k₀ r a else r)

end Fp12

structure PairingCurve (p : Nat) where

  order : Nat
  g1 : Curve (Fin p)
  g2 : Curve (Fp2 p)

  k₆ : Nat
  k₀ : Nat

  ξ : Nat

  t₁ : Fp12 p
  t₂ : Fp12 p
  t₃ : Fp12 p

  loop : Nat

  frob : Option (Fp2 p × Fp2 p)

namespace PairingCurve

variable {p : Nat} [NeZero p] (E : PairingCurve p)

def mul (a b : Fp12 p) : Fp12 p := Fp12.mul E.k₆ E.k₀ a b

def emb (a : Fp2 p) : Fp12 p := Fp12.lift (a.re - Fin.ofNat p E.ξ * a.im) a.im

def line (R₁ R₂ : Pt (Fp2 p)) (xp yp : Fin p) : Fp12 p :=
  match R₁, R₂ with
  | .aff x₁ y₁, .aff x₂ y₂ =>
    let slope : Option (Fp2 p) :=
      if x₁ == x₂ then
        if y₁ == y₂ then
          some (FieldOps.ofNat 3 * x₁ * x₁ * FieldOps.inv (FieldOps.ofNat 2 * y₁))
        else none
      else some ((y₂ - y₁) * FieldOps.inv (x₂ - x₁))
    match slope with
    | some l =>
      Fp12.sub (Fp12.add (E.mul (E.emb (Fp2.scale xp l)) E.t₁) (E.mul (E.emb (y₁ - l * x₁)) E.t₃))
        (Fp12.const yp)
    | none => Fp12.sub (Fp12.const xp) (E.mul (E.emb x₁) E.t₂)
  | _, _ => Fp12.one

def frobPt (γ : Fp2 p × Fp2 p) : Pt (Fp2 p) → Pt (Fp2 p)
  | .inf => .inf
  | .aff x y => .aff (Fp2.conj x * γ.1) (Fp2.conj y * γ.2)

def miller (Q : Pt (Fp2 p)) (P : Pt (Fin p)) : Fp12 p :=
  match P with
  | .inf => Fp12.one
  | .aff xp yp =>
    match Q with
    | .inf => Fp12.one
    | .aff _ _ =>
      let step (s : Fp12 p × Pt (Fp2 p)) (i : Nat) : Fp12 p × Pt (Fp2 p) :=
        let f := E.mul (E.mul s.1 s.1) (E.line s.2 s.2 xp yp)
        let R := E.g2.double s.2
        if E.loop / 2 ^ i % 2 = 1 then (E.mul f (E.line R Q xp yp), E.g2.add R Q) else (f, R)
      let (f, R) := (List.range (bitLength E.loop - 1)).reverse.foldl step (Fp12.one, Q)
      match E.frob with
      | none => f
      | some γ =>
        let Q₁ := frobPt γ Q
        let nQ₂ := Curve.neg (frobPt γ Q₁)
        let f := E.mul f (E.line R Q₁ xp yp)
        E.mul f (E.line (E.g2.add R Q₁) nQ₂ xp yp)

example (Q : Pt (Fp2 p)) : E.miller Q (.inf : Pt (Fin p)) = Fp12.one := rfl

example (P : Pt (Fin p)) : E.miller (.inf : Pt (Fp2 p)) P = Fp12.one := by
  cases P <;> rfl

def finalExp (f : Fp12 p) : Fp12 p := Fp12.pow E.k₆ E.k₀ f ((p ^ 12 - 1) / E.order)

def check (pairs : List (Pt (Fin p) × Pt (Fp2 p))) : Bool :=
  E.finalExp (pairs.foldl (fun acc pq => E.mul acc (E.miller pq.2 pq.1)) Fp12.one) == Fp12.one

end PairingCurve

end Solidity.Precompiles
