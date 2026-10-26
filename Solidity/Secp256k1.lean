import Solidity.RevertBytes

/-!
# Computed secp256k1 recovery

Coordinates and scalars have their respective modular types. Jacobian points
carry the curve equation; smart construction checks it after each operation.
The scalar walk and modular exponentiation inspect at most 256 bits. Recovery
uses Ethereum's two parity choices (`v = 27/28`, `x = r`), accepts high `s`,
and returns none for invalid inputs or infinity. No signer-authority,
collision-freedom, primality or group-law axiom is introduced. The algorithms
are executable definitions; conformance vectors do not constitute a general
proof of equivalence to a particular external precompile implementation.
-/
namespace Solidity.Secp256k1

def prime : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
def order : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
instance : NeZero prime := ⟨by decide⟩
instance : NeZero order := ⟨by decide⟩
abbrev Fp := Fin prime
abbrev Scalar := Fin order

/-- Exponentiation modulo `m`, over exactly the representable exponent bits. -/
def pow256 {m : Nat} [NeZero m] (a : Fin m) (e : Fin (2 ^ 256)) : Fin m :=
  let rec go : Nat → Fin m → Nat → Fin m → Fin m
    | 0, _, _, r => r
    | k + 1, a, e, r =>
      if e == 0 then r else go k (a * a) (e / 2) (if e % 2 == 1 then r * a else r)
  go 256 a e.val 1

/-- A Jacobian point. Every zero Z denotes infinity. -/
structure Point where
  x : Fp
  y : Fp
  z : Fp
  onCurve : z = 0 ∨ y * y = x * x * x + 7 * z ^ 6
  deriving DecidableEq

def infinity : Point := ⟨0, 1, 0, Or.inl rfl⟩

/-- No unchecked coordinate triple enters the point type. -/
def checked (x y z : Fp) : Option Point :=
  if _hz : z = 0 then some infinity
  else if hc : y * y = x * x * x + 7 * z ^ 6 then some ⟨x, y, z, Or.inr hc⟩
  else none

/-- The standard generator, at affine Z = 1. -/
def generator : Point :=
  ⟨⟨0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, by decide⟩,
   ⟨0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8, by decide⟩,
   1, Or.inr (by decide)⟩

/-- Jacobian doubling for the curve with a = 0. -/
def double (p : Point) : Option Point := do
  if p.z == 0 || p.y == 0 then return infinity
  let a : Fp := p.x * p.x
  let b : Fp := p.y * p.y
  let c : Fp := b * b
  let d : Fp := 2 * ((p.x + b) * (p.x + b) - a - c)
  let e : Fp := 3 * a
  let f : Fp := e * e
  let x : Fp := f - 2 * d
  checked x (e * (d - x) - 8 * c) (2 * p.y * p.z)

/-- Jacobian addition, including equal points, opposites and infinity. -/
def add (p q : Point) : Option Point := do
  if p.z == 0 then return q
  if q.z == 0 then return p
  let z1 : Fp := p.z * p.z
  let z2 : Fp := q.z * q.z
  let u1 : Fp := p.x * z2
  let u2 : Fp := q.x * z1
  let s1 : Fp := p.y * q.z * z2
  let s2 : Fp := q.y * p.z * z1
  if u1 == u2 then
    if s1 == s2 then double p else return infinity
  else
    let h : Fp := u2 - u1
    let i : Fp := (2 * h) * (2 * h)
    let j : Fp := h * i
    let r : Fp := 2 * (s2 - s1)
    let v : Fp := u1 * i
    let x : Fp := r * r - j - 2 * v
    checked x (r * (v - x) - 2 * s1 * j)
      (((p.z + q.z) * (p.z + q.z) - z1 - z2) * h)

/-- A bounded binary scalar walk. Every intermediate result is checked. -/
def scale (k : Scalar) (p : Point) : Option Point :=
  let rec go : Nat → Nat → Point → Point → Option Point
    | 0, _, _, r => some r
    | n + 1, k, p, r => do
      if k == 0 then return r
      let r ← if k % 2 == 1 then add r p else pure r
      let p ← double p
      go n (k / 2) p r
  go 256 k.val p infinity

/-- Recover the public curve point before hashing its affine coordinates.
The Nat boundary admits malformed ABI inputs so they can be rejected here;
validated coordinates and group scalars immediately enter bounded types. -/
def recoverPoint (h v r s : Nat) : Option Point := do
  if !((v == 27 || v == 28) && 0 < r && r < order && 0 < s && s < order) then failure
  let x : Fp := Fin.ofNat prime r
  let yy : Fp := x * x * x + 7
  let y0 : Fp := pow256 yy ⟨(prime + 1) / 4, by decide⟩
  if y0 * y0 != yy then failure
  let y : Fp := if y0.val % 2 == v - 27 then y0 else -y0
  let R ← checked x y 1
  let ri : Scalar := pow256 (Fin.ofNat order r) ⟨order - 2, by decide⟩
  let u1 : Scalar := -(Fin.ofNat order h) * ri
  let u2 : Scalar := Fin.ofNat order s * ri
  let a ← scale u1 generator
  let b ← scale u2 R
  let q ← add a b
  if q.z == 0 then none else some q

/-- Low 160 bits of Keccak of the uncompressed public key without its tag. -/
def address (q : Point) : Fin (2 ^ 160) :=
  let zi : Fp := pow256 q.z ⟨prime - 2, by decide⟩
  let x : Fp := q.x * zi * zi
  let y : Fp := q.y * zi * zi * zi
  let bytes := Semantics.wordBytes x.val ++ Semantics.wordBytes y.val
  ⟨Keccak.keccak256Nat (bytes.map UInt8.toNat) % 2 ^ 160, Nat.mod_lt _ (by decide)⟩

/-- Ethereum's recovery result, with failure represented explicitly. -/
def recover (h v r s : Nat) : Option (Fin (2 ^ 160)) :=
  (recoverPoint h v r s).map address

end Solidity.Secp256k1
