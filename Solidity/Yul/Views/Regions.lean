import Solidity.Yul.Views.Bytes
import Solidity.Yul.Views.Packing

/-!
# Typed region and residual reconstruction

A reusable preparation law. `owner_at` is a real layout/separation obligation,
not a hash axiom. The caller supplies codecs for the actual source types.
No source heap/store representation changes here. In particular `Storage.cell`
tracks `none` versus an explicit default; physical bits cannot recover that
administrative distinction, so whole-storage identity is not asserted.
-/
namespace Solidity.Yul.Views

/-- An intrinsically typed source cell's exact byte codec. -/
structure ByteCodec (D : Source.Layout) (τ : Source.STy) (n : Nat) where
  encode : Source.Val D τ → Fin n → UInt8
  decode : (Fin n → UInt8) → Option (Source.Val D τ)
  decode_encode : ∀ v, decode (encode v) = some v

/-- The inverse region map certifies that logical regions do not overlap. -/
structure Regions (P : Type) where
  width : P → Nat
  address : (p : P) → Fin (width p) → Nat
  owner : Nat → Option (Sigma fun p => Fin (width p))
  owner_at : ∀ p i, owner (address p i) = some ⟨p, i⟩
  address_owner : ∀ a p i, owner a = some ⟨p, i⟩ → address p i = a

/-- Residual bytes have no logical owner, by construction. -/
abbrev Regions.Residual {P : Type} (r : Regions P) :=
  {a : Nat // r.owner a = none} → UInt8

def Regions.encode {P : Type} (r : Regions P) {D : Source.Layout} {τ : P → Source.STy}
    (c : (p : P) → ByteCodec D (τ p) (r.width p))
    (v : (p : P) → Source.Val D (τ p)) (res : r.Residual) : ByteView :=
  fun a => if h : (r.owner a).isNone = true then res ⟨a, Option.eq_none_of_isNone h⟩
    else match r.owner a with
      | none => 0
      | some ⟨p, i⟩ => (c p).encode (v p) i

theorem Regions.encode_at {P : Type} (r : Regions P) {D : Source.Layout} {τ : P → Source.STy}
    (c : (p : P) → ByteCodec D (τ p) (r.width p))
    (v : (p : P) → Source.Val D (τ p)) (res : r.Residual) (p : P) (i : Fin (r.width p)) :
    r.encode c v res (r.address p i) = (c p).encode (v p) i := by
  simp only [Regions.encode, r.owner_at, Option.isNone_some, Bool.false_eq_true, ↓reduceDIte]

/-- Decode-after-encode for actual typed source values, at every region. -/
theorem Regions.decode_encode {P : Type} (r : Regions P) {D : Source.Layout} {τ : P → Source.STy}
    (c : (p : P) → ByteCodec D (τ p) (r.width p))
    (v : (p : P) → Source.Val D (τ p)) (res : r.Residual) (p : P) :
    (c p).decode (fun i => r.encode c v res (r.address p i)) = some (v p) := by
  simp only [Regions.encode_at, ByteCodec.decode_encode]

/-- Residual extraction is exact, including all bytes outside logical regions. -/
theorem Regions.encode_residual {P : Type} (r : Regions P) {D : Source.Layout} {τ : P → Source.STy}
    (c : (p : P) → ByteCodec D (τ p) (r.width p))
    (v : (p : P) → Source.Val D (τ p)) (res : r.Residual) (a : {a // r.owner a = none}) :
    r.encode c v res a.val = res a := by
  simp only [Regions.encode, a.property, Option.isNone_none, ↓reduceDIte]

/-- Exact physical unchanged-view writeback, with its necessary canonical-codec
 premise exposed. Arbitrary invalid enum/bool bit patterns do not satisfy it. -/
theorem Regions.unchanged {P : Type} (r : Regions P) {D : Source.Layout} {τ : P → Source.STy}
    (c : (p : P) → ByteCodec D (τ p) (r.width p)) (m : ByteView)
    (v : (p : P) → Source.Val D (τ p))
    (canonical : ∀ p i, (c p).encode (v p) i = m (r.address p i)) :
    r.encode c v (fun a => m a.val) = m := by
  funext a
  cases h : r.owner a with
  | none => simp only [Regions.encode, h, Option.isNone_none, ↓reduceDIte]
  | some x =>
    rcases x with ⟨p, i⟩
    simp only [Regions.encode, h, Option.isNone_some, Bool.false_eq_true, ↓reduceDIte]
    rw [canonical, r.address_owner a p i h]

/-- Non-overlap follows from the inverse map; it is not inferred from hashing. -/
theorem Regions.disjoint {P : Type} (r : Regions P) {p q : P}
    {i : Fin (r.width p)} {j : Fin (r.width q)} (h : r.address p i = r.address q j) :
    (⟨p, i⟩ : Sigma fun p => Fin (r.width p)) = ⟨q, j⟩ := by
  have e := r.owner_at p i
  rw [h, r.owner_at q j] at e
  exact (Option.some.inj e).symm

end Solidity.Yul.Views
