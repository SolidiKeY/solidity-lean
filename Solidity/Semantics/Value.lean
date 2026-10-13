import Solidity.Semantics

/-!
# Typed primitive values

The operations on a primitive value, by its type (`docs/intrinsic.md`,
Decision 3, M4a): a `bool` a `Bool`, a `uint` or an `int` an integer in its
type's range.  Arithmetic stays on `Int`, so the kernel never unfolds
`Nat.land` on a `uint` (56642ee); the range is a proof beside the number.

`CallValue.ofTyped` packs a typed value with its type, what the tools take
and print, and `CallValue.as?` reads one back where it has the type.
`PrimTy.toWord` is its ABI word and `PrimTy.ofWord?` reads a word at a type:
what a `try` decodes a call's returned data with.  `PrimTy.ofInt?` reads an
integer at a type, range-checked.
-/

namespace Solidity

/-- KeY's ledger: bounded Solidity addresses, unbounded signed net amounts.
A ledger cannot contain a boolean, a negative address or an overflowing address. -/
abbrev Ledger := List (PrimTy.uint.Denote × Int)

namespace Ledger

/-- Numeric observations for the EVM bridge; the stored keys remain typed. -/
def entries (l : Ledger) : List (Int × Int) := l.map fun (a, n) => (a.1, n)

/-- A numeric read at a typed address is its typed read. -/
theorem lookup_entries (a : PrimTy.uint.Denote) (l : Ledger) :
    Semantics.lookupBy a.1 (entries l) = Semantics.lookupBy a l := by
  induction l with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨b, w⟩ := entry
    by_cases h : a = b
    · subst b
      simp only [entries, List.map_cons, Semantics.lookupBy, if_true]
    · have hn : a.1 ≠ b.1 := fun e => h (Subtype.ext e)
      simp only [entries, List.map_cons, Semantics.lookupBy, h, hn, if_false]
      exact ih

/-- Writing a typed address agrees with the numeric EVM observation. -/
theorem entries_setBy (a : PrimTy.uint.Denote) (v : Int) (l : Ledger) :
    entries (Semantics.setBy a v l) = Semantics.setBy a.1 v (entries l) := by
  induction l with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨b, w⟩ := entry
    simp only [entries] at ih
    by_cases h : a = b
    · subst b
      simp only [Semantics.setBy, entries, List.map_cons, if_true]
    · have hn : a.1 ≠ b.1 := fun e => h (Subtype.ext e)
      simp only [Semantics.setBy, h, hn, if_false, entries, List.map_cons, ih]

end Ledger

namespace PrimTy

/-- The default of a type: what `uint x;` binds and `delete` writes. -/
def dflt : (p : PrimTy) → p.Denote
  | .bool => (false : Bool)
  | .uint => (⟨0, rfl⟩ : {n : Int // PrimTy.uint.inRange n = true})
  | .int => (⟨0, rfl⟩ : {n : Int // PrimTy.int.inRange n = true})

/-- An integer at a type, range-checked: `none` outside the range, and at
`bool`. -/
def ofInt? : (p : PrimTy) → Int → Option p.Denote
  | .uint, n =>
    if h : PrimTy.uint.inRange n = true then
      some (⟨n, h⟩ : {n : Int // PrimTy.uint.inRange n = true})
    else none
  | .int, n =>
    if h : PrimTy.int.inRange n = true then
      some (⟨n, h⟩ : {n : Int // PrimTy.int.inRange n = true})
    else none
  | .bool, _ => none

/-- A number's integer; `none` for a `bool`. -/
def num? : {p : PrimTy} → p.Denote → Option Int
  | .bool, _ => none
  | .uint, n => some n.1
  | .int, n => some n.1

/-- A word read at a type, as solc's ABI decoder reads it: a `uint256` is
the word, an `int256` its two's complement, a `bool` `0` or `1` (any other
word reverts the decoding: `none`). -/
def ofWord? : (p : PrimTy) → Semantics.Word → Option p.Denote
  | .bool, w => if w.1 = 0 then some false else if w.1 = 1 then some true else none
  | .uint, w => some w
  | .int, w => ofInt? .int (if w.1 < 2 ^ 255 then w.1 else w.1 - 2 ^ 256)

/-- The ABI word of a typed value: its two's complement for an `int256`. -/
def toWord : {p : PrimTy} → p.Denote → Semantics.Word
  | .bool, b => cond (b : Bool) ⟨1, rfl⟩ ⟨0, rfl⟩
  | .uint, n => n
  | .int, n => if h : 0 ≤ n.1 then ⟨n.1, by
        have hr := n.2
        simp only [PrimTy.inRange, decide_eq_true_eq] at hr ⊢
        omega⟩
      else ⟨n.1 + 2 ^ 256, by
        have hr := n.2
        simp only [PrimTy.inRange, decide_eq_true_eq] at hr ⊢
        omega⟩

/-- A mapping key as the integer it is hashed as.  solc hashes a key padded
to a word (`keccak256(h(k) . p)`), and a `bool` pads to `0` or `1`, so
`mapping(bool => V)` keeps two slots, at the keys `0` and `1`
(`docs/solc-alignment.md`); a number is itself. -/
def key : {p : PrimTy} → p.Denote → Int
  | .bool, b => cond (b : Bool) 1 0
  | .uint, n => n.1
  | .int, n => n.1

/-- A `uint` is not negative. -/
theorem uint_nonneg (i : PrimTy.uint.Denote) : 0 ≤ i.1 := by
  have h := i.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.1

/-- Two keys hash alike only when they are equal. -/
theorem key_inj : {p : PrimTy} → {a b : p.Denote} → key a = key b → a = b
  | .bool, a, b, h => by
    cases ha : (a : Bool) <;> cases hb : (b : Bool) <;>
      simp only [key, ha, hb, cond_true, cond_false] at h <;> first | rfl | (exact absurd h (by decide))
  | .uint, _, _, h => Subtype.ext h
  | .int, _, _, h => Subtype.ext h

end PrimTy

namespace Semantics.CallValue

/-- The value's type. -/
def ty : CallValue → PrimTy
  | .bool _ => .bool
  | .uint _ => .uint
  | .int _ => .int

/-- The value at the type `p`: `none` where it has another type. -/
def as? : (p : PrimTy) → CallValue → Option p.Denote
  | .bool, .bool b => some b
  | .uint, .uint n => some n
  | .int, .int n => some n
  | _, _ => none

theorem as?_ofTyped {p : PrimTy} (v : p.Denote) : as? p (ofTyped v) = some v := by
  cases p <;> rfl

/-- A number's integer; `none` for a `bool`. -/
def num? (v : CallValue) : Option Int := match v with
  | .bool _ => none
  | .uint n => some n.1
  | .int n => some n.1

end Semantics.CallValue


end Solidity
