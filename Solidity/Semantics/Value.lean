import Solidity.Semantics

/-!
# Typed primitive values

The operations on a primitive value, by its type (`docs/intrinsic.md`,
Decision 3, M4a): a `bool` a `Bool`, a `uint` or an `int` an integer in its
type's range.  Arithmetic stays on `Int`, so the kernel never unfolds
`Nat.land` on a `uint` (56642ee); the range is a proof beside the number.

`PrimTy.erase` is its ABI word (`Semantics.Value`): what a call's
returned wire data is made of and what the tools print, and
`PrimTy.ofValue?` reads one back, where the word has the type: what a `try`
decodes and what the tools take as arguments.
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

/-- The untyped value of a typed one. -/
def erase : {p : PrimTy} → p.Denote → Semantics.Value
  | .bool, b => .bool b
  | .uint, n => .int n.1
  | .int, n => .int n.1

/-- The default of a type: what `uint x;` binds and `delete` writes. -/
def dflt : (p : PrimTy) → p.Denote
  | .bool => (false : Bool)
  | .uint => (⟨0, rfl⟩ : {n : Int // PrimTy.uint.inRange n = true})
  | .int => (⟨0, rfl⟩ : {n : Int // PrimTy.int.inRange n = true})

/-- An untyped value read at a type: `none` where it is not one. -/
def ofValue? : (p : PrimTy) → Semantics.Value → Option p.Denote
  | .bool, .bool b => some b
  | .uint, .int n =>
    if h : PrimTy.uint.inRange n = true then
      some (⟨n, h⟩ : {n : Int // PrimTy.uint.inRange n = true})
    else none
  | .int, .int n =>
    if h : PrimTy.int.inRange n = true then
      some (⟨n, h⟩ : {n : Int // PrimTy.int.inRange n = true})
    else none
  | .bool, .int _ | .uint, .bool _ | .int, .bool _ => none

/-- A mapping key as the integer it is hashed as.  solc hashes a key padded
to a word (`keccak256(h(k) . p)`), and a `bool` pads to `0` or `1`, so
`mapping(bool => V)` keeps two slots, at the keys `0` and `1`
(`docs/solc-alignment.md`); a number is itself. -/
def key : {p : PrimTy} → p.Denote → Int
  | .bool, b => cond (b : Bool) 1 0
  | .uint, n => n.1
  | .int, n => n.1

end PrimTy


end Solidity
