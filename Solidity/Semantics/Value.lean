import Solidity.Semantics

/-!
# Typed primitive values

What a value of a primitive type is, by its type (`docs/intrinsic.md`,
Decision 3, M4a): a `bool` a `Bool`, a `uint` or an `int` an integer in its
type's range.  Arithmetic stays on `Int`, so the kernel never unfolds
`Nat.land` on a `uint` (56642ee); the range is a proof beside the number.

`PrimTy.erase` is its ABI word (`Semantics.Value`): what a call's
arguments and returned data are made of and what the tools print, and
`PrimTy.ofValue?` reads one back, where the word has the type: what a `try`
decodes and what the tools take as arguments.
-/

namespace Solidity

/-- The values of the primitive type `p`. -/
def PrimTy.Denote : PrimTy → Type
  | .bool => Bool
  | .uint => {n : Int // PrimTy.uint.inRange n = true}
  | .int => {n : Int // PrimTy.int.inRange n = true}

namespace PrimTy

instance decEqDenote : (p : PrimTy) → DecidableEq p.Denote
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .uint => inferInstanceAs (DecidableEq {n : Int // PrimTy.uint.inRange n = true})
  | .int => inferInstanceAs (DecidableEq {n : Int // PrimTy.int.inRange n = true})

instance reprDenote : (p : PrimTy) → Repr p.Denote
  | .bool => inferInstanceAs (Repr Bool)
  | .uint => ⟨fun n _ => repr n.1⟩
  | .int => ⟨fun n _ => repr n.1⟩

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
