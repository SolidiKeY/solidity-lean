import Solidity.Semantics

/-!
# Typed primitive values

What a value of a primitive type is, by its type (`docs/intrinsic.md`,
Decision 3, M4a): a `bool` a `Bool`, a `uint` or an `int` an integer in its
type's range.  Arithmetic stays on `Int`, so the kernel never unfolds
`Nat.land` on a `uint` (56642ee); the range is a proof beside the number.

`PrimTy.erase` is the value the untyped interpreter holds for it
(`Semantics.Value`), and `PrimTy.ofValue?` reads one back, where the untyped
value has the type.  Until the typed interpreter replaces `Stmt.run` (M4),
these are the bridge.
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

theorem erase_dflt : (p : PrimTy) → erase (dflt p) = PrimTy.default p
  | .bool | .uint | .int => rfl

theorem ofValue?_erase : {p : PrimTy} → (v : p.Denote) → ofValue? p (erase v) = some v
  | .bool, _ => rfl
  | .uint, ⟨_, h⟩ => dif_pos h
  | .int, ⟨_, h⟩ => dif_pos h

theorem erase_of_ofValue? : {p : PrimTy} → {w : Semantics.Value} → {v : p.Denote} →
    ofValue? p w = some v → erase v = w
  | .bool, .bool _, _, h => by cases h; rfl
  | .uint, .int n, v, h => by
    simp only [ofValue?] at h
    split at h
    · cases h; rfl
    · cases h
  | .int, .int n, v, h => by
    simp only [ofValue?] at h
    split at h
    · cases h; rfl
    · cases h
  | .bool, .int _, _, h | .uint, .bool _, _, h | .int, .bool _, _, h => nomatch h

theorem erase_injective {p : PrimTy} {v w : p.Denote} (h : erase v = erase w) : v = w := by
  have := ofValue?_erase v
  rw [h, ofValue?_erase w] at this
  exact (Option.some.inj this).symm

/-- A numeric value is the integer it holds: `Value.asInt` never fails on one. -/
theorem asInt_erase_uint (v : PrimTy.uint.Denote) : Semantics.Value.asInt (erase v) = .ok v.1 := rfl

theorem asInt_erase_int (v : PrimTy.int.Denote) : Semantics.Value.asInt (erase v) = .ok v.1 := rfl

/-- A `bool` is the Boolean it holds: `Value.asBool` never fails on one. -/
theorem asBool_erase (v : PrimTy.bool.Denote) : Semantics.Value.asBool (erase v) = .ok v := rfl

end PrimTy

namespace Core

/-- An `Option` as a run's result: `none` is a revert, the one way a typed
operation fails.  A typed operation's agreement with its untyped namesake
reads `untyped (erase x) = toRes erase (typed x)`, so the untyped one is
never stuck there. -/
def toRes {α β : Type} (f : α → β) : Option α → Semantics.Res β
  | some a => .ok (f a)
  | none => .error .revert

end Core

end Solidity
