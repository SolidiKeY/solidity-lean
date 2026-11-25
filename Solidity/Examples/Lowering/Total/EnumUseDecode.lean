import Solidity.Correctness.Lowering.Total.EnumUseDecode

/-!
# Checks of the enum-use decoder

`enum State { Open, Locked, Closed } enum Side { Buy, Sell }` in contract `C`:
`State.Locked` and `type(Side).max` read by `enumLit?` and carried by
`decode_use` to Source resolution, conversion target, a typed `State(1)` and
the enum value; local, state, absent-member, absent-enum, empty-table and
memberless failures.
-/
namespace Solidity.Examples.Lowering.Total.EnumUseDecode

open Solidity Solidity.Correctness.Lowering.Total.EnumDecode
open Solidity.Correctness.Lowering.Total.EnumUseDecode

/-- `enum State { Open, Locked, Closed } enum Side { Buy, Sell }`. -/
def two : Contract := { vars := [], enums := [("State", ["Open", "Locked", "Closed"]), ("Side", ["Buy", "Sell"])] }

def twoParts : Source.Syn (.list (.part false)) :=
  .cons (.enum "State" "Open" ["Locked", "Closed"]) (.cons (.enum "Side" "Buy" ["Sell"]) .nil)

/-- The enums decode in order. -/
theorem two_decode : decode two = .ok twoParts := rfl

def cDecl : Source.Decl := ⟨.contract, "C", none, true, .contract false "C" .none .nil twoParts⟩

/-- A body of `contract C { … }` with no local, raw and Source. -/
def ctx : Source.Ctx := { env := ⟨[cDecl] ++ twoParts.collect (some "C") ++ []⟩, scope := some "C", locals := [] }

/-- The alignment holds for every enum name of `C` in a body with no local. -/
theorem aligned (x : Name) (hx : x ≠ "") : Aligned two twoParts [] ctx "C" [cDecl] [] x :=
  ⟨rfl, rfl, by simp [cDecl], by simp, by simp [ctx], by simp [cDecl], by decide, hx⟩

-- `State.Locked`, `State.Closed`, `type(State).min`, `type(State).max`: raw readings.
example : enumLit? two [] (.name "State") "Locked" = some 1 := rfl
example : enumLit? two [] (.name "State") "Closed" = some 2 := rfl
example : enumLit? two [] (.name "State") "type(min)" = some 0 := rfl
example : enumLit? two [] (.name "State") "type(max)" = some 2 := rfl
example : enumLit? two [] (.name "State") "Locked" = rawMember? two "State" "Locked" :=
  enumLit?_member two [] rfl (by decide) (by decide)

/-- `State.Locked` in Source: `State` resolves to its declaration, `State(1)` is
typed at `State`, and `enumOfInt` gives the value of ordinal 1. -/
example : ctx.resolve "State" = some (.decls [enumDecl "C" "State" "Open" ["Locked", "Closed"]]) ∧
    sourceRead ctx.env ⟨some "C", "State"⟩ (.member "Locked") = some 1 ∧
    Nonempty (Source.Typed ctx (ordinalSpell "State" 1) (.enum ⟨some "C", "State"⟩)) ∧
    Source.enumOfInt (D := ctx.env.layout) ⟨some "C", "State"⟩ 1 = pure (.enum ⟨1, by decide⟩) := by
  obtain ⟨⟨f, r, hl, hr⟩, -, hs, ht, _, -, he⟩ :=
    decode_use (m := "Locked") two_decode (aligned "State" (by decide)) rfl
  cases hl
  exact ⟨hr, hs, ht, he⟩

/-- `type(Side).max` in Source: the last member. -/
example : sourceRead ctx.env ⟨some "C", "Side"⟩ .max = some 1 :=
  (decode_use (m := "type(max)") two_decode (aligned "Side" (by decide)) rfl).2.2.1

-- Absent member, absent enum, another enum's member, a non-name base.
example : enumLit? two [] (.name "State") "Pending" = none := rfl
example : sourceRead ctx.env ⟨some "C", "State"⟩ (.member "Pending") = none := rfl
example : enumLit? two [] (.name "Mode") "type(min)" = none := rfl
example : ctx.convTarget "Mode" = none := rfl
example : enumLit? two [] (.name "Side") "Locked" = none := rfl
example : enumLit? two [] (.num 0) "Locked" = none := rfl

-- A local `uint State;` shadows the enum, raw and Source.
example : enumLit? two [(Var.ofName "State", .val .uint)] (.name "State") "Locked" = none :=
  enumLit?_shadowed two _ rfl
example : ({ ctx with locals := [("State", .int .u256)] } : Source.Ctx).convTarget "State" = none :=
  convTarget_local (by simp)

/-- A state variable `bool State;` beside the enum (solc refuses it). -/
def withState : Contract := { two with vars := [("State", .prim .bool)] }

def stateDecl : Source.Decl :=
  ⟨.stateVar, "State", some "C", false, .stateVar (.elem .bool) none none none false "State" .none⟩

example : enumLit? withState [] (.name "State") "Locked" = none := enumLit?_shadowed withState [] rfl
example : ({ ctx with env := ⟨ctx.env.decls ++ [stateDecl]⟩ } : Source.Ctx).convTarget "State" = none := rfl

-- The empty table, and a memberless enum: no bounds raw, no decoding.
example : enumLit? { vars := [], enums := [] } [] (.name "State") "Locked" = none := enumLit?_empty _ [] _ _ rfl
example : enumLit? { vars := [], enums := [("E", [])] } [] (.name "E") "type(max)" = none := rfl
example : decode { vars := [], enums := [("E", [])] } = .error (.emptyEnum 0 "E") := rfl

end Solidity.Examples.Lowering.Total.EnumUseDecode
