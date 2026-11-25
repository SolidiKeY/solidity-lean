import Solidity.Correctness.Lowering.Total.EnumUseDecode

/-!
# Checks of the enum-use decoder

Two enums decoded into contract `C`'s unit; `E.m`, `type(E).min` and
`type(E).max` read by `enumLit?` and transported by `decode_use` to Source
name resolution, S01's conversion target, a typed `E(i)` and the enum value.
Failures: a local or state-variable shadow (raw and Source), an absent member,
an absent enum, an empty table, and a memberless enum (no minimum or maximum,
and no decoding).
-/
namespace Solidity.Examples.Lowering.Total.EnumUseDecode

open Solidity
open Solidity.Correctness.Lowering.Total.EnumDecode
open Solidity.Correctness.Lowering.Total.EnumUseDecode
open Solidity.Semantics (lookupBy)

/-- Two enums: `State` with three ordered members, `Side` with two. -/
def two : Contract :=
  { vars := [], enums := [("State", ["Open", "Locked", "Closed"]), ("Side", ["Buy", "Sell"])] }

/-- The decoded parts. -/
def twoParts : Source.Syn (.list (.part false)) :=
  .cons (.enum "State" "Open" ["Locked", "Closed"]) (.cons (.enum "Side" "Buy" ["Sell"]) .nil)

theorem two_decode : decode two = .ok twoParts := rfl

/-- The contract declaration of `C`, before its parts. -/
def cDecl : Source.Decl := ⟨.contract, "C", none, true, .contract false "C" .none .nil twoParts⟩

/-- The Source context: a body of `C`, with no local. -/
def ctx : Source.Ctx := { env := ⟨[cDecl] ++ twoParts.collect (some "C") ++ []⟩, scope := some "C", locals := [] }

/-- The raw context: no local. -/
def raw : NCtx := []

theorem aligned (x : Name) (hx : x ≠ "") : Aligned two twoParts raw ctx "C" [cDecl] [] x where
  scope := rfl
  decls := rfl
  pre_nonEnum := by simp [cDecl]
  post_nonEnum := by simp
  locals := by simp [ctx]
  state := by simp [cDecl]
  distinct := by decide
  nonempty := hx

/-! ## Successful reads -/

-- The raw readings: member positions, the first and the last position.
example : Form.raw "State" (.member "Locked") = .field (.name "State") "Locked" := rfl
example : enumLit? two raw (.name "State") "Locked" = some 1 := rfl
example : enumLit? two raw (.name "State") "Closed" = some 2 := rfl
example : enumLit? two raw (.name "State") "type(min)" = some 0 := rfl
example : enumLit? two raw (.name "State") "type(max)" = some 2 := rfl
example : enumLit? two raw (.name "Side") "type(max)" = some 1 := rfl

-- The same through the general theorems.
example : enumLit? two raw (.name "State") "Locked" = rawMember? two "State" "Locked" :=
  enumLit?_member two raw rfl (by decide) (by decide)
example : enumLit? two raw (.name "State") "type(max)" = some 2 :=
  enumLit?_max two raw (ms := ["Open", "Locked", "Closed"]) rfl rfl (by simp)

/-- `State.Locked` in Source: resolution, conversion target, reading, typing
and value, all from `decode_use`. -/
theorem locked :
    (∃ f r, lookupBy "State" two.enums = some (f :: r) ∧
      ctx.resolve "State" = some (.decls [enumDecl "C" "State" f r])) ∧
    ctx.convTarget "State" = some (.enum ⟨some "C", "State"⟩) ∧
    sourceRead ctx.env ⟨some "C", "State"⟩ (Form.ofField "Locked") = some 1 ∧
    Nonempty (Source.Typed ctx (ordinalSpell "State" 1) (.enum ⟨some "C", "State"⟩)) ∧
    ∃ hi : 1 < ctx.env.layout.enumSize ⟨some "C", "State"⟩,
      (Source.Val.enum ⟨1, hi⟩ : Source.Val ctx.env.layout (.enum ⟨some "C", "State"⟩)).key = some 1 ∧
      Source.enumOfInt (D := ctx.env.layout) ⟨some "C", "State"⟩ 1 = pure (.enum ⟨1, hi⟩) :=
  decode_use two_decode (aligned "State" (by decide)) rfl

example : ctx.resolve "State" = some (.decls [enumDecl "C" "State" "Open" ["Locked", "Closed"]]) := by
  obtain ⟨⟨f, r, hl, hr⟩, -⟩ := locked
  cases hl
  exact hr

example : ctx.convTarget "State" = some (.enum ⟨some "C", "State"⟩) := locked.2.1

example : sourceRead ctx.env ⟨some "C", "State"⟩ (.member "Locked") = some 1 := locked.2.2.1

/-- The typed Source conversion `State(1)`. -/
def lockedTyped : Source.Typed ctx (ordinalSpell "State" 1) (.enum ⟨some "C", "State"⟩) :=
  typedOrdinal locked.2.1 1

-- The ordinal is below the Source member count, and the value carries it.
example : ctx.env.layout.enumSize ⟨some "C", "State"⟩ = 3 := rfl
example : Source.enumOfInt (D := ctx.env.layout) ⟨some "C", "State"⟩ 1 = pure (.enum ⟨1, by decide⟩) := by
  obtain ⟨-, -, -, -, hi, -, h⟩ := locked
  exact h

-- `type(Side).max` in Source: the last member.
example : sourceRead ctx.env ⟨some "C", "Side"⟩ .max = some 1 :=
  (decode_use (m := "type(max)") two_decode (aligned "Side" (by decide)) rfl).2.2.1

-- The Source readings computed directly, and the minimum's existence.
example : sourceRead ctx.env ⟨some "C", "State"⟩ .min = some 0 := rfl
example : (sourceRead ctx.env ⟨some "C", "Side"⟩ .min).isSome = true := by
  rw [(sourceRead_min_isSome two_decode (E := ctx.env) rfl (by simp [cDecl]) (by simp) "Side").1]; rfl

/-! ## Failures -/

-- Absent member and absent enum: nothing on either side.
example : enumLit? two raw (.name "State") "Pending" = none := rfl
example : sourceRead ctx.env ⟨some "C", "State"⟩ (.member "Pending") = none := rfl
example : enumLit? two raw (.name "Mode") "type(min)" = none := enumLit?_absent two raw rfl
example : sourceRead ctx.env ⟨some "C", "Mode"⟩ .min = none := rfl
example : ctx.convTarget "Mode" = none := rfl

-- A member of one enum is not a member of another.
example : enumLit? two raw (.name "Side") "Locked" = none := rfl

-- A non-name base reads nothing.
example : enumLit? two raw (.num 0) "Locked" = none := rfl

/-- A raw local named `State`. -/
def shadowRaw : NCtx := [(Var.ofName "State", .val .uint)]

example : enumLit? two shadowRaw (.name "State") "Locked" = none :=
  enumLit?_shadow_local two shadowRaw (t := .val .uint) rfl

/-- The Source local named `State`. -/
def shadowCtx : Source.Ctx := { ctx with locals := [("State", .int .u256)] }

example : shadowCtx.convTarget "State" = none := convTarget_local (by simp [shadowCtx])

/-- A state variable named `State` beside the enum (solc refuses it). -/
def withState : Contract := { two with vars := [("State", .prim .uint)] }

example : enumLit? withState raw (.name "State") "Locked" = none :=
  enumLit?_shadow_state withState raw (T := .prim .uint) rfl

/-- Its Source declaration, after the enums. -/
def stateDecl : Source.Decl :=
  ⟨.stateVar, "State", some "C", false, .stateVar (.elem .bool) none none none false "State" .none⟩

/-- The context with the state variable. -/
def stateCtx : Source.Ctx := { ctx with env := ⟨[cDecl] ++ twoParts.collect (some "C") ++ [stateDecl]⟩ }

theorem stateAligned : Aligned withState twoParts raw stateCtx "C" [cDecl] [stateDecl] "State" where
  scope := rfl
  decls := rfl
  pre_nonEnum := by simp [cDecl]
  post_nonEnum := by simp [stateDecl]
  locals := by simp [stateCtx, ctx]
  state := fun _ _ _ _ => rfl
  distinct := by decide
  nonempty := by decide

example : stateCtx.convTarget "State" = none :=
  convTarget_shadow (ms := ["Open", "Locked", "Closed"]) (rfl : decode withState = .ok twoParts)
    stateAligned (by simp [stateCtx, ctx]) rfl (d := stateDecl) (by simp) rfl rfl

/-- The empty enum table. -/
def empty : Contract := { vars := [], enums := [] }

example : enumLit? empty raw (.name "State") "Locked" = none := enumLit?_empty empty raw _ _ rfl
example : enumLit? empty raw (.name "State") "type(min)" = none := rfl
example : decode empty = .ok .nil := rfl
example : sourceRead ⟨[]⟩ ⟨some "C", "State"⟩ .min = none := rfl

/-- A memberless enum: no minimum or maximum raw, and no Source decoding. -/
def memberless : Contract := { vars := [], enums := [("E", [])] }

example : enumLit? memberless raw (.name "E") "type(min)" = none := rfl
example : enumLit? memberless raw (.name "E") "type(max)" = none := rfl
example : decode memberless = .error (.emptyEnum 0 "E") := rfl

/-! ## The member and bound spellings are not typed by S01 -/

example (τ : Source.STy) : Source.Typed ctx (Form.spell "State" (.member "Locked")) τ → False :=
  spell_member_untyped (d := enumDecl "C" "State" "Open" ["Locked", "Closed"]) rfl rfl

example (τ : Source.STy) : Source.Typed ctx (Form.spell "State" .min) τ → False :=
  spell_bound_untyped (.inl rfl)

end Solidity.Examples.Lowering.Total.EnumUseDecode
