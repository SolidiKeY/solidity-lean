import Solidity.Correctness.Lowering.Total.EnumDecode

/-!
# Checks of the enum-declaration decoder

Two enums decoded in order into one contract unit, member lookup computed on
the Source side and transported from the raw table by `sourceMember?_eq`
(present, absent and repeated members, unknown enums, another scope), and a
table with a memberless enum that fails with its position and name.
-/
namespace Solidity.Examples.Lowering.Total.EnumDecode

open Solidity
open Solidity.Correctness.Lowering.Total.EnumDecode

/-- Two enums, the first with three ordered members and a repeated name. -/
def two : Contract :=
  { vars := [], enums := [("State", ["Open", "Locked", "Closed", "Open"]), ("Side", ["Buy", "Sell"])] }

/-- The decoded parts, in declaration and member order. -/
def twoParts : Source.Syn (.list (.part false)) :=
  .cons (.enum "State" "Open" ["Locked", "Closed", "Open"]) (.cons (.enum "Side" "Buy" ["Sell"]) .nil)

theorem two_decode : decode two = .ok twoParts := rfl

/-- The parts placed in contract `C`'s unit. -/
def twoUnit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil twoParts) .nil)

theorem twoUnit_decls :
    twoUnit.env.decls = [⟨.contract, "C", none, true, .contract false "C" .none .nil twoParts⟩] ++
      twoParts.collect (some "C") ++ [] := rfl

example : (twoParts.collect (some "C")).map entryOf = two.enums.map some :=
  decode_collect two_decode "C"

example : (twoParts.collect (some "C")).map (·.name) = ["State", "Side"] := rfl

/-- Lookup transported from the raw table. -/
theorem two_member (n m : Name) :
    sourceMember? twoUnit.env ⟨some "C", n⟩ m = rawMember? two n m :=
  sourceMember?_eq two_decode twoUnit_decls (by simp) (by simp) n m

-- Member indices follow declaration order; a repeated name has its first index.
example : sourceMember? twoUnit.env ⟨some "C", "State"⟩ "Locked" = some 1 := by
  rw [two_member]; rfl
example : sourceMember? twoUnit.env ⟨some "C", "State"⟩ "Closed" = some 2 := by
  rw [two_member]; rfl
example : sourceMember? twoUnit.env ⟨some "C", "State"⟩ "Open" = some 0 := by
  rw [two_member]; rfl
example : sourceMember? twoUnit.env ⟨some "C", "Side"⟩ "Sell" = some 1 := by
  rw [two_member]; rfl
-- The same name in another enum is not a member of this one.
example : sourceMember? twoUnit.env ⟨some "C", "Side"⟩ "Locked" = none := by
  rw [two_member]; rfl
-- Unsuccessful lookup: an unknown enum on both sides.
example : sourceMember? twoUnit.env ⟨some "C", "Mode"⟩ "Open" = none := by
  rw [two_member]; rfl
example : rawMember? two "Mode" "Open" = none := rfl
-- Computed directly on the Source side, without the theorem.
example : sourceMember? twoUnit.env ⟨some "C", "State"⟩ "Closed" = some 2 := rfl
example : sourceMember? twoUnit.env ⟨some "C", "Side"⟩ "Hold" = none := rfl
-- Another scope (here file level) has no such enum.
example : sourceMember? twoUnit.env ⟨none, "State"⟩ "Open" = none := rfl

-- Member counts in the Source layout.
example : twoUnit.env.layout.enumSize ⟨some "C", "State"⟩ = 4 := by
  rw [enumSize_eq two_decode twoUnit_decls (by simp) (by simp)]; rfl
example : twoUnit.env.layout.enumSize ⟨some "C", "Side"⟩ = 2 := rfl
example : twoUnit.env.layout.enumSize ⟨some "C", "Mode"⟩ = 0 := rfl

/-- A memberless enum after a representable one. -/
def withEmpty : Contract :=
  { vars := [], enums := [("Side", ["Buy", "Sell"]), ("Empty", []), ("Late", ["X"])] }

-- It fails at its own position and name; the later entry is not skipped to.
theorem withEmpty_decode : decode withEmpty = .error (.emptyEnum 1 "Empty") := rfl

example : ¬ Representable withEmpty := by decide
example : Representable two := by decide
example : withEmpty.enums[1]? = some ("Empty", []) := decode_error_entry withEmpty_decode
example : ∃ err, decode withEmpty = .error err := (decode_error_iff _).2 (by decide)

-- No enums: an empty prefix.
example : decode { vars := [] } = .ok .nil := rfl

end Solidity.Examples.Lowering.Total.EnumDecode
