import Solidity.Correctness.Lowering.Total.CallSpellExt

/-! Checks of the call-spelling extension contract: what the first registry
claims and how its one spelling reads arguments. No faithfulness is checked
here; it is a statement under review. -/
namespace Solidity.Examples.Lowering.Total.CallSpellExt

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.CallSpellExt

/-- The first registry claims the bytes-literal name and no user function. -/
example : registry1.claims bytesLitName = true := rfl
example : registry1.claims "f" = false := rfl

/-- Numeral arguments are folded and spelled as one `hex"…"` literal. -/
example : bytesSpelling.spell [.num 222, .num 173] = some (.lit (.hexStr [222, 173])) := rfl
example : bytesSpelling.spell [.num 0, .num 256] = some (.lit (.hexStr [1, 0])) := rfl

/-- A non-numeral argument is a gap, not a guess. -/
example : bytesSpelling.spell [.bool true] = none := rfl

/-- A user call is unclaimed; a nested bytes literal is claimed. -/
example : registry1.Unclaimed (.call "f" [.num 1]) := by
  simp [Registry.Unclaimed, RawExpr.any, Registry.claims, Registry.lookup, registry1,
    bytesSpelling, bytesLitName]
example : ¬ registry1.Unclaimed (.binop .add (.num 1) (.bytesLit [1])) := by
  simp [Registry.Unclaimed, RawExpr.any, RawExpr.bytesLit, Registry.claims, Registry.lookup,
    registry1, bytesSpelling]

end Solidity.Examples.Lowering.Total.CallSpellExt
