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

/-- Under v2 a nested bytes literal is spelled by its registered spelling:
`1 + #bytes(1)` is `1 + hex"01"`, not a call of `#bytes`. -/
example (T : Decode.Tables) :
    ExprX T registry1 (.binop .add (.num 1) (.bytesLit [1]))
      (.addSub .add (Decode.num 1) (.lit (.hexStr [1]))) :=
  .binop rfl (.num 1) (.claimed rfl rfl) rfl

/-- The bridges proved so far, and the statements left open until the shared
meaning is bound. -/
example (M : Meaning) :
    Registry.claims [] "f" = false ∧ Registry.Faithful M [] ∧ registry1.WellFormed :=
  ⟨claims_nil _, faithful_nil M, registry1_wellFormed⟩
example (T : Decode.Tables) : Conforms T [] T.expr := conforms_nil T
example (M : Meaning) :
    [conformsX_conforms_statement, exprX_nil_statement, exprX_unclaimed_statement,
    bytesFaithfulStatement M, registry1FaithfulStatement M,
    ∀ T f, ConformsX T registry1 f → Conforms T registry1 f].length = 6 := rfl

end Solidity.Examples.Lowering.Total.CallSpellExt
