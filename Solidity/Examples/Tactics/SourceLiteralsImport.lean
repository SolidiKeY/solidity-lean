import Solidity.Frontend.Testing
import Solidity.Calculus.Close
import Solidity.Calculus.Closers

/-! Source-validated literal regressions, including a rejecting assertion. -/
solc_import "../../../tests/solc/SourceLiterals.ast.json" hash 0x148b0e297850462c
  as Imported.SourceLiterals testing


namespace Solidity.Examples.Tactics.SourceLiteralsImport

/-- Packed source address literals occupy twenty bytes; nested address
literals retain their type through inline-array inference. -/
theorem address_context_initial :
    (Prog.run (State.init Imported.SourceLiterals)
      Imported.SourceLiterals.addressContext).isOk = true := by
  decide +kernel


/-- Exact rational, signed, byte, bound and extreme constants execute as
the pinned compilers do; the deliberately false assertion panics. -/
theorem literal_execution :
    (Prog.run (State.init Imported.SourceLiterals) Imported.SourceLiterals.rationalRemainders).isOk = true ∧
    (Prog.run (State.init Imported.SourceLiterals) Imported.SourceLiterals.signedConstants).isOk = true ∧
    (Prog.run (State.init Imported.SourceLiterals) Imported.SourceLiterals.computedBounds).isOk = true ∧
    (Prog.run (State.init Imported.SourceLiterals) Imported.SourceLiterals.byteSequences).isOk = true ∧
    (Prog.run (State.init Imported.SourceLiterals) Imported.SourceLiterals.extremeConstants).isOk = true ∧
    (Prog.run (State.init Imported.SourceLiterals) Imported.SourceLiterals.degeneratePowers).isOk = true ∧
    (Prog.run (State.init Imported.SourceLiterals) Imported.SourceLiterals.falseRemainder).isOk = false := by
  decide +kernel


open scoped Scoped
local instance : InContract := ⟨Imported.SourceLiterals⟩

/-- The source remainder assertion is valid from every admitted typed state. -/
theorem rational_remainder_valid : ⊨ᶠ spec!{rationalRemainders} := by
  sol_symex
  sol_decide


/-- The false source assertion is not a valid box obligation. -/
theorem false_remainder_invalid : ¬ (⊨ᶠ spec!{falseRemainder}) :=
  fun h => Modality.afterRunTR_not_panic
    ((h (State.init _)) rfl) (by decide +kernel)

end Solidity.Examples.Tactics.SourceLiteralsImport

