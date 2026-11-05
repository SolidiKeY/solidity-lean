import Solidity.Frontend.StatementGrammarH28.Shape

/-! Kernel controls for the intrinsic root observation, not parser tests. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

example (r : Root) : ∃ s : Syn (.stmt ⟨true, false⟩), HasRoot s r := by
  apply root_inhabited
  cases r <;> trivial

example (r : Root) : ∃ s : Syn (.stmt ⟨true, true⟩), HasRoot s r := by
  apply root_inhabited
  cases r <;> trivial

example : ¬ ∃ s : Syn (.stmt .body), HasRoot s .breakLoop := by
  intro h
  have bad : false = true := (root_inhabited_iff .body .breakLoop).mp h
  cases bad

example : ¬ ∃ s : Syn (.stmt ⟨false, true⟩), HasRoot s .continueLoop := by
  intro h
  have bad : false = true := (root_inhabited_iff ⟨false, true⟩ .continueLoop).mp h
  cases bad

example {k : SCtx} (b : Syn (.block k)) (s : Syn .simple) :
    Syn.blockStmt b ≠ Syn.simpleStmt s := root_discriminate (by change Root.block ≠ Root.simple; decide)

end Solidity.Frontend.StatementGrammarH28
