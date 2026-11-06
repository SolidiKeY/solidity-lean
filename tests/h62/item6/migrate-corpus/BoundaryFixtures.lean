import Solidity.Corpus.Basic

/-! Migration fixtures for the existing run/diamond boundary.
These finite examples do not extend the quantified claims of the corpus.
Normal termination must be accepted; require failure and assertion panic must
remain distinct and must both be rejected by `runOk`.
-/
namespace Solidity.Corpus.MigrationFixtures
open Semantics

example : Diamond (State.init TestSuite)
    sol[TestSuite]{ require(true); assert(true); } := by
  corpus_decide

example : runOk (State.init TestSuite)
    sol[TestSuite]{ require(false); } = false := by
  decide +kernel

example : outcome (State.init TestSuite)
    sol[TestSuite]{ require(false); } = "revert" := by
  decide +kernel

example : runOk (State.init TestSuite)
    sol[TestSuite]{ assert(false); } = false := by
  decide +kernel

example : outcome (State.init TestSuite)
    sol[TestSuite]{ assert(false); } = "panic" := by
  decide +kernel

end Solidity.Corpus.MigrationFixtures
