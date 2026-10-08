import Solidity.TestSuite.Problems
import Solidity.Calculus.Core.Derive

/-!
# solkey's `TestSuite` obligations, scoped

`Problems.lean`'s obligations stated over the scoped calculus,
`Solkey.TestSuite.f.problem.core : Core.Fml Solkey.TestSuite []`
(`solc_scoped_problems`, `Frontend/Problems.lean`), for the `Core*` twins
of the `Derived` modules (`docs/intrinsic.md`, W2 `symex`, the early gate).
Each is checked to erase to its statement in `Problems.lean`.  They are
declared, not compiled (`decl`): compiling 437 obligations in one command
takes more than the default heartbeats, and the scoped `sol_prove` reads an
obligation by its value (`Core.Symex.evaluable`).  W3 `testsuite` moves
them into `Problems.lean` as `Solkey.TestSuite.f.problem` (`main`), the
legacy ones renamed `.problem.legacy`, once the flip can take every
`Derived` module (`docs/intrinsic.md`, W3 lane `testsuite`).
-/

/-- info: 437 obligations declared scoped, 437 erasing to their legacy statement -/
#guard_msgs in solc_scoped_problems Solkey.TestSuite decl
