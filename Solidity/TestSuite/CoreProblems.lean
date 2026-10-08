import Solidity.TestSuite.Problems
import Solidity.Calculus.Core.Derive

/-!
# solkey's `TestSuite` obligations, scoped

`Problems.lean`'s obligations stated over the scoped calculus,
`Solkey.TestSuite.f.problem.core : Core.Fml Solkey.TestSuite []`
(`solc_scoped_problems`, `Frontend/Problems.lean`), for the `Core*` twins
of the `Derived` modules (`docs/intrinsic.md`, W2 `symex`, the early gate).
Each is checked to erase to its statement in `Problems.lean`.  They are
the entries of one table, `Solkey.TestSuite.problems.core`, which the kernel
checks once, and are declared, not compiled (`decl`): compiling 437
obligations in one command takes more than the default heartbeats, and the
scoped `sol_prove` reads an obligation by its value
(`Core.Symex.evaluable`).  At the flip this file
becomes `solc_scoped_problems Solkey.TestSuite main decl`, declaring
`Solkey.TestSuite.f.problem`, while `Problems.lean` keeps
`solc_problems Solkey.TestSuite legacy` (the `TestSuite/Problems` timing
gate), and the `Derived` modules import this file (`docs/intrinsic.md`,
W3 lane `testsuite`).
-/

/-- info: 437 obligations declared scoped -/
#guard_msgs in solc_scoped_problems Solkey.TestSuite decl
