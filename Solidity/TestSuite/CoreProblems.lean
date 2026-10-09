import Solidity.TestSuite.Problems
import Solidity.Calculus.Core.Surface

/-!
# solkey's `TestSuite` obligations, scoped

`Problems.lean`'s obligations stated over the scoped calculus,
`Solkey.TestSuite.f.problem : Core.Fml Solkey.TestSuite []`
(`solc_scoped_problems … main`, `Frontend/Problems.lean`), each checked to
erase to its legacy statement `Solkey.TestSuite.f.problem.legacy` in
`Problems.lean`.  They are the entries of one table,
`Solkey.TestSuite.problems`, which the kernel checks once, and are declared,
not compiled (`decl`): compiling 437 obligations in one command takes more
than the default heartbeats, and the scoped `sol_prove` reads an obligation
by its value (`Core.Symex.evaluable`).  The `Derived` modules state
`⊢ Solkey.TestSuite.f.problem` under `open scoped Solidity.Core.Scoped`,
the scoped sequent (`Calculus/Core/ProvesDerive.lean`).  A module of its
own: in `Problems.lean` the scoped table would put that module past its
timing gate (`docs/intrinsic.md`, W3b lane `testsuite`).
-/

/-- info: 437 obligations declared scoped -/
#guard_msgs in solc_scoped_problems Solkey.TestSuite main decl
