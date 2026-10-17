import Solidity.TestSuite.Problems
import Solidity.Calculus.Surface

/-!
# solkey's `TestSuite` obligations, declared

`Problems.lean`'s obligations, `Solkey.TestSuite.f.problem : Fml
Solkey.TestSuite []` (`solc_scoped_problems`, `Frontend/Problems.lean`),
each written on its scoped program `Solkey.TestSuite.f`.  They are the
entries of one table,
`Solkey.TestSuite.problems`, which the kernel checks once, and are declared,
not compiled (`decl`): compiling the obligations in one command takes more
than the default heartbeats, and the scoped `sol_prove` reads an obligation
by its value (`Symex.evaluable`).  The `Derived` modules state
`⊢ Solkey.TestSuite.f.problem` under `open scoped Solidity.Scoped`,
the scoped sequent (`Calculus/ProvesDerive.lean`).  A module of its
own: in `Problems.lean` the scoped table would put that module past its
timing gate (`docs/intrinsic.md`, W3b lane `testsuite`).
-/

/-- info: 534 obligations declared scoped -/
#guard_msgs in solc_scoped_problems Solkey.TestSuite decl
