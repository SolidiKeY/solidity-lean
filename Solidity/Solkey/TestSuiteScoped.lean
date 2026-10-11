import Solidity.Solkey.TestSuite

/-!
# `TestSuite.sol`'s programs, scoped

The TestSuite import's programs are scoped, `Solkey.TestSuite.f : Prog
Solkey.TestSuite Γ Γ'` (`docs/intrinsic.md`, M2, W8), each read in its
parameters' context and checked by the kernel at the import;
`solc_scoped` (`Frontend/Import.lean`) checks that every row it elaborated
is one.
-/

/-- info: 449 programs declared scoped -/
#guard_msgs in solc_scoped Solkey.TestSuite
