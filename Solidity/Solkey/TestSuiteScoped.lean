import Solidity.Solkey.TestSuite

/-!
# `TestSuite.sol`'s programs, scoped

The lint of the scoped syntax (`docs/intrinsic.md`, M2) over the TestSuite
import: each of its programs resolved from its parameters, quoted and
declared `Solkey.TestSuite.f.core : Prog Solkey.TestSuite Γ Γ'`, the
kernel checking it (`solc_scoped`, `Frontend/Import.lean`).  A module of its
own: the kernel's check costs about a third of the import's, which
`Solkey/TestSuite.lean` keeps.
-/

/-- info: 449 programs declared scoped -/
#guard_msgs in solc_scoped Solkey.TestSuite
