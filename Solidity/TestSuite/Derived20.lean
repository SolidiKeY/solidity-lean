import Solidity.TestSuite.ScopedProblems
import Solidity.Calculus.Closers

/-! Obligations whose leaves each close but together pass one declaration's
heartbeats (`docs/solkey-migration.md`): declared by `sol_auto_theorem`
(`Calculus/Closers.lean`), the walk and each leaf with heartbeats of their
own. -/

open Solidity
open scoped Scoped

sol_auto_theorem Solkey.TestSuite.bitAndSymbolic.proved : ⊢ Solkey.TestSuite.bitAndSymbolic.problem

sol_auto_theorem Solkey.TestSuite.invariantForBreakSkipsUpdate.proved : ⊢ Solkey.TestSuite.invariantForBreakSkipsUpdate.problem

sol_auto_theorem Solkey.TestSuite.invariantQuantifiedOverPrefix.proved : ⊢ Solkey.TestSuite.invariantQuantifiedOverPrefix.problem
