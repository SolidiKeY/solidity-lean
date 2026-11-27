import Solidity.TestSuite.ScopedProblems
import Solidity.Calculus.Closers


open Solidity
open scoped Scoped

sol_auto_theorem Solkey.TestSuite.bitAndSymbolic.proved : ⊢ Solkey.TestSuite.bitAndSymbolic.problem

sol_auto_theorem Solkey.TestSuite.invariantForBreakSkipsUpdate.proved : ⊢ Solkey.TestSuite.invariantForBreakSkipsUpdate.problem

sol_auto_theorem Solkey.TestSuite.invariantQuantifiedOverPrefix.proved : ⊢ Solkey.TestSuite.invariantQuantifiedOverPrefix.problem
