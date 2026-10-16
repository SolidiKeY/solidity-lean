import Solidity.Frontend.Problems
import Solidity.Calculus.Close
import Solidity.Calculus.Surface

/-!
# The scoped flip's switches, on one box function

`tests/solc/ScopedFlip.sol` holds one box function, so each command the
TestSuite's obligations go through (`docs/intrinsic.md`, W3b lane
`testsuite`, W8) runs on every build: `solc_scoped_problems … decl` (the
table `N.problems`, each `N.f.problem` its entry), `#solkey_problem` on
the statement, `#solkey_derive?` on `⊢ N.f.problem` (`scopedSearch`), and
`#solkey_obligations` counting the theorem.
`scripts/solc-ast.mjs --source tests/solc/ScopedFlip.sol --out
tests/solc/ScopedFlip.ast.json --wrapper Solidity/Solkey/ScopedFlip.lean`
rewrites the fixture and its hash.
-/

open Solidity
open scoped Scoped

solc_import "../../tests/solc/ScopedFlip.ast.json" hash 0x7c6221bb7e6edb3f as Solkey.ScopedFlip

/-- info: 1 obligation declared scoped -/
#guard_msgs in
solc_scoped_problems Solkey.ScopedFlip decl

-- `N.f.problem` is the scoped statement, an entry of `N.problems`
example : Solkey.ScopedFlip.additionStorageWrite.problem =
    Solkey.ScopedFlip.problems.getD 0 (Fml.tt (C := Solkey.ScopedFlip)) := rfl

/--
info: \programVariables {
    int x;
    int y;
}

\problem {
    wt(storage) -> \[{ additionStorageWrite(x, y)@ScopedFlip; }\](true)
}
-/
#guard_msgs in
#solkey_problem Solkey.ScopedFlip.additionStorageWrite

/--
info: theorem Solkey.ScopedFlip.additionStorageWrite.proved : ⊢ Solkey.ScopedFlip.additionStorageWrite.problem := by
  sol_prove (steps := 128)

additionStorageWrite: derived
-/
#guard_msgs in
#solkey_derive? Solkey.ScopedFlip only additionStorageWrite

theorem Solkey.ScopedFlip.additionStorageWrite.proved : ⊢ Solkey.ScopedFlip.additionStorageWrite.problem := by
  sol_prove (steps := 128)

/--
info: 1 functions: 1 derived, 0 pending, 0 other

pending:
-/
#guard_msgs in
#solkey_obligations Solkey.ScopedFlip
