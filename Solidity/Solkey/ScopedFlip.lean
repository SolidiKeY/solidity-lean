import Solidity.Frontend.Problems
import Solidity.Calculus.NFmlClose
import Solidity.Calculus.Surface

/-!
# The scoped flip's switches, on one box function

`tests/solc/ScopedFlip.sol` holds one box function, so each switch of the
flip (`docs/intrinsic.md`, W3b lane `testsuite`) runs on every build:
`solc_problems … legacy` (the legacy statement, not compiled, read through
`legacyStatement`), `solc_scoped_problems … main decl` (the table
`N.problems`, each `N.f.problem` its entry), `#solkey_problem` on the
legacy statement, `#solkey_derive?` on the scoped `⊢ N.f.problem`
(`scopedSearch`), and `#solkey_obligations` counting the scoped theorem.
`scripts/solc-ast.mjs --source tests/solc/ScopedFlip.sol --out
tests/solc/ScopedFlip.ast.json --wrapper Solidity/Solkey/ScopedFlip.lean`
rewrites the fixture and its hash.
-/

open Solidity NFml.Proves
open scoped Scoped

solc_import "../../tests/solc/ScopedFlip.ast.json" hash 0x7c6221bb7e6edb3f as Solkey.ScopedFlip

-- the legacy statement, `N.f.problem.legacy`, declared and not compiled
#guard_msgs in
solc_problems Solkey.ScopedFlip legacy

/-- info: 1 obligation declared scoped -/
#guard_msgs in
solc_scoped_problems Solkey.ScopedFlip main decl

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
  sol_prove

additionStorageWrite: derived
-/
#guard_msgs in
#solkey_derive? Solkey.ScopedFlip only additionStorageWrite

theorem Solkey.ScopedFlip.additionStorageWrite.proved : ⊢ Solkey.ScopedFlip.additionStorageWrite.problem := by
  sol_prove

/--
info: 1 functions: 1 derived, 0 pending, 0 other

pending:
-/
#guard_msgs in
#solkey_obligations Solkey.ScopedFlip
