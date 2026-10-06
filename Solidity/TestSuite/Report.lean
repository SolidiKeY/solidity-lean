import Solidity.TestSuite.Derived1
import Solidity.TestSuite.Derived2
import Solidity.TestSuite.Derived3
import Solidity.TestSuite.Derived4
import Solidity.TestSuite.Derived5
import Solidity.TestSuite.Derived6
import Solidity.TestSuite.Derived7
import Solidity.TestSuite.Derived8
import Solidity.TestSuite.Derived9
import Solidity.TestSuite.Derived10
import Solidity.TestSuite.Derived11
import Solidity.TestSuite.Derived12
import Solidity.TestSuite.Derived13
import Solidity.TestSuite.Derived14

/-!
# What is derived of solkey's `TestSuite`

Every function, by what `#solkey_obligations` (`Frontend/Problems.lean`)
finds: derived when its theorem `N.f.proved` exists, states
`⊢ N.f.problem` and uses no axiom but Lean's three (so no `sorry` and no
`native_decide`: one that does is listed "unsound"), pending when only its
statement does, and the import's verdict for the fifteen with no statement
(solkey states an obligation only for a public or external function, and
inlines an `internal` one at its calls).  A pending obligation is no theorem
and no `sorry`.  solkey `1b4341a303`'s twenty new functions (`send`,
internal calls, `return`, tuples) are derived in `Derived14.lean`.
`testArrayCopyClearsOldElements` writes through an alias bound through an
index after a `pop` made it dangle (`SymB.stale`) and reads the slot again after a copy: its leaf's
reduction is past `Derive.elimSize`, and the `push()` takes its slot from a
storage with writes at another root below it, which the slot facts do not
read.  It is listed with its reasons in `docs/testsuite-proofs.md`.
`storagePushReadBack` is not valid in the model (the length delta,
`docs/solc-alignment.md`): `tests/solkey/expected.tsv` lists it
`divergent`, so the tables count one pending fewer.
-/

/--
info: 452 functions: 435 derived, 2 pending, 15 other
excluded recursiveStructMapping
skipped tryCalleeGet
skipped tryCalleePing
internal returnOne
internal returnSign
internal returnOrdered
internal returnSwapped
internal returnStats
internal returnFromNestedBlock
internal returnOrFallThrough
internal returnAddOne
internal returnAddTwo
internal returnRevertsOnZero
internal returnInsideTry
internal returnVoidEarly
pending:
storagePushReadBack testArrayCopyClearsOldElements
-/
#guard_msgs in
#solkey_obligations Solkey.TestSuite
