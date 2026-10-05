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

/-!
# What is derived of solkey's `TestSuite`

Every function, by what `#solkey_obligations` (`Frontend/Problems.lean`)
finds: derived when its theorem `N.f.proved` exists, states
`⊢ N.f.problem` and uses no axiom but Lean's three (so no `sorry` and no
`native_decide`: one that does is listed "unsound"), pending when only its
statement does, and the import's verdict for the three with no statement.
A pending obligation is no theorem and no `sorry`: but for the one below,
each writes through an alias bound through an index after a `pop` made it
dangle (`SymB.stale`): one reads the slot again after a copy whose
reduction is past `Derive.elimSize`, the other pushes through the alias,
which the elimination keeps whole; they are listed with their reasons in
`docs/testsuite-proofs.md`.
`storagePushReadBack` is not valid in the model (the length delta,
`docs/solc-alignment.md`): `tests/solkey/expected.tsv` lists it
`divergent`, so the tables count one pending fewer.
-/

/--
info: 420 functions: 414 derived, 3 pending, 3 other
excluded recursiveStructMapping
skipped tryCalleeGet
skipped tryCalleePing
pending:
storagePushReadBack testArrayCopyClearsOldElements testDanglingInnerArrayReappearsAfterPush
-/
#guard_msgs in
#solkey_obligations Solkey.TestSuite
