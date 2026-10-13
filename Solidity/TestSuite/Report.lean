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
`testArrayCopyClearsOldElements` (a write through an alias a `pop` made
dangle, read again after a copy) and `storagePushReadBack` (the slot at
`(len + 1) - 1` after a push) are derived since W10.4, in `Derived13.lean`
and `Derived7.lean`.
-/

/--
info: 452 functions: 437 derived, 0 pending, 15 other
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
-/
#guard_msgs in
#solkey_obligations Solkey.TestSuite
