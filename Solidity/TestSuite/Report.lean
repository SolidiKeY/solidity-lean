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
import Solidity.TestSuite.Derived15
import Solidity.TestSuite.Derived16
import Solidity.TestSuite.Derived17
import Solidity.TestSuite.Derived18
import Solidity.TestSuite.Derived19
import Solidity.TestSuite.Derived20
import Solidity.TestSuite.Derived21
import Solidity.TestSuite.Refuted

/-!
# What is derived of solkey's `TestSuite`

Every function, by what `#solkey_obligations` (`Frontend/Problems.lean`)
finds: derived when its theorem `N.f.proved` exists, states
`⊢ N.f.problem` and uses no axiom but Lean's three (so no `sorry` and no
`native_decide`: one that does is listed "unsound"), pending when only its
statement does, and the import's verdict for a function with no statement
(solkey states an obligation only for a public or external function, and
inlines an `internal` one at its calls).  A pending obligation is no theorem
and no `sorry`. The fixture pins solkey `473da8944c`. `Derived15.lean`
adds the migration's newly provable obligations; `Derived14.lean` retains
the earlier send, internal-call, return and tuple derivations.
`testArrayCopyClearsOldElements` (a write through an alias a `pop` made
dangle, read again after a copy) and `storagePushReadBack` (the slot at
`(len + 1) - 1` after a push) are derived since W10.4, in `Derived13.lean`
and `Derived7.lean`.  Since solkey `d85018517f` an empty push saves only the
length and exposes the slot as it is: the seven obligations that read an
appended reference slot as its default (solkey's `SYMBOLIC_TAIL_OPENS`)
are false in the model (a dirty slot past an array's end, which `wt`
admits), and are refuted with the `unprovable*` ones
(`Solidity/TestSuite/Refuted.lean`, listed "refuted"), and so is
`invariantClosedFormSum`, from an array of `2^255` elements
(`docs/automation.md`, M6).
-/

/--
info: 617 functions: 552 derived, 0 pending, 65 other
internal valuesRef
internal valuesRefWithEffect
internal matrixRefWithEffect
internal basketRefWithEffect
excluded recursiveStructMapping
internal mutateStorageCopySource
skipped tryCalleeGet
skipped tryCalleePing
internal returnOne
internal returnSign
internal returnOrdered
internal returnSwapped
internal returnStats
internal bitAndSetTotal
internal retConditionalTwo
internal conditionalSetOne
internal conditionalSetTwo
internal returnFromNestedBlock
internal returnOrFallThrough
internal returnAddOne
internal returnAddTwo
internal returnRevertsOnZero
internal returnInsideTry
internal returnVoidEarly
internal returnDefaults
internal returnDefaultAddress
internal returnDefaultEnum
internal returnDefaultMemoryArray
internal returnInThenBranch
internal returnInElseBranch
internal returnEnumInOneBranch
internal returnAssignsOneOfTwo
internal returnReadsItsDefault
internal overloadPick__solc17820
internal overloadPick__solc17833
internal modifierGuarded
internal modifierAroundBody
internal modifierOrdered
internal loopNestedReturn
internal setTotalToOne
internal firstOf
internal setTokenValue
internal readTokenValue
internal credit
internal digits
internal twiceKeepsLocal
internal repeatedContinuationBody
internal nextContinuationArgument
internal reenteredArgumentBody
internal conditionalContinuationBody
internal nestedReturningContinuation
internal loopContinuationBody
internal whileContinuationBody
internal doWhileContinuationBody
refuted storagePushReturnPrimitiveBindComplexReceiver
refuted storageArrayMethodReferencesComplexReceiver
refuted storageArrayMethodReferencesComposedCallReceiver
refuted unprovableStorageShortCircuitMutation
refuted invariantClosedFormSum
refuted unprovableInvariantBreakPostcondition
refuted unprovableInvariantForContinueUpdate
refuted testFixedShapeEmptyPushFixedElementReadsZero
refuted testEmptyPushFixedArrayReturnReadsZero
refuted testEmptyPushDynamicArrayReturnReadsZero
refuted testEmptyPushStructReturnReadsZero
pending:
-/
#guard_msgs in
#solkey_obligations Solkey.TestSuite
