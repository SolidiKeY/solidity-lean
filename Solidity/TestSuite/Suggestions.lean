import Solidity.TestSuite.ScopedProblems

/-!
# The suggestions `#solkey_derive?` prints, pinned

Each runs the search, so this module imports only the statements and no
`Derived` module imports it: the searches run beside the theorems, not
before them.  A statement is picked by name (`only`), so a function added
to `TestSuite.sol` does not move a pin.

A statement the closer proves in the residue is `sol_prove` alone; a leaf
it leaves (a member written through the alias a nested `push` returns,
outside the scoped closer's fragment) is closed on its scoped form
(`sol_leaf`, then a closer: `Derive.searchLeaf`), and several leaves each
go under their `case`.
-/

/--
info: theorem Solkey.TestSuite.additionStorageWrite.proved : ⊢ Solkey.TestSuite.additionStorageWrite.problem := by
  sol_prove

additionStorageWrite: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only additionStorageWrite

/--
info: theorem Solkey.TestSuite.testStorageNestedPushReturnAlias.proved : ⊢ Solkey.TestSuite.testStorageNestedPushReturnAlias.problem := by
  sol_prove
  sol_leaf
  sol_close

testStorageNestedPushReturnAlias: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only testStorageNestedPushReturnAlias

/-! `returnEarly` calls `returnSign` (three exits) three times, and
`tupleReturnDiscardsComponents` runs `returnStats` (four conditionals and an
`&&`) on literals: a split whose condition is ground under its updates keeps
only the branch it takes (`Seq.refutes`, closed by
`Proves.closeFalse`), so each replay fits one
declaration (`Derive.replayFits`). -/

/--
info: theorem Solkey.TestSuite.returnEarly.proved : ⊢ Solkey.TestSuite.returnEarly.problem := by
  sol_prove

returnEarly: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only returnEarly

/--
info: theorem Solkey.TestSuite.tupleReturnDiscardsComponents.proved : ⊢ Solkey.TestSuite.tupleReturnDiscardsComponents.problem := by
  sol_prove

tupleReturnDiscardsComponents: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only tupleReturnDiscardsComponents
