import Solidity.TestSuite.Problems

/-!
# The suggestions `#solkey_derive?` prints, pinned

Each runs the search, so this module imports only the statements and no
`Derived` module imports it: the searches run beside the theorems, not
before them.  A statement is picked by name (`only`), so a function added
to `TestSuite.sol` does not move a pin.

A statement the closer proves in the residue is `sol_prove` alone; a leaf
it leaves (a member written through the alias a `push` returns, past what
the layout types) is closed with the `wt` premise set aside
(`Derive.searchLeaf`), and several leaves each go under their `case`.
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
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

testStorageNestedPushReturnAlias: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only testStorageNestedPushReturnAlias
