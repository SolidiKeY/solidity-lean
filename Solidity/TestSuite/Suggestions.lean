import Solidity.TestSuite.ScopedProblems


/--
info: theorem Solkey.TestSuite.additionStorageWrite.proved : ⊢ Solkey.TestSuite.additionStorageWrite.problem := by
  sol_prove (steps := 128)

additionStorageWrite: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only additionStorageWrite

/--
info: theorem Solkey.TestSuite.testStorageNestedPushReturnAlias.proved : ⊢ Solkey.TestSuite.testStorageNestedPushReturnAlias.problem := by
  sol_prove (steps := 128)

testStorageNestedPushReturnAlias: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only testStorageNestedPushReturnAlias


/--
info: theorem Solkey.TestSuite.returnEarly.proved : ⊢ Solkey.TestSuite.returnEarly.problem := by
  sol_prove (steps := 128)

returnEarly: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only returnEarly

/--
info: theorem Solkey.TestSuite.tupleReturnDiscardsComponents.proved : ⊢ Solkey.TestSuite.tupleReturnDiscardsComponents.problem := by
  sol_prove (steps := 128)

tupleReturnDiscardsComponents: derived
-/
#guard_msgs in
#solkey_derive? Solkey.TestSuite only tupleReturnDiscardsComponents
