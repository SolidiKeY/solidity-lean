import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Full-program walkthroughs

Complete multi-statement programs from `keyext.solidity.examples/taclets`,
reduced to the empty block one taclet at a time. The corresponding
semantic tests (with postconditions, verified by `native_decide`) are in
`Examples/Taclets/StorageOps.lean`; here the same programs show *which*
rule fires on each statement and what the program rewrites to.

These read as the calculus's derivations do: `⇝[.rule]` for a step whose rule
is worth naming on the arrow, `⇝*` for a run of administrative steps the
calculus would collapse into one `⇝*` line. -/

/-! ### `storage-field-deep-write-read.key` (the goal example)
`alice.account.balance = 34; result = alice.account.balance`

The write unfolds its path into the storage alias `sp`, having first frozen
the value operand into `se` (`Counterexamples/ErrorOrder.lean`); the read
then unfolds through the same alias. -/

sol_derivation storageFieldDeepWriteRead :
    solbox!{ alice.account.balance = 34; .. readBack }
  ⇝[.storageFieldWriteUnfoldLeftFst]
    solbox!{ uint se = 34;
             Account storage sp = alice.account;
             sp@Account.balance = se;
             .. readBack }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .localValueAssign]
    solbox!{ Account storage sp = alice.account;
             sp@Account.balance = se;
             .. readBack }
  ⇝[.storagePlaceAlias]
    solbox!{ sp@Account.balance = se; .. readBack }
  -- The suffix is now the active statement, so it is written out again.
  ⇝[.storageFieldWriteSave]
    solbox!{ result = alice.account.balance }
  ⇝[.storageFieldReadUnfoldRightFst]
    solbox!{ Account storage sp = alice.account;
             result = sp@Account.balance }
  ⇝[.storagePlaceAlias]
    solbox!{ result = sp@Account.balance }
  ⇝[.storageFieldReadFind]
    solbox!{}
where
  -- The read half of the program: the calculus's inactive suffix `omega`, named
  -- once instead of retyped on every line while the write is executed.
  readBack := sblock!{ result = alice.account.balance }

/-! ### `storage-index-postincrement-assign.key` (modulo the length premise)
`values[i] = 40; result = values[i]++` -/

sol_derivation storageIndexPostincrementAssign :
    solbox!{ values[i] = 40; result = values[i]++ }
  ⇝[.storageIndexWriteArraySaveBox]
    solbox!{ result = values[i]++ }
  ⇝[.storageIndexIncrementAssignment .postInc]
    solbox!{}

end Solidity.Examples
