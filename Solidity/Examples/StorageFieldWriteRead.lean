import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 800000

/-! ## Storage field write / read examples

These examples demonstrate the step-by-step symbolic execution of storage
field assignments and reads, showing path decomposition via aliases. -/

/-! ### Example 1: `alice.age = ageVal`
`storageFieldWriteSave` -/

example : solbox!{ alice.age = amount } —→ solbox!{} := by single_step storageFieldWriteSave

/-! ### Example 2: `alice.account.balance = amount`
1. `storageFieldWriteUnfoldLeftFst`
2. `storagePlaceAlias`
3. `storageFieldWriteSave` -/

example : solbox!{ alice.account.balance = amount } —↠ solbox!{} :=
  calc
    solbox!{ alice.account.balance = amount }
        —→ solbox!{ uint se = amount;
              Account storage sp = alice.account;
              sp@Account.balance = se } := by
          single_step storageFieldWriteUnfoldLeftFst
    _ —→ solbox!{ uint se;
              se = amount;
              Account storage sp = alice.account;
              sp@Account.balance = se } := by single_step localValueDeclInitDrop
    _ —→ solbox!{ se = amount;
              Account storage sp = alice.account;
              sp@Account.balance = se } := by single_step valueDeclSkip
    _ —→ solbox!{ Account storage sp = alice.account;
              sp@Account.balance = se } := by single_step localValueAssign
    _ —→ solbox!{ sp@Account.balance = se } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step storageFieldWriteSave

/-! ### Example 3: `alice.account.token.value = amount`
1. `storageFieldWriteUnfoldLeftFst`
2. `storagePlaceAlias`
3. `storageFieldWriteSave` -/

example : solbox!{ alice.account.token.value = amount } —↠ solbox!{} :=
  calc
    solbox!{ alice.account.token.value = amount }
        —→ solbox!{ uint se = amount;
              Token storage sp = alice.account.token;
              sp@Token.value = se } := by
          single_step storageFieldWriteUnfoldLeftFst
    _ —→ solbox!{ uint se;
              se = amount;
              Token storage sp = alice.account.token;
              sp@Token.value = se } := by single_step localValueDeclInitDrop
    _ —→ solbox!{ se = amount;
              Token storage sp = alice.account.token;
              sp@Token.value = se } := by single_step valueDeclSkip
    _ —→ solbox!{ Token storage sp = alice.account.token;
              sp@Token.value = se } := by single_step localValueAssign
    _ —→ solbox!{ sp@Token.value = se } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step storageFieldWriteSave

/-! ### Example 4: `amount = alice.age`
`storageFieldReadFind` -/

example : solbox!{ amount = alice.age } —→ solbox!{} := by single_step storageFieldReadFind

/-! ### Example 5: `amount = alice.account.balance`
1. `storageFieldReadUnfoldRightFst`
2. `storagePlaceAlias`
3. `storageFieldReadFind` -/

example : solbox!{ amount = alice.account.balance } —↠ solbox!{} :=
  calc
    solbox!{ amount = alice.account.balance }
        —→ solbox!{ Account storage sp = alice.account;
              amount = sp@Account.balance } := by single_step storageFieldReadUnfoldRightFst
    _ —→ solbox!{ amount = sp@Account.balance } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step storageFieldReadFind

end Solidity.Examples
