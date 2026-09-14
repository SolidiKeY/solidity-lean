import Solidity.Examples.Common

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 3200000

/-! ## Cross-domain examples (storage ↔ memory) -/

/-! ### Example 31: `Person memory carol = alice` — storage-to-memory root copy
`storageToMemoryDeclCopyRoot` -/

example : solbox!{ Person memory carol = alice } —→ solbox!{} := by single_step storageToMemoryDeclCopyRoot

/-! ### Example 32: `Person memory carol = alice.account` — storage-to-memory field copy
`storageToMemoryDeclCopyField` -/

example : solbox!{ Person memory carol = alice.account } —→ solbox!{} := by single_step storageToMemoryDeclCopyField

/-! ### Example 33: `Token memory carol = alice.account.token`
  — storage-to-memory resolve base
1. `storageToMemoryDeclUnfoldRightFst`
2. `storagePlaceAlias`
3. `storageToMemoryDeclCopyField` -/

example : solbox!{ Token memory carol = alice.account.token } —↠ solbox!{} :=
  calc
    solbox!{ Token memory carol = alice.account.token }
        —→ solbox!{ Account storage sp = alice.account;
              Token memory carol = sp@Account.token } := by single_step storageToMemoryDeclUnfoldRightFst
    _ —→ solbox!{ Token memory carol = sp@Account.token } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step storageToMemoryDeclCopyField

/-! ### Example 34: `alice = carol` — memory-to-storage root store
`memoryToStorageStoreRoot` -/

example : solbox!{ alice = carol } —→ solbox!{} := by single_step memoryToStorageStoreRoot

/-! ### Example 35: `alice.account = david` — memory-to-storage save field
`memoryToStorageFieldCopyRoot` -/

example : solbox!{ alice.account = david } —→ solbox!{} := by single_step memoryToStorageFieldCopyRoot

/-! ### Example 36: `alice.account = carol.account`
  — memory-to-storage with complex source
1. `memoryToStorageUnfoldRightFstSource`
2. `memoryLocalDeclInitDrop`
3. `memoryFieldReadAliasRoot`
4. `memoryToStorageFieldCopyRoot` -/

example : solbox!{ alice.account = carol.account } —↠ solbox!{} :=
  calc
    solbox!{ alice.account = carol.account }
        —→ solbox!{ Account memory pv = carol.account;
              alice.account = pv@Account } := by single_step memoryToStorageUnfoldRightFstSource
    _ —→ solbox!{ pv@Account = carol.account;
              alice.account = pv@Account } := by single_step memoryLocalDeclInitDrop
    _ —→ solbox!{ alice.account = pv@Account } := by single_step memoryFieldReadAliasRoot
    _ —→ solbox!{} := by single_step memoryToStorageFieldCopyRoot

/-! ### Example 37: `alice.account.token = carol`
  — memory-to-storage with complex target path
1. `memoryToStorageUnfoldLeftFstTarget`
2. `storagePlaceAlias`
3. `memoryToStorageFieldCopyRoot` -/

example : solbox!{ alice.account.token = carol } —↠ solbox!{} :=
  calc
    solbox!{ alice.account.token = carol }
        —→ solbox!{ Account storage sp = alice.account;
              sp@Account.token = carol } := by single_step memoryToStorageUnfoldLeftFstTarget
    _ —→ solbox!{ sp@Account.token = carol } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step memoryToStorageFieldCopyRoot

end Solidity.Examples
