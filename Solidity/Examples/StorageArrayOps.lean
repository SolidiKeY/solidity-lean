import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 800000

/-! ## Storage array / index operations

Index read/write on `people` (a `Person[]` storage array), push, and pop. -/

/-! ### Example 9: `people[i] = bob` — array index write copy
`storageIndexWriteArrayCopySourceBox` -/

example : solbox!{ people[i] = bob } —→ solbox!{} := by single_step storageIndexWriteArrayCopySourceBox

/-! ### Example 10: `people[i] = amount` — array index write save
`storageIndexWriteArraySaveBox` -/

example : solbox!{ people[i] = amount } —→ solbox!{} := by single_step storageIndexWriteArraySaveBox

/-! ### Example 11: `sp = people[i]` — array index read bind local root
`storageIndexReadArrayBindLocalRootBox` -/

example : solbox!{ sp = people[i] } —→ solbox!{} := by single_step storageIndexReadArrayBindLocalRootBox

/-! ### Example 12: `people.push(bob)` — push value copy source
`storagePushValueCopySource` -/

example : solbox!{ people.push(bob) } —→ solbox!{} := by single_step storagePushValueCopySource

/-! ### Example 13: `people.pop()` — pop save
`storagePopSaveBox` -/

example : solbox!{ people.pop() } —→ solbox!{} := by single_step storagePopSaveBox

/-! ### Example 14: `alice.friends[i] = bob` — nonsimple path index write
1. `storageIndexWriteUnfoldLeftFst`
2. `storagePlaceAlias`
3. `storageIndexWriteArrayCopySourceBox` -/

example : solbox!{ alice.friends[i] = bob } —↠ solbox!{} :=
  calc
    solbox!{ alice.friends[i] = bob }
        —→ solbox!{ PersonArray storage sp = alice.friends;
              sp@PersonArray[i] = bob } := by single_step storageIndexWriteUnfoldLeftFst
    _ —→ solbox!{ sp@PersonArray[i] = bob } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step storageIndexWriteArrayCopySourceBox

end Solidity.Examples
