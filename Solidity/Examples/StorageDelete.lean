import Solidity.Examples.Common

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 800000

/-! ## Storage delete examples -/

/-! ### Example 15: `delete alice.account` — simple target
`storageDeleteSimpleTarget` -/

example : solbox!{ delete alice.account } —→ solbox!{} := by single_step storageDeleteSimpleTarget

/-! ### Example 16: `delete alice.account.token` — complex target
1. `storageDeleteComplexTarget`
2. `storagePlaceAlias`
3. `storageDeleteSimpleTarget` -/

example : solbox!{ delete alice.account.token } —↠ solbox!{} :=
  calc
    solbox!{ delete alice.account.token }
        —→ solbox!{ Account storage sp = alice.account;
              delete sp@Account.token } := by single_step storageDeleteComplexTarget
    _ —→ solbox!{ delete sp@Account.token } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step storageDeleteSimpleTarget

/-! ### Example 17: `delete people[i]` — indexed delete (simple)
`storageDeleteSimpleTarget` -/

example : solbox!{ delete people[i] } —→ solbox!{} := by single_step storageDeleteSimpleTarget

end Solidity.Examples
