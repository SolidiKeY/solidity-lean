import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 800000

/-! ## Storage delete examples -/

/-! ### Example 15: `delete alice.account` — simple field target
`storageFieldDelete` -/

example : solbox!{ delete alice.account } —→ solbox!{} := by single_step storageFieldDelete

/-! ### Example 16: `delete alice.account.token` — complex target
1. `storageFieldDeleteUnfoldLeftFst`
2. `storagePlaceAlias`
3. `storageFieldDelete` -/

example : solbox!{ delete alice.account.token } —↠ solbox!{} :=
  calc
    solbox!{ delete alice.account.token }
        —→ solbox!{ Account storage sp = alice.account;
              delete sp@Account.token } := by single_step storageFieldDeleteUnfoldLeftFst
    _ —→ solbox!{ delete sp@Account.token } := by single_step storagePlaceAlias
    _ —→ solbox!{} := by single_step storageFieldDelete

/-! ### Example 17: `delete people[i]` — indexed delete (simple)
`storageIndexDelete` -/

example : solbox!{ delete people[i] } —→ solbox!{} := by single_step storageIndexDelete

end Solidity.Examples
