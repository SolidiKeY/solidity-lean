import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 3200000

/-! ## Memory delete and array operations -/

/-! ### Example 28: `delete carol` — memory delete simple target
`memoryDeleteSimpleTarget` -/

example : solbox!{ delete carol } —→ solbox!{} := by single_step memoryDeleteSimpleTarget

/-! ### Example 29: `delete carol.account` — memory delete simple field target
`memoryDeleteSimpleTarget` -/

example : solbox!{ delete carol.account } —→ solbox!{} := by single_step memoryDeleteSimpleTarget

/-! ### Example 30: `delete carol.account.token` — memory delete complex target
1. `memoryDeleteComplexTarget`
2. `memoryLocalDeclInitDrop`
3. `memoryFieldReadAliasRoot`
4. `memoryDeleteSimpleTarget` -/

example : solbox!{ delete carol.account.token } —↠ solbox!{} :=
  calc
    solbox!{ delete carol.account.token }
        —→ solbox!{ Account memory mv = carol.account;
              delete mv@Account.token } := by single_step memoryDeleteComplexTarget
    _ —→ solbox!{ mv = carol.account;
              delete mv@Account.token } := by single_step memoryLocalDeclInitDrop
    _ —→ solbox!{ delete mv@Account.token } := by single_step memoryFieldReadAliasRoot
    _ —→ solbox!{} := by single_step memoryDeleteSimpleTarget

end Solidity.Examples
