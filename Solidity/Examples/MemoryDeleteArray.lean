import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 3200000

/-! ## Memory delete and array operations -/

/-! ### Example 28: `delete carol` — memory delete of a root
`memoryRootDeleteFreshRebind` -/

example : solbox!{ delete carol } —→ solbox!{} := by single_step memoryRootDeleteFreshRebind

/-! ### Example 29: `delete carol.account` — memory delete of a reference member
`memoryFieldDeleteReference` (`account` is a struct; a primitive member would
be `memoryFieldDeletePrimitive`) -/

example : solbox!{ delete carol.account } —→ solbox!{} := by single_step memoryFieldDeleteReference

/-! ### Example 30: `delete carol.account.token` — memory delete complex target
1. `memoryFieldDeleteUnfoldLeftFst`
2. `memoryLocalDeclInitDrop`
3. `memoryFieldReadAliasRoot`
4. `memoryFieldDeleteReference` -/

example : solbox!{ delete carol.account.token } —↠ solbox!{} :=
  calc
    solbox!{ delete carol.account.token }
        —→ solbox!{ Account memory mv = carol.account;
              delete mv@Account.token } := by single_step memoryFieldDeleteUnfoldLeftFst
    _ —→ solbox!{ mv = carol.account;
              delete mv@Account.token } := by single_step memoryLocalDeclInitDrop
    _ —→ solbox!{ delete mv@Account.token } := by single_step memoryFieldReadAliasRoot
    _ —→ solbox!{} := by single_step memoryFieldDeleteReference

end Solidity.Examples
