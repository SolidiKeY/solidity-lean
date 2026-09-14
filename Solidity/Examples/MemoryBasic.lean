import Solidity.Examples.Common

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 1600000

/-! ## Memory basic operations

Aliasing, field write/read, declaration splitting, and root rebinding. -/

/-! ### Example 19: `carol.age = amount` — memory field write store
`memoryFieldWriteStore` -/

example : solbox!{ carol.age = amount } —→ solbox!{} := by single_step memoryFieldWriteStore

/-! ### Example 20: `carol = david` — memory root alias
`memoryRootAlias` -/

example : solbox!{ carol = david } —→ solbox!{} := by single_step memoryRootAlias

/-! ### Example 21: `Person memory carol = david` — memory decl init split
1. `memoryLocalDeclInitDrop`
2. `memoryRootAlias` -/

example : solbox!{ Person memory carol = david } —↠ solbox!{} :=
  calc
    solbox!{ Person memory carol = david }
        —→ solbox!{ carol = david } := by single_step memoryLocalDeclInitDrop
    _ —→ solbox!{} := by single_step memoryRootAlias

/-! ### Example 22: `Person memory carol` — memory decl fresh alloc
`memoryDeclFreshAlloc` -/

example : solbox!{ Person memory carol } —→ solbox!{} := by single_step memoryDeclFreshAlloc

/-! ### Example 23: `amount = carol.age` — memory field read heap
`memoryFieldReadHeap` -/

example : solbox!{ amount = carol.age } —→ solbox!{} := by single_step memoryFieldReadHeap

/-! ### Example 24: `david = carol.account` — memory field read alias root
`memoryFieldReadAliasRoot` -/

example : solbox!{ david = carol.account } —→ solbox!{} := by single_step memoryFieldReadAliasRoot

/-! ### Example 25: `carol.account.balance = amount` — memory field write with resolve
1. `memoryFieldWriteUnfoldLeftFst`
2. `memoryLocalDeclInitDrop`
3. `memoryFieldReadAliasRoot`
4. `memoryFieldWriteStore` -/

example : solbox!{ carol.account.balance = amount } —↠ solbox!{} :=
  calc
    solbox!{ carol.account.balance = amount }
        —→ solbox!{ uint rv = amount;
              Account memory mv = carol.account;
              mv.balance = rv } := by
          single_step memoryFieldWriteUnfoldLeftFst
    _ —→ solbox!{ uint rv;
              rv = amount;
              Account memory mv = carol.account;
              mv.balance = rv } := by single_step localValueDeclInitDrop
    _ —→ solbox!{ rv = amount;
              Account memory mv = carol.account;
              mv.balance = rv } := by single_step valueDeclSkip
    _ —→ solbox!{ Account memory mv = carol.account;
              mv.balance = rv } := by single_step localValueAssign
    _ —→ solbox!{ mv = carol.account;
              mv.balance = rv } := by single_step memoryLocalDeclInitDrop
    _ —→ solbox!{ mv.balance = rv } := by
          single_step memoryFieldReadAliasRoot
    _ —→ solbox!{} := by single_step memoryFieldWriteStore

/-! ### Example 26: `amount = carol.account.balance` — memory field read with resolve
1. `memoryFieldReadUnfoldRightFst`
2. `memoryLocalDeclInitDrop`
3. `memoryFieldReadAliasRoot`
4. `memoryFieldReadHeap` -/

example : solbox!{ amount = carol.account.balance } —↠ solbox!{} :=
  calc
    solbox!{ amount = carol.account.balance }
        —→ solbox!{ Account memory mv = carol.account;
              amount = mv.balance } := by single_step memoryFieldReadUnfoldRightFst
    _ —→ solbox!{ mv = carol.account;
              amount = mv.balance } := by single_step memoryLocalDeclInitDrop
    _ —→ solbox!{ amount = mv.balance } := by single_step memoryFieldReadAliasRoot
    _ —→ solbox!{} := by single_step memoryFieldReadHeap

/-! ### Example 27: `carol.account = david.account` — memory field read split LHS
1. `memoryFieldReadUnfoldRightSndResult`
2. `memoryLocalDeclInitDrop`
3. `memoryFieldReadAliasRoot`
4. `memoryFieldWriteCopy` -/

example : solbox!{ carol.account = david.account } —↠ solbox!{} :=
  calc
    solbox!{ carol.account = david.account }
        —→ solbox!{ Account memory pv = david.account;
              carol.account = pv@Account } := by single_step memoryFieldReadUnfoldRightSndResult
    _ —→ solbox!{ pv@Account = david.account;
              carol.account = pv@Account } := by single_step memoryLocalDeclInitDrop
    _ —→ solbox!{ carol.account = pv@Account } := by single_step memoryFieldReadAliasRoot
    _ —→ solbox!{} := by single_step memoryFieldWriteCopy

end Solidity.Examples
