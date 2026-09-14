import Solidity.Examples.Common

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Increment / decrement derivations

Step-by-step taclet derivations for the `i++` family, complementing the
semantic ports in `Examples/Taclets/StorageOps.lean` (which are checked
against the interpreter by `native_decide`). Here every `⇝[.rule]` step is
one rule application on the head statement, so the rewriting is visible
line by line and the rule that fired is part of the statement.

`--` cannot be a Lean token (it starts a comment), so a decrement is
spelled `predec(e)` / `postdec(e)` in the surface notation -- the same
`IncDec.preDec`/`.postDec` statement, written without dropping to
constructors. -/

/-! ### `age++;` — root post-increment (statement form) -/

example : solbox!{ age++ } ⇝[.storageRootIncDec .postInc] solbox!{} := by
  rule_step

/-! ### `++age;` — root pre-increment (statement form) -/

example : solbox!{ ++age } ⇝[.storageRootIncDec .preInc] solbox!{} := by
  rule_step

/-! ### `age--;` — root post-decrement -/

example : solbox!{ postdec(age) } ⇝[.storageRootIncDec .postDec] solbox!{} := by
  rule_step

/-! ### `--age;` — root pre-decrement -/

example : solbox!{ predec(age) } ⇝[.storageRootIncDec .preDec] solbox!{} := by
  rule_step

/-! ### `alice.age++;` — field post-increment, simple path -/

example : solbox!{ alice.age++ } ⇝[.storageFieldIncDec .postInc] solbox!{} := by
  rule_step

/-! ### `result = age++` — assignment form yields the old value -/

example :
    solbox!{ result = age++ }
      ⇝[.storageRootIncDecAssignment .postInc] solbox!{} := by rule_step

/-! ### `result = ++age` — assignment form yields the new value -/

example :
    solbox!{ result = ++age }
      ⇝[.storageRootIncDecAssignment .preInc] solbox!{} := by rule_step

/-! ### `result = values[i]++` — index assignment form -/

example :
    solbox!{ result = values[i]++ }
      ⇝[.storageIndexIncDecAssignment .postInc] solbox!{} := by rule_step

/-! ### `alice.account.balance++;` — complex path unfolds first
The path prefix is hoisted into the storage alias `sp`, the alias is
bound, and the increment happens through it. -/

sol_derivation fieldPostIncrementComplexPath :
    solbox!{ alice.account.balance++ }
  ⇝[.storageFieldIncDecUnfoldLeftFst .postInc]
    solbox!{ Account storage sp = alice.account; sp@Account.balance++ }
  ⇝[.storagePlaceAlias]
    solbox!{ sp@Account.balance++ }
  ⇝[.storageFieldIncDec .postInc]
    solbox!{}

/-! ### Program: `age = 10; age++; result = age`
Mirrors `storage-root-postincrement.key`, one taclet per statement. -/

sol_derivation rootPostincrementProgram :
    solbox!{ age = 10; age++; result = age }
  ⇝[.storageRootWriteStore]       solbox!{ age++; result = age }
  ⇝[.storageRootIncDec .postInc]  solbox!{ result = age }
  ⇝[.storageRootReadSelect]       solbox!{}

/-! ## Memory targets

The calculus's `memoryFieldIncrement` and its solkey siblings: the inc/dec
family with the heap read/write in place of `find`/`save`. -/

/-! ### `carol.age++;` — memory field increment -/

example :
    solbox!{ carol.age++ }
      ⇝[.memoryFieldIncDec .postInc] solbox!{} := by rule_step

/-! ### `result = carol.age++` — memory assignment form -/

example :
    solbox!{ result = carol.age++ }
      ⇝[.memoryFieldIncDecAssignment .postInc] solbox!{} := by rule_step

/-! ### `++mv@UintArray[i];` — memory index increment -/

example :
    solbox!{ ++mv@UintArray[i] }
      ⇝[.memoryIndexIncDec .preInc] solbox!{} := by rule_step

/-! ### `carol.account.balance++;` — complex memory path unfolds first -/

sol_derivation memoryFieldPostIncrementComplexPath :
    solbox!{ carol.account.balance++ }
  ⇝[.memoryFieldIncDecUnfoldLeftFst .postInc]
    solbox!{ Account memory mv = carol.account; mv@Account.balance++ }
  ⇝*[.memoryLocalDeclInitDrop, .memoryFieldReadAliasRoot]
    solbox!{ mv@Account.balance++ }
  ⇝[.memoryFieldIncDec .postInc]
    solbox!{}

end Solidity.Examples
