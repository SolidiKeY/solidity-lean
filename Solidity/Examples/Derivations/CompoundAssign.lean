import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Compound-assignment derivations

Step-by-step taclet derivations for `+=`/`-=`/`*=`/`/=`/`%=` on storage,
complementing the semantic ports in `Examples/Taclets/StorageOps.lean`.
Unlike `Examples/StorageCompound.lean`, which walks the *desugared*
read–compute–write block, these apply the dedicated compound-assignment
taclets (`storage{Root,Field,Index}{Add,…,Mod}Assign`). -/

/-! ### `age += amount` — root compound assignment -/

example :
    solbox!{ age += amount } ⇝[.storageRootCompoundAssign .add] solbox!{} := by
  rule_step

/-! ### `alice.age -= amount` — field compound assignment, simple path -/

example :
    solbox!{ alice.age -= amount }
      ⇝[.storageFieldCompoundAssign .sub] solbox!{} := by rule_step

/-! ### `values[i] *= amount` — index compound assignment -/

example :
    solbox!{ values[i] *= amount }
      ⇝[.storageIndexCompoundAssign .mul] solbox!{} := by rule_step

/-! ### `alice.account.balance += amount` — complex path unfolds first

The unfold rule freezes the value operand into `rv` *before* capturing any
part of the target (`Counterexamples/ErrorOrder.lean` is why), which costs
the three administrative steps `localValueDeclInitDrop` → `valueDeclSkip` →
`localValueAssign`.  They are elided into one `⇝*` line, exactly as the
calculus writes `⇝*`; the rule list keeps them checked. -/

sol_derivation fieldAddAssignComplexPath :
    solbox!{ alice.account.balance += amount }
  ⇝[.storageFieldCompoundAssignUnfoldLeftFst .add]
    solbox!{ uint rv = amount;
             Account storage sp = alice.account;
             sp@Account.balance += rv }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .localValueAssign]
    solbox!{ Account storage sp = alice.account; sp@Account.balance += rv }
  ⇝[.storagePlaceAlias]
    solbox!{ sp@Account.balance += rv }
  ⇝[.storageFieldCompoundAssign .add]
    solbox!{}

/-! ### Program: `alice.age = 30; alice.age += 4; result = alice.age`
Mirrors `storage-field-add-assign.key`, one taclet per statement. -/

sol_derivation fieldAddAssignProgram :
    solbox!{ alice.age = 30; alice.age += 4; result = alice.age }
  ⇝[.storageFieldWriteSave]             solbox!{ alice.age += 4; result = alice.age }
  ⇝[.storageFieldCompoundAssign .add]   solbox!{ result = alice.age }
  ⇝[.storageFieldReadFind]              solbox!{}

/-! ## Memory targets

The calculus's memory-target arithmetic (the rule set, "Memory-target
arithmetic"): the storage terminals with `read`/`write` on the heap in place
of `find`/`save`.  There is no root form — a memory root is an identity, not
a value cell — and no mapping form, because memory has no mappings. -/

/-! ### `carol.age += amount` — memory field compound assignment -/

example :
    solbox!{ carol.age += amount }
      ⇝[.memoryFieldCompoundAssign .add] solbox!{} := by rule_step

/-! ### `carol.age /= amount` — the calculus's separate `memoryFieldDivAssign`

The calculus splits division out because the zero divisor is a second sequent;
in Lean the revert lives in the interpreter's `applyBinOp`, so it is the same
rule at a different operator. -/

example :
    solbox!{ carol.age /= amount }
      ⇝[.memoryFieldCompoundAssign .div] solbox!{} := by rule_step

/-! ### `mv@UintArray[i] *= amount` — memory index compound assignment -/

example :
    solbox!{ mv@UintArray[i] *= amount }
      ⇝[.memoryIndexCompoundAssign .mul] solbox!{} := by rule_step

/-! ### `carol.account.balance += amount` — complex memory path unfolds first

The memory twin of `fieldAddAssignComplexPath` above, down to the `rv`
freeze: the path prefix goes into the memory alias `mv`, which
`memoryLocalDeclInitDrop` then binds. -/

sol_derivation memoryFieldAddAssignComplexPath :
    solbox!{ carol.account.balance += amount }
  ⇝[.memoryFieldCompoundAssignUnfoldLeftFst .add]
    solbox!{ uint rv = amount;
             Account memory mv = carol.account;
             mv@Account.balance += rv }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .localValueAssign]
    solbox!{ Account memory mv = carol.account; mv@Account.balance += rv }
  ⇝*[.memoryLocalDeclInitDrop, .memoryFieldReadAliasRoot]
    solbox!{ mv@Account.balance += rv }
  ⇝[.memoryFieldCompoundAssign .add]
    solbox!{}

end Solidity.Examples
