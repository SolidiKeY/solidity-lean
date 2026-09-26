import Solidity.Calculus.Close

/-!
# Storage and memory: the copies between them

An assignment across the two data locations copies (storage to memory,
memory to storage): a memory declaration from a storage path
allocates a fresh object holding the storage value (`memoryStorageCopy`,
KeY's `copySt`), and a storage write from a memory path saves the memory
object's value (`memoryToStorage*`, KeY's `copyMem`).  Neither aliases, so a
write on one side after the copy is not seen on the other.  A nonsimple path
on the storage side is aliased first (`memoryStorageCopyUnfold`,
`memoryToStorageField_unfold_leftFst`), as a storage write's receiver is.

Each worked example is a walk naming its taclets and reading the
copied value back (`StorageSteps.lean`'s docstring says how to read one);
the programs of solkey's `taclets` suite (`storage-to-memory.key`,
`memory-to-storage.key`, …) are proved by the strategy.  The printed
`Person memory carol;` is the first line of a program here, since a memory
local has no root to fall back on (`Memory.lean`).
-/

namespace Solidity.Examples.CrossDomain

open Proves Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · Storage to memory -/

/-- `alice.age = 34; Person memory carol = alice; uint v = carol.age;` — the
copy holds the storage value, and the memory read finds it
(`memoryStorageCopy`, then `memoryFieldReadHeap`). -/
theorem storageToMemoryRootCopy :
    ⊨ dl!{ [ alice.age = 34; Person memory carol = alice; uint v = carol.age; ] v == 34 } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  -- { carol := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(…) }
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  apply close
  sol_symex
  sol_close

/-- `alice.account.balance = 10; Account memory acc = alice.account; uint v =
acc.balance;` — the same at a member source, which is aliased first
(`memoryStorageCopyUnfold`). -/
theorem storageToMemoryMemberCopy :
    ⊨ dl!{ [ alice.account.balance = 10; Account memory acc = alice.account;
             uint v = acc.balance; ] v == 10 } := by
  apply Proves.valid
  apply unfold .storageFieldWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteSave
  apply unfold .memoryLocalDeclInitDrop
  apply unfold .memoryStorageCopyUnfold
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .memoryStorageCopy
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  apply close
  sol_symex
  sol_close

/-- `Token memory t = alice.account.token;` — two selectors: the storage path
is aliased (`memoryStorageCopyUnfold`, whose alias's own right-hand side is a
Step 1 read), then copied. -/
theorem storageToMemoryNonsimplePath :
    ⊨ dl!{ [ alice.account.token.value = 3; Token memory t = alice.account.token;
             uint v = t.value; ] v == 3 } := by
  apply Proves.valid
  apply unfold .storageFieldWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet  -- `storageFieldRead_unfold_rightFst`
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteSave
  apply unfold .memoryLocalDeclInitDrop
  apply unfold .memoryStorageCopyUnfold
  apply unfold .storageLocalDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet  -- `storageFieldRead_unfold_rightFst`
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .memoryStorageCopy
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  apply close
  sol_symex
  sol_close

/-- `alice.age = 27; Person memory carol = alice; alice.age = 30;` — a copy,
not an alias: the later storage write is not seen through `carol`
(`storage-to-memory.key`). -/
theorem storageToMemoryIsCopy :
    ⊨ dl!{ [ alice.age = 27; Person memory carol = alice; alice.age = 30; uint v = carol.age; ]
           v == 27 } := by
  sol_symex
  sol_close

/-- `Person memory carol; carol = alice;` — the assignment form of the copy
(`memoryStorageCopy` on `mv = sp;`), a copy again. -/
theorem storageToMemoryAssign :
    ⊨ dl!{ [ alice.age = 30; Person memory carol; carol = alice; alice.age = 5;
             uint v = carol.age; ] v == 30 } := by
  sol_symex
  sol_close

/-- `Account memory acc = bob.account;` — a nonsimple storage source is aliased,
then copied (`memoryStorageCopyUnfold`), and the copy is again not an alias.
(solkey's `memoryStorageCopyUnfold` example copies `people[i]`; that program
closes the same way, at four times the cost.) -/
theorem storageToMemoryUnfold :
    ⊨ dl!{ [ bob.account.balance = 7; Account memory acc = bob.account;
             bob.account.balance = 9; uint v = acc.balance; ] v == 7 } := by
  sol_symex
  sol_close

/-! ## 2 · Memory to storage -/

/-- `carol.age = 34; alice = carol; uint v = alice.age;` — a storage root
written from memory stores the object's value (`memoryToStorageStoreRoot`),
and the storage read finds it. -/
theorem memoryToStorageRootCopy :
    ⊨ dl!{ [ Person memory carol; carol.age = 34; alice = carol; uint v = alice.age; ]
           v == 34 } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryFieldWriteStore
  apply update .memoryToStorageStoreRoot
  -- { storage := store(storage, alice, copyMem(mtSt, memory, carol)) }
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `acc.balance = 10; alice.account = acc; uint v = alice.account.balance;` —
from a memory local, at a storage *field* (`memoryToStorageFieldCopyRoot`). -/
theorem memoryToStorageFromAlias :
    ⊨ dl!{ [ Account memory acc = bob.account; acc.balance = 10; alice.account = acc;
             uint v = alice.account.balance; ] v == 10 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply unfold .memoryStorageCopyUnfold
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .memoryStorageCopy
  apply update .memoryFieldWriteStore
  apply update .memoryToStorageFieldCopyRoot
  -- { storage := save(storage, alice.account, copyMem(mtSt, memory, acc)) }
  apply unfold .localValueDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet  -- `storageFieldRead_unfold_rightFst`
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `carol.account.balance = 50; alice.account = carol.account;` — a memory
*member* as the source: no alias is introduced for it, the rule copies the
member's object directly (`memoryToStorageFieldCopyRoot`). -/
theorem memoryToStorageFromMemberSource :
    ⊨ dl!{ [ Person memory carol = bob; carol.account.balance = 50;
             alice.account = carol.account; uint v = alice.account.balance; ] v == 50 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryFieldWrite_unfold_leftFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldWriteStore
  apply update .memoryToStorageFieldCopyRoot
  apply unfold .localValueDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet  -- `storageFieldRead_unfold_rightFst`
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `t.value = 99; alice.account.token = t;` — the target is the nonsimple
path, so it is the target that is aliased
(`memoryToStorageField_unfold_leftFst`); the memory source is simple. -/
theorem memoryToStorageNonsimplePath :
    ⊨ dl!{ [ Token memory t = bob.account.token; t.value = 99; alice.account.token = t;
             uint v = alice.account.token.value; ] v == 99 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply unfold .memoryStorageCopyUnfold
  apply unfold .storageLocalDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet  -- `storageFieldRead_unfold_rightFst`
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .memoryStorageCopy
  apply update .memoryFieldWriteStore
  apply unfold .memoryToStorageField_unfold_leftFst
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .memoryToStorageFieldCopyRoot
  apply unfold .localValueDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet  -- `storageFieldRead_unfold_rightFst`
  apply unfold .storageLocalDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet  -- `storageFieldRead_unfold_rightFst`
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `carol.age = 8; alice = carol; carol.age = 9;` — a copy, not an alias: the
later memory write is not seen in storage (`memory-to-storage.key`). -/
theorem memoryToStorageIsCopy :
    ⊨ dl!{ [ Person memory carol = bob; carol.age = 8; alice = carol; carol.age = 9;
             uint v = alice.age; ] v == 8 } := by
  sol_symex
  sol_close

/-- `people[i] = carol;` — into an array element
(`memoryToStorageIndexArrayCopyRoot`), a copy again. -/
theorem memoryToStorageIndexArray :
    ⊨ dl!{ [ Person memory carol = bob; carol.age = 6; people[i] = carol; carol.age = 8;
             uint v = people[i].age; ] v == 6 } := by
  sol_symex
  sol_close

/-- `folks[k] = carol;` — into a mapping entry
(`memoryToStorageIndexMappingCopyRoot`). -/
theorem memoryToStorageIndexMapping :
    ⊨ dl!{ [ Person memory carol; carol.age = 6; folks[k] = carol; uint v = folks[k].age; ]
           v == 6 } := by
  sol_symex
  sol_close

/-! ## 3 · A run of the interpreter

`carol.account.balance = 8; alice = carol; carol.account.balance = 9;` — the
copy into storage is deep, so a later write to a *nested* memory object is not
seen either (solkey's `testMemoryFieldShallowCopy`).  `sol_close` reads a
copy member by member, one level down, so this one is a run from
`State.exampleStore`. -/

/-- What the local `x` holds after `P` runs from the store `σ`. -/
def localAfter {C : Contract} (σ : State) (P : Prog C) (x : String) : Res Binding := do
  (← Prog.run σ P).getEnv (.user x)

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 8))
-/
#guard_msgs in
#eval localAfter State.exampleStore
  sol{ Person memory carol; carol.account.balance = 8; alice = carol;
       carol.account.balance = 9; uint result = alice.account.balance; } "result"

end Solidity.Examples.CrossDomain
