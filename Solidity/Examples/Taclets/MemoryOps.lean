import Solidity.Semantics

/-!
# Ports of `keyext.solidity.examples/taclets`: memory operations

Memory declarations alias by identity; storage↔memory assignments
deep-copy (`copySt`/`copyMem`, `docs/copyStMem.md`).

`memory-array-index.key` (`new uint[](4)`) is not ported: the fragment
has no `new` expression.
-/

namespace Solidity
namespace TacletExamples

/-- `memory-decl-fresh.key` / `memory-decl-default.key`: the fresh
declaration succeeds *and* the allocated struct carries the default
field values (a post of `true == true` would only show that the
declaration neither reverts nor sticks). -/
example :
    (sol!{ < Person memory carol; result = carol.age >
           (result == 0) }).Holds := by
  native_decide

/-- `memory-deep-field.key` -/
example :
    (sol!{ < Person memory carol;
             carol.account.balance = 10;
             result = carol.account.balance > (result == 10) }).Holds := by
  native_decide

/-- `memory-root-alias.key`: memory roots alias. -/
example :
    (sol!{ < Person memory carol;
             Person memory david;
             david.age = 40;
             carol = david;
             carol.age = 41;
             result = david.age > (result == 41) }).Holds := by
  native_decide

/-- `memory-field-alias.key`: a memory field read aliases the nested
object. -/
example :
    (sol!{ < Person memory carol;
             Account memory mv = carol.account;
             mv.balance = 100;
             result = carol.account.balance > (result == 100) }).Holds := by
  native_decide

/-- `memory-field-reference-assign.key`: assigning a memory reference
into a field aliases, so writes through one path are visible through
the other. -/
example :
    (sol!{ < Person memory carol;
             Person memory david;
             Account memory mv = david.account;
             carol.account = mv;
             carol.account.balance = 60;
             result = david.account.balance > (result == 60) }).Holds := by
  native_decide

/-- `memory-root-delete-fresh.key` -/
example :
    (sol!{ < Person memory carol; delete carol; result = carol.age >
           (result == 0) }).Holds := by
  native_decide

/-- `memory-delete.key`: deleting a reference field re-binds a fresh
identity; the old alias keeps the old object. -/
example :
    (sol!{ < Person memory carol;
             Account memory mv = carol.account;
             carol.age = 20;
             mv.balance = 100;
             delete carol.age;
             delete carol.account;
             result = carol.age;
             uint aliasBalance = mv.balance;
             uint newBalance = carol.account.balance >
           (result == 0) && (aliasBalance == 100) && (newBalance == 0)
    }).Holds := by
  native_decide

/-- `storage-to-memory.key`: declaration from storage deep-copies; later
storage writes are invisible. -/
example :
    (sol!{ < alice.age = 27;
             Person memory carol = alice;
             alice.age = 30;
             result = carol.age > (result == 27) }).Holds := by
  native_decide

/-- `memory-to-storage.key`: assigning memory into storage deep-copies. -/
example :
    (sol!{ < Person memory carol;
             carol.age = 44;
             alice = carol;
             result = alice.age > (result == 44) }).Holds := by
  native_decide

/-- `testMemoryFieldShallowCopy` flavor (mainFeatures): memory→storage
copies the whole reachable object graph. -/
example :
    (sol!{ < Person memory carol;
             carol.account.balance = 8;
             alice = carol;
             carol.account.balance = 9;
             result = alice.account.balance > (result == 8) }).Holds := by
  native_decide

/-- KeY `memoryStorageCopy` (`m = sp;`): the assignment form of the
storage → memory deep copy. Later storage writes do not show through
the memory object (deep copy, not alias). -/
example :
    (sol!{ < alice.age = 30;
             Person memory carol;
             carol = alice;
             alice.age = 5;
             result = carol.age > (result == 30) }).Holds := by
  native_decide

/-- KeY `memoryStorageCopyUnfold`: a complex storage path is captured
into a storage alias, then deep-copied. -/
example :
    (sol!{ < uint i = 0; people.push(); people[i].age = 7;
             Person memory carol;
             carol = people[i];
             people[i].age = 9;
             result = carol.age > (result == 7) }).Holds := by
  native_decide

/-- KeY `memoryRootDeleteFreshRebind` (rule-map `verify` row): deleting
a memory root rebinds it to a fresh default object, and the fresh
object is writable. -/
example :
    (sol!{ < Person memory carol;
             carol.age = 5;
             delete carol;
             carol.age = 3;
             result = carol.age > (result == 3) }).Holds := by
  native_decide

/-- KeY `memoryToStorageIndexArrayCopyRoot` (rule-map `verify` row): a memory
root assigned into an indexed storage slot deep-copies
(`memoryToStorageIndexArrayCopyRoot{Box,Diamond}` in Lean, the mapping form
is `memoryToStorageIndexMappingCopyRoot`; the field form is
`memoryToStorageFieldCopyRoot`). -/
example :
    (sol!{ < uint i = 0; people.push();
             Person memory carol;
             carol.age = 6;
             people[i] = carol;
             carol.age = 8;
             result = people[i].age > (result == 6) }).Holds := by
  native_decide

end TacletExamples
end Solidity
