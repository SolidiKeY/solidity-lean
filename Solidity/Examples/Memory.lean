import Solidity.Calculus.Close

/-!
# Memory

Memory holds objects by identity: a memory local is bound to an object, a
memory declaration from a memory path binds the *same* object (an alias, no
copy), and a write through either name is a write to that object.  That is
the point of the memory examples,
and it is what the rules say: `memoryRootAlias` binds `mv₁ := mv₂`,
`memoryFieldReadAliasRoot` binds `mv₁ := read(memory, mv₂.fr)` — the identity
the member holds — and only `memoryFieldWriteStore` writes the heap.

Every example is a theorem `⊨ dl!{ … }`, proved by the strategy (`sol_symex;
sol_close`) or, for a worked example, by a walk naming each
taclet (`StorageSteps.lean`'s docstring says how to read one).  A memory local
has no root to fall back on, so every program declares its objects: either
fresh (`Person memory carol;`, `memoryReferenceDeclFreshAlloc`) or as a copy
of a storage object (`Person memory carol = alice;`, `memoryStorageCopy`,
whose storage side is `CrossDomain.lean`).  The printed worked examples start
after `Person memory carol;`; here that line is the first of the program.
Their derivations, line by line, are `MemoryChains.lean`.

Where `sol_close` cannot read the result back, the postcondition is `true` and
the walk is the claim.  Two things it does not know (`Close.lean`): that two
allocations are different objects, and what a member of a fresh object reads
as by default.  Those claims are runs of the interpreter at the end of the
file, from `State.exampleStore`.

A read whose receiver is not simple (`memoryFieldRead_unfold_rightFst`,
`memoryIndexRead_unfold_rightFst`) lands in a hole, as its storage twin does,
so the walk takes the strategy's rule for it, `unfoldRule (Stmt.step _ _ _).rule`, and
a comment names it (`StorageSteps.lean`'s docstring says why).

The arrays are the struct table's (`AST.lean`): a `Token[]` inside a
`TokenBucket` stands for `carol.account.tokens`, which
`Account` does not have here.  Memory `delete` is §6, `new T[](n)` and
`.length` §7.
-/

namespace Solidity.Examples.Memory

open Proves Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · Declarations -/

/-- `Person memory carol;` — a fresh object: the allocation is one update,
the identity and the heap that holds it (`memoryReferenceDeclFreshAlloc`),
and a write to it reads back. -/
theorem memoryDeclFreshAlloc :
    ⊨ dl!{ [ Person memory carol; carol.age = 5; uint x = carol.age; ] x == 5 } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `Person memory carolAlias = carol;` — aliasing by declaration: the
initialiser drops (`memoryLocalDeclInitDrop`) and the alias binds the same
identity (`memoryRootAlias`), with no heap write, so a write through the alias
is seen through `carol`. -/
theorem memoryDeclAlias :
    ⊨ dl!{ [ Person memory carol; Person memory carolAlias = carol; carolAlias.age = 3;
             uint x = carol.age; ] x == 3 } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryRootAlias
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `Token memory t = carol.account.token;` — the same one selector deeper:
the receiver `carol.account` is bound to a memory local first, and each
binding is a `read` of an identity (`memoryFieldReadAliasRoot`), still with
no heap write. -/
theorem memoryDeclDeepAlias :
    ⊨ dl!{ [ Person memory carol = alice; Token memory t = carol.account.token; t.value = 9;
             uint x = carol.account.token.value; ] x == 9 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryLocalDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! ## 2 · Writes and reads -/

/-- `carol.age = amount;` — both parts simple: one write (`memoryFieldWriteStore`). -/
theorem memoryFieldWrite :
    ⊨ dl!{ [ Person memory carol; carol.age = amount; uint x = carol.age; ] x == amount } := by
  sol_symex
  sol_close

/-- `carol.account.balance = 10;` — the memory twin of the headline
(`StorageSteps.deepFieldWrite`): the receiver is bound to a memory local
(`memoryFieldWrite_unfold_leftFst`, `memoryFieldReadAliasRoot`), then written
through (`memoryFieldWriteStore`), a `write` at an identity where storage has
a `save` at a path. -/
theorem memoryDeepFieldWrite :
    ⊨ dl!{ [ Person memory carol; carol.account.balance = 10; uint x = carol.account.balance; ]
           x == 10 } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryFieldWrite_unfold_leftFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `carol.age = a + b;` — a computed value is captured before the write
(`memoryFieldWriteUnfoldSource`), as a storage field write captures it. -/
theorem memoryFieldWriteCapturedRhs :
    ⊨ dl!{ [ Person memory carol; carol.age = a + b; uint x = carol.age; ] x == a + b } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryFieldWriteUnfoldSource
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! ## 3 · Aliasing -/

/-- `Account memory carolAcc = carol.account; carolAcc.balance = 100;` — the
aliasing example.  The alias binds the identity `carol.account` holds,
so the write through it is a write to that object, and the path reads it
back. -/
theorem memoryAliasWrite :
    ⊨ dl!{ [ Person memory carol; Account memory carolAcc = carol.account;
             carolAcc.balance = 100; uint x = carol.account.balance; ] x == 100 } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot  -- { carolAcc := read(memory, carol.account) }
  apply update .memoryFieldWriteStore     -- { memory := write(memory, carolAcc.balance, 100) }
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule   -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `carol.account = acc;` — a reference-valued field write stores the
identity (`memoryFieldWriteCopy`), so the two names share one object: a write
through `carol.account` is seen through `acc`. -/
theorem memoryFieldReferenceAssign :
    ⊨ dl!{ [ Person memory carol = alice; Account memory acc = bob.account; carol.account = acc;
             carol.account.balance = 60; uint x = acc.balance; ] x == 60 } := by
  sol_symex
  sol_close

/-- `carol.account = david.account;` — the source is a memory path, and its
identity is what is written: no alias is introduced for it
(`memoryFieldWriteCopy` takes any memory path). -/
theorem memoryFieldCopy :
    ⊨ dl!{ [ Person memory carol; Person memory david; carol.account = david.account; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryFieldWriteCopy
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `carol = david;` — a root assignment rebinds (`memoryRootAlias`); the heap
is untouched, and `carol` now names `david`'s object. -/
theorem memoryRootAssign :
    ⊨ dl!{ [ Person memory carol; Person memory david; david.age = 40; carol = david;
             carol.age = 41; uint x = david.age; ] x == 41 } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryReferenceDeclFreshAlloc
  apply update .memoryFieldWriteStore
  apply update .memoryRootAlias
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `carolAcc = d.account;` — a memory field on the right is not captured: the
local is rebound to the identity the read yields (`memoryFieldReadAliasRoot`),
and a write through it is a write to `d`'s account. -/
theorem memoryRootRebind :
    ⊨ dl!{ [ Person memory carol = alice; Account memory carolAcc = carol.account;
             Person memory d = bob; carolAcc = d.account; carolAcc.balance = 4;
             uint x = d.account.balance; ] x == 4 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! ## 4 · Arrays

A memory array element is read and written with `read`/`write` at an index
(`memoryIndexReadHeap`, `memoryIndexWriteStore`).  The bounds check is inside
the term, as `transfer`'s funds check is (`Revert.lean`): an index out of
bounds halts the update, which the box accepts. -/

/-- `uint[] memory v;` — a fresh array is one allocation, as a struct is
(`memoryReferenceDeclFreshAlloc`); it is empty, so every access to it
reverts. -/
theorem memoryArrayAlloc : ⊨ dl!{ [ uint[] memory v; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `v[i] = 100; x = v[i];` — the write and the read, both simple
(`memoryIndexWriteStore`, `memoryIndexReadHeap`), on a copy of `values`. -/
theorem memoryArrayWriteRead :
    ⊨ dl!{ [ uint[] memory v = values; v[i] = 100; uint x = v[i]; ] x == 100 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply update .memoryIndexWriteStore
  apply unfold .localValueDeclInitDrop
  apply update .memoryIndexReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `b.tokens[i].value = 42;` — a nested path under an index (the printed
`carol.account.values[i] = 42;`): the receiver `b.tokens[i]` is bound to a
memory local, which binds `b.tokens` first. -/
theorem memoryNestedArrayWrite :
    ⊨ dl[TestSuite]{ [ TokenBucket memory b = bucket; b.tokens[i].value = 42;
                       uint x = b.tokens[i].value; ] x == 42 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryFieldWrite_unfold_leftFst
  apply unfold .memoryLocalDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryIndexRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryIndexReadAliasRoot
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryIndexRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryIndexReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

set_option maxHeartbeats 300000 in
/-- `ts[i] = t;` — a reference-valued element written from a memory path: the
identity is stored (`memoryIndexWriteCopy`), so the slot and `t` alias (the
printed `carolTokens[i] = david.account.token;`). -/
theorem memoryArrayWriteRefSource :
    ⊨ dl[TestSuite]{ [ Token[] memory ts = tokens; Token memory t = tok; ts[i] = t;
                       t.value = 7; uint x = ts[i].value; ] x == 7 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply update .memoryIndexWriteCopy
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryIndexReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

set_option maxHeartbeats 400000 in
/-- `carol.account.token = ts[i];` — the other direction: the element's
identity is written into the member (the printed
`carol.account.token = davidTokens[i];`). -/
theorem memoryFieldWriteFromArrayElem :
    ⊨ dl[TestSuite]{ [ Person memory carol = alice; Token[] memory ts = tokens;
                       carol.account.token = ts[i]; ts[i].value = 5;
                       uint x = carol.account.token.value; ] x == 5 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryFieldWrite_unfold_leftFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldWriteCopy
  apply unfold .memoryFieldWrite_unfold_leftFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryIndexReadAliasRoot
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `Token memory t = b.tokens[i];` — a declaration from an element under a
nested path: two identity bindings and no heap write (the printed
`Token memory tok = carol.account.tokens[i];`). -/
theorem memoryDeclFromNestedArrayElem :
    ⊨ dl[TestSuite]{ [ TokenBucket memory b = bucket; Token memory t = b.tokens[i];
                       t.value = 3; uint x = b.tokens[i].value; ] x == 3 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryLocalDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryIndexRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryIndexReadAliasRoot
  apply update .memoryFieldWriteStore
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryIndexRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryIndexReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! ## 5 · Runs of the interpreter

What `sol_close` cannot read back — the default a fresh object holds, and two
allocations being different objects — holds of the contract's initial store,
`State.exampleStore`.  A struct's default is built by a well-founded
definition (`defaultForTy`) that `rfl` does not unfold, so these runs are
printed, as `StorageSuite.lean` prints its. -/

/-! `Person memory carol; uint result = carol.age;` — a fresh object holds its
type's default (`memory-decl-fresh.key`, `memory-decl-default.key`). -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore
  sol{ Person memory carol; uint result = carol.age; } "result"

/-! `Person memory carol; Person memory david; Account memory mv = david.account;
carol.account = mv; carol.account.balance = 60; uint result = david.account.balance;`
— the field assignment aliases across two fresh objects
(`memory-field-reference-assign.key`).  `memoryFieldReferenceAssign` is the
same claim over copies of storage objects, for every state. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 60))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore
  sol{ Person memory carol; Person memory david; Account memory mv = david.account;
       carol.account = mv; carol.account.balance = 60; uint result = david.account.balance; }
  "result"

/-! `uint[] memory v; v[0] = 100;` — a fresh array is empty, so the write is
out of bounds and reverts: the bounds check `memoryIndexWriteStore`'s `write`
carries. -/

/-- info: Except.error (Solidity.Semantics.Halt.revert) -/
#guard_msgs in
#eval Prog.run State.exampleStore (sol{ uint[] memory v; v[0] = 100; } : Prog StandardExample)

/-! ## 6 · Memory `delete`

`delete` of a memory local binds it to a fresh default object
(`memoryRootDeleteFreshRebind`); of a member or an element, it writes the
member's default there, a fresh default object for a reference
(`memoryFieldDeleteReference`, `memoryIndexDeleteReference`).  So an alias of
the old object keeps it, which is the point.  The values a fresh default holds
are the runs at the end of the section. -/

/-- `Person memory carol; Person memory carolAlias = carol; carol.age = 33;
delete carol; oldAge = carolAlias.age; newAge = carol.age;` — the alias keeps
the old object (`memoryRootDeleteFreshRebind`).  The printed program, its
`oldAge`, `newAge` undeclared; its chain is `MemoryChains.rootDelete`. -/
theorem memoryRootDelete :
    ⊨ dl!{ [ Person memory carol; Person memory carolAlias = carol; carol.age = 33; delete carol;
             oldAge = carolAlias.age; newAge = carol.age; ] true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryRootAlias
  apply update .memoryFieldWriteStore
  apply update .memoryRootDeleteFreshRebind
  apply update .memoryFieldReadHeap
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `delete carol.age;` — a primitive member is reset to its default
(`memoryFieldDeletePrimitive`), which reads back. -/
theorem memoryFieldDeletePrim :
    ⊨ dl!{ [ Person memory carol = alice; carol.age = 33; delete carol.age;
             uint x = carol.age; ] x == 0 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply update .memoryFieldWriteStore
  apply update .memoryFieldDeletePrimitive
  apply unfold .localValueDeclInitDrop
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `Person memory carol; Account memory carolAcc = carol.account;
carolAcc.balance = 100; delete carol.account; oldBal = carolAcc.balance;
newBal = carol.account.balance;` — a member of reference type gets a fresh
default object (`memoryFieldDeleteReference`); `carolAcc` keeps the old one.
The printed program; its chain is `MemoryChains.fieldDeleteRef`. -/
theorem memoryFieldDeleteRef :
    ⊨ dl!{ [ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100;
             delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]
           true } := by
  apply Proves.valid
  apply update .memoryReferenceDeclFreshAlloc
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldWriteStore
  apply update .memoryFieldDeleteReference
  apply update .memoryFieldReadHeap
  apply unfoldRule (Stmt.step _ _ _).rule  -- `memoryFieldRead_unfold_rightFst`
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryFieldReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `delete carolValues[i];` (box) — an element of an array of primitives
is reset (`memoryIndexDeletePrimitive`); out of bounds the write reverts,
which the box accepts. -/
theorem memoryIndexDeletePrim :
    ⊨ dl!{ [ uint[] memory carolValues = values; carolValues[i] = 5; delete carolValues[i];
             uint x = carolValues[i]; ] x == 0 } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply update .memoryIndexWriteStore
  apply update .memoryIndexDeletePrimitive
  apply unfold .localValueDeclInitDrop
  apply update .memoryIndexReadHeap
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `delete carolTokens[i];` (box) — an element of an array of structs gets
a fresh default object (`memoryIndexDeleteReference`). -/
theorem memoryIndexDeleteRef :
    ⊨ dl[TestSuite]{ [ Token[] memory carolTokens = tokens; delete carolTokens[i]; ] true } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply update .memoryIndexDeleteReference
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `delete carol.account.tokens[i];` (box; here `b.tokens[i]`, `TokenBucket`
having the tokens) — the receiver is bound first
(`memoryIndexDelete_unfold_leftFst`). -/
theorem memoryNestedIndexDelete :
    ⊨ dl[TestSuite]{ [ TokenBucket memory b = bucket; delete b.tokens[i]; ] true } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryIndexDelete_unfold_leftFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryIndexDeleteReference
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `delete carolValues[i + 1];` — a complex index is captured first
(`memoryIndexDeleteNonSimpleIndexCapture`). -/
theorem memoryIndexDeleteCapture :
    ⊨ dl!{ [ uint[] memory carolValues = values; delete carolValues[i + 1]; ] true } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .memoryIndexDeleteNonSimpleIndexCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .memoryIndexDeletePrimitive
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! `Person memory carolAlias = carol; carol.age = 33; delete carol;` — the
two reads: the alias still sees `33`, `carol` the default `0`. -/

/--
info: (Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 33)),
 Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0)))
-/
#guard_msgs in
#eval
  let P : Prog StandardExample := sol{ Person memory carol; Person memory carolAlias = carol;
    carol.age = 33; delete carol; uint oldAge = carolAlias.age; uint newAge = carol.age; }
  (Prog.localAfter State.exampleStore P "oldAge", Prog.localAfter State.exampleStore P "newAge")

/-! `carolAcc.balance = 100; delete carol.account;` — the old account keeps
`100`, the member reads the fresh default `0`. -/

/--
info: (Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 100)),
 Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0)))
-/
#guard_msgs in
#eval
  let P : Prog StandardExample := sol{ Person memory carol; Account memory carolAcc = carol.account;
    carolAcc.balance = 100; delete carol.account; uint oldBal = carolAcc.balance;
    uint newBal = carol.account.balance; }
  (Prog.localAfter State.exampleStore P "oldBal", Prog.localAfter State.exampleStore P "newBal")

/-! ## 7 · `new T[](n)` and `.length`

`new T[](n)` allocates `n` default elements (`memoryArrayFreshAlloc`, into
a memory local; `newArrayCapture` binds one first for any other target), and
`.length` reads an array's length (`memoryLengthRead`, `storageLengthRead`;
KeY's member reads at `length`). -/

/-- `uint[] memory xs = new uint[](n); uint len = xs.length;` —
`memoryArrayFreshAlloc`, then `memoryLengthRead`. -/
theorem memoryNewArray :
    ⊨ dl!{ [ uint[] memory xs = new uint[](n); uint len = xs.length; ] true } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryArrayFreshAlloc
  apply unfold .localValueDeclInitDrop
  apply update .memoryLengthRead
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `xs[0] = new uint[](3);` — a fresh array written into a memory element is
bound to a fresh memory local first (`newArrayCapture`). -/
theorem memoryNewArrayCapture :
    ⊨ dl!{ [ uint[][] memory xs = new uint[][](1); xs[0] = new uint[](3); ] true } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryArrayFreshAlloc
  apply unfold .newArrayCapture
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryArrayFreshAlloc
  apply update .memoryIndexWriteCopy
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `basketA.items = new uint[](2);` — into storage, through a fresh memory
local (`newArrayCapture`), then copied back (`memoryToStorageFieldCopyRoot`). -/
theorem storageNewArrayCapture :
    ⊨ dl[TestSuite]{ [ basketA.items = new uint[](2); uint len = basketA.items.length; ] true } := by
  apply Proves.valid
  apply unfold .newArrayCapture
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryArrayFreshAlloc
  apply update .memoryToStorageFieldCopyRoot
  apply unfold .localValueDeclInitDrop
  apply unfold .storageLengthRead_unfold_rightFst
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageLengthRead
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `TokenBucket memory b = bucket; uint len = b.tokens.length;` — the
receiver bound first (`memoryLengthRead_unfold_rightFst`). -/
theorem memoryNestedLength :
    ⊨ dl[TestSuite]{ [ TokenBucket memory b = bucket; uint len = b.tokens.length; ] true } := by
  apply Proves.valid
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryStorageCopy
  apply unfold .localValueDeclInitDrop
  apply unfold .memoryLengthRead_unfold_rightFst
  apply unfold .memoryLocalDeclInitDrop
  apply update .memoryFieldReadAliasRoot
  apply update .memoryLengthRead
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! `new uint[](3)` holds three zeros; `new Token[](2)` two fresh `Token`s,
each its own object; the lengths read back. -/

/--
info: (Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 3)),
 Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0)))
-/
#guard_msgs in
#eval
  let P : Prog StandardExample := sol{ uint[] memory xs = new uint[](3); uint len = xs.length;
    uint x = xs[2]; }
  (Prog.localAfter State.exampleStore P "len", Prog.localAfter State.exampleStore P "x")

/--
info: (Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 5)),
 Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0)))
-/
#guard_msgs in
#eval
  let P : Prog TestSuite := sol[TestSuite]{ Token[] memory ts = new Token[](2);
    ts[0].value = 5; uint a = ts[0].value; uint b = ts[1].value; }
  (Prog.localAfter State.testSuiteStore P "a", Prog.localAfter State.testSuiteStore P "b")

/-- info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 2)) -/
#guard_msgs in
#eval Prog.localAfter State.testSuiteStore
  (sol[TestSuite]{ basketA.items = new uint[](2); uint len = basketA.items.length; }) "len"

/-! ## 8 · Fixed-size arrays in memory

`uint[3] memory x;` allocates three default elements (a memory object marked
fixed, `MObj.array`); it is indexed by the same rules as a `uint[]`
(`memoryIndexWriteStore`, `memoryIndexReadHeap`, over either kind of array,
`ArrTy`), and its `.length` is the literal. -/

/-- `uint[3] memory x; x[1] = 5; uint y = x[1];` (`TestSuite.testMemoryFixedArrayLength`). -/
theorem memoryFixedWriteRead :
    ⊨ dl[TestSuite]{ [ uint[3] memory x; x[1] = 5; uint y = x[1]; ] y == 5 } := by
  sol_symex
  sol_close

/-! From the initial store, solkey's `testMemoryFixedArrayLength`,
`testMemoryNestedFixedArrayLength`, `testNewArrayOfFixedElementLength` and
`testMemoryStructFixedMemberLength`: each run ends normally. -/

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [
  (Prog.run State.testSuiteStore (sol[TestSuite]{ uint[3] memory x; assert(x.length == 3);
    x[1] = 5; assert(x[1] == 5); assert(x[0] == 0); })).isOk,
  (Prog.run State.testSuiteStore (sol[TestSuite]{ uint[2][3] memory y; assert(y.length == 3);
    assert(y[0].length == 2); })).isOk,
  (Prog.run State.testSuiteStore (sol[TestSuite]{ uint[2][] memory z = new uint[2][](4);
    assert(z.length == 4); assert(z[1].length == 2); })).isOk,
  (Prog.run State.testSuiteStore (sol[TestSuite]{ FixedTriple memory t;
    assert(t.items.length == 3); t.items[1] = 5; assert(t.items[1] == 5);
    assert(t.items[0] == 0); })).isOk]

/-! A struct with a fixed-size member copied into memory and back keeps the
member fixed: `triple.items` is still three long, and `delete` keeps it so. -/

/-- info: true -/
#guard_msgs in
#eval (Prog.run State.testSuiteStore (sol[TestSuite]{ FixedTriple memory t = triple;
  t.items[0] = 9; triple = t; assert(triple.items[0] == 9);
  assert(triple.items.length == 3); delete triple; assert(triple.items[0] == 0); })).isOk

end Solidity.Examples.Memory
