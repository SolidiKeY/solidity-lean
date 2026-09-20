import Solidity.Tactics.Rewrite

/-!
# The calculus's worked examples — the lines after the program

A worked example of the paper does not end when the last statement is
consumed.  The calculus's chain leaves an update whose right-hand sides are
still terms, and the paper keeps rewriting them by the theories' rules until
the value is there:

```
⇝  {mem := M₁, storage := S₁, v := findSt(store(storage, alice, copyMem(∅, M₁, carol)), alice·age)}
⇝  {mem := M₁, storage := S₁, v := readR(write(mem, carol, age, 42), carol, ⟨age⟩)}
⇝  {mem := M₁, storage := S₁, v := 42}
```

Those three lines are `Paper/CrossDomain.lean`'s missing tail, and they are
not `⇝` lines of the calculus: no taclet fires, an equation between terms is
applied.  This module is them — one `sol_rewrite` chain per example that has
any, picking up where that example's `sol_derivation` stops.

`docs/paper-parity.md` names both chains of such an example, and the pair is
the example.  Why the two cannot be one chain is `Tactics/Rewrite.lean`'s
docstring: `Sequent.upd` is a state function, and the terminal line is false
of one — at a pre-state where the memory variable is unbound the read errors
where the literal does not.  It is true of the *terms*, which is what the
paper's signature is about and what these chains are written in.

## Conventions

The scratch names are `docs/paper-parity.md`'s, so a chain here and its
calculus twin read the same; the values are the Lean chain's where the paper's
differ (`34` for the paper's `25`/`42`).  A root that the calculus invents is
a variable `r` rather than a numeral: the paper's `new(mem, r) →` premise says
only that it is fresh, and a chain that picked `7` would be proving less.

Paths are `List Seg`, so the paper's `alice·account·balance` is
`[alice, account, balance]` and its `⟨f⟩` is `[f]` -- which is why
`singletonPath` has no rule here, as `Theory/Rewrite.lean` records.
-/

namespace Solidity.Examples.Paper.Theory

open Solidity.Theory Solidity.Theory.StValue Semantics

/-! ## The segments the worked examples use -/

private abbrev alice   : Seg := .field "alice"
private abbrev bob     : Seg := .field "bob"
private abbrev age     : Seg := .field "age"
private abbrev account : Seg := .field "account"
private abbrev balance : Seg := .field "balance"
private abbrev token   : Seg := .field "token"
private abbrev value   : Seg := .field "value"
private abbrev tokens  : Seg := .field "tokens"
private abbrev len     : Seg := .field "length"

/-! ## The two abbreviations the paper writes

`M₁` and `S₁` are the paper's own names for the memory and storage terms a
chain has accumulated by the time the program is gone
(`sections/memory-to-storage.tex`).  They are functions of the fresh root here
because the root is a variable: the calculus's `new(mem, r) →` premise says
only that it is fresh, and a chain that picked a numeral would prove less. -/

/-- `M₁ = write(mem, idC(r, ∅), a, v)` -- one memory write to a fresh root. -/
private abbrev memWrite (r : IdentityPrim) (a : Seg) (v : Int) : Memory :=
  .write .mtMem (.idC r []) a (.prim (.int v))

/-- `S₁ = save(∅, p, v)` -- one storage write. -/
private abbrev stSave (p : List Seg) (v : Int) : Struct :=
  save Struct.mtSt p (StValue.int v)

/-! ## 1 · Storage fields and roots

The read that follows `deepFieldWrite`.  `sections/storage-examples.tex` states
it in prose — "the subsequent field read sees …" — and
`Theory/Storage.lean`'s `Sanity` section had it as an anonymous `example`; this
is the same fact as a chain, with the rule on the arrow. -/

/-- **`alice.account.balance = 10; v = alice.account.balance;`** — the headline
example's read, which is `findOnSave` and nothing else.  The slides' name for
this rule is `findOnSaveEqual`. -/
sol_rewrite deepFieldWriteValue (s : Struct) :
    findSt (save s [alice, account, balance] (StValue.int 10)) [alice, account, balance]
  =[.findOnSave] StValue.int 10

/-- **The frame.**  `bob.age` does not see a write to `alice.account.balance`:
the two paths diverge at the first segment.  `findOnSaveDifferent` in the
slides' naming. -/
sol_rewrite deepFieldWriteFrame (s : Struct) :
    findSt (save s [alice, account, balance] (StValue.int 10)) [bob, age]
  =[.findOnSaveDifferent] findSt s [bob, age]

/-- **Reading above the write.**  A prefix of the written path reads the write
pushed down to what is left of it — the step the calculus takes when an alias
was captured above the target. -/
sol_rewrite deepFieldWritePrefix (s : Struct) :
    findSt (save s ([alice] ++ [account, balance]) (StValue.int 10)) [alice]
  =[.findOnSavePrefix]
    StValue.st (save (asStruct (findSt s [alice])) [account, balance] (StValue.int 10))

/-! ## 2 · Storage arrays — the push/pop aliasing argument

`sections/storage-examples.tex` writes this one entirely in the theory: three
abbreviating `save` equations and then a read off them.  The `let` prefix is
the paper's own "Let S₁ = …", and the chain is its next sentence, "the
subsequent field read sees `findSt(S₃, tokens[0].value) = 7`".

`Paper/Checks.lean`'s `pushPopSlotCleared` runs the same program through the
interpreter; this is the calculus's side of it. -/

sol_rewrite pushPopSlotValue
    let S1 := save (delAt Struct.mtSt [tokens, .at 0]) [tokens, len] (StValue.int 0),
        S2 := save S1 [tokens, .at 0, value] (StValue.int 7),
        S3 := save S2 [tokens, len] (StValue.int 1) :
    findSt S3 [tokens, .at 0, value]
  =[.findOnSaveDifferent] findSt S2 [tokens, .at 0, value]
  =[.findOnSave]          StValue.int 7

/-! ## 3 · `delete`

A deleted leaf reads as its type's default, and a leaf beside it survives:
`delAtEmpty` puts the marker on, `selectOnDelAt` reads through it. -/

sol_rewrite deleteLeafValue :
    delAt (stSave [alice, age] 34) []
  =[.delAtEmpty] delNode (stSave [alice, age] 34)

/-- …and the leaf below it then reads as its type's default, which is
`delValueDefault` at the end of the walk. -/
sol_rewrite deleteLeafDefault (q : PrimVal) :
    delValue (StValue.prim q)
  =[.delValueDefault] StValue.prim (primDefault q)

/-! ## 5–7 · Memory

The last line of the paper's aliasing example is pure term rewriting: the
member of a freshly added root reads as `dflt`, and the cast at the `Identity`
sort turns that into the identity one field further down.  That is how a
reference member exists as soon as its parent does, without anything being
allocated for it. -/

/-- **`Person memory carol; carol.account.balance = 100;`** — the tail of
`memoryAliasWrite`.  `r` is the root the calculus invents; the chain says
nothing about which one it is. -/
sol_rewrite memoryAliasIdentity (r : IdentityPrim) (ty : RefTy) :
    MemValue.asIdentity (Memory.readIn (.addM .mtMem r ty) (.idC r []) account)
      (.idC r []) account
  =[.readAddEqual]    MemValue.asIdentity .dflt (.idC r []) account
  =[.defaultIdentity] Identity.idC r ([] ++ [account])

/-- **The read-over-write the memory examples end on.** -/
sol_rewrite memoryFieldValue (r : IdentityPrim) :
    Memory.readR (memWrite r age 34) (.idC r []) [age]
  =[.readRSingleton] Memory.readIn (memWrite r age 34) (.idC r []) age
  =[.readWriteEqual] MemValue.prim (PrimVal.int 34)

/-! ## 8 · Cross-domain copies

The four lines `Paper/CrossDomain.lean` stops short of, and the reason it does:
`copySt` and `copyMem` are the two lazy views, and until
`Theory/CrossDomain.lean` there was nothing to write them with.  Each chain
below starts where its calculus twin's last update leaves the read. -/

/-- **`alice.age = 34; Person memory mv2 = alice; v = mv2.age;`** — the tail of
`storageToMemoryRootCopy`.  `sections/storage-to-memory.tex` counts these: "the
sixth step is `readCopySt`; the seventh is read-over-write on the resulting
`find`". -/
sol_rewrite storageToMemoryRootCopyValue (r : IdentityPrim) :
    Memory.readIn (.copySt .mtMem r (stSave [alice, age] 34)) (.idC r [alice]) age
  =[.readCopySt] StValue.toMemValue (find (stSave [alice, age] 34) ([alice] ++ [age]))
  =[.findOnSave] StValue.toMemValue (StValue.int 34)
  =              MemValue.prim (PrimVal.int 34)

/-- …and the same read below *another* root, which does not see the copy at
all: `readCopyStOther`, the frame of the storage-to-memory view. -/
sol_rewrite storageToMemoryOtherRoot (r1 r2 : IdentityPrim) (m : Memory) (s : Struct)
    (hne : r1 ≠ r2) :
    Memory.readIn (.copySt m r1 s) (.idC r2 [alice]) age
  =[.readCopyStOther] Memory.readIn m (.idC r2 [alice]) age

/-- **`carol.age = 34; alice = carol; v = alice.age;`** — the tail of
`memoryToStorageRootCopy`, and the three lines the paper spends on it.  The
decisive one is `findCopyMem`: a storage read becomes a memory read without
either theory having walked anything. -/
sol_rewrite memoryToStorageRootCopyValue (r : IdentityPrim) :
    StValue.find (.storeSt Struct.mtSt alice
      (.st (.copyMem (memWrite r age 34) (.idC r [])))) [alice, age]
  =[.findPath]       StValue.find (.copyMem (memWrite r age 34) (.idC r [])) [age]
  =[.findCopyMem]    MemValue.ofView (memWrite r age 34)
                       (Memory.readR (memWrite r age 34) (.idC r []) [age])
  =[.readRSingleton] MemValue.ofView (memWrite r age 34)
                       (Memory.readIn (memWrite r age 34) (.idC r []) age)
  =[.readWriteEqual] StValue.prim (PrimVal.int 34)

/-- **`mv.balance = 10; alice.account = mv; v = alice.account.balance;`** — the
tail of `memoryToStorageFromAlias`.  The view sits one selector deeper, so the
storage half of the read is two segments and the memory half one. -/
sol_rewrite memoryToStorageFromAliasValue (r : IdentityPrim) :
    StValue.find (.storeSt Struct.mtSt alice
        (.st (.storeSt Struct.mtSt account
          (.st (.copyMem (memWrite r balance 10) (.idC r []))))))
      [alice, account, balance]
  =[.findPath]       StValue.find (.storeSt Struct.mtSt account
                       (.st (.copyMem (memWrite r balance 10) (.idC r []))))
                       [account, balance]
  =[.findPath]       StValue.find (.copyMem (memWrite r balance 10) (.idC r [])) [balance]
  =[.findCopyMem]    MemValue.ofView (memWrite r balance 10)
                       (Memory.readR (memWrite r balance 10) (.idC r []) [balance])
  =[.readRSingleton] MemValue.ofView (memWrite r balance 10)
                       (Memory.readIn (memWrite r balance 10) (.idC r []) balance)
  =[.readWriteEqual] StValue.prim (PrimVal.int 10)

/-- **`carolToken.value = 99; alice.account.token = carolToken; v = …`** — the
tail of `memoryToStorageNonsimplePath`, where the *target* is the nonsimple
path.  Three storage selectors above the view instead of two. -/
sol_rewrite memoryToStorageNonsimplePathValue (r : IdentityPrim) :
    StValue.find (.storeSt Struct.mtSt alice
        (.st (.storeSt Struct.mtSt account
          (.st (.storeSt Struct.mtSt token
            (.st (.copyMem (memWrite r value 99) (.idC r []))))))))
      [alice, account, token, value]
  =[.findPath]       StValue.find (.storeSt Struct.mtSt account
                       (.st (.storeSt Struct.mtSt token
                         (.st (.copyMem (memWrite r value 99) (.idC r []))))))
                       [account, token, value]
  =[.findPath]       StValue.find (.storeSt Struct.mtSt token
                       (.st (.copyMem (memWrite r value 99) (.idC r [])))) [token, value]
  =[.findPath]       StValue.find (.copyMem (memWrite r value 99) (.idC r [])) [value]
  =[.findCopyMem]    MemValue.ofView (memWrite r value 99)
                       (Memory.readR (memWrite r value 99) (.idC r []) [value])
  =[.readRSingleton] MemValue.ofView (memWrite r value 99)
                       (Memory.readIn (memWrite r value 99) (.idC r []) value)
  =[.readWriteEqual] StValue.prim (PrimVal.int 99)

end Solidity.Examples.Paper.Theory
