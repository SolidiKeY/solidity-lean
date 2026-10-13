import Solidity.Theory.Rewrite
import Solidity.Theory.Typed.Obs
import Solidity.Syntax

/-!
# The lines after the program: rewriting by the theories

A worked example does not end when the last statement is
consumed.  The calculus leaves an update whose right-hand sides are still
terms — `find(storage, …)`, `read(memory, …)`, `copySt`, `copyMem` — and the
derivation keeps rewriting them by the theories' rules until the value is there:

```
⇝  {mem := M₁, storage := S₁, v := findSt(store(storage, alice, copyMem(∅, M₁, carol)), alice·age)}
⇝  {mem := M₁, storage := S₁, v := readR(write(mem, carol, age, 42), carol, ⟨age⟩)}
⇝  {mem := M₁, storage := S₁, v := 42}
```

Those lines are not steps of the calculus: no taclet fires, an equation
between terms is applied.  Here each chain is a `calc` over the free-term
algebras of `Theory/Terms.lean`, one line per rule, and the comment at the end
of a line is the rule's name in the signature — a `TheoryRule`
(`Theory/Rewrite.lean`), whose `lemmaNames` is the theorem the line cites.
The calculus side of each example — the program run into those terms and read
back — is `StorageSteps.lean`, `Memory.lean` and `CrossDomain.lean`; the name
of each chain here says which one it continues.

The storage fields and `delete` (sections 1 and 3) are read in the typed
Theory, where an equation of the calculus is read (`Theory/Typed/Obs.lean`):
a storage is its observations at typed locations, a law is stated once by its
solkey name (`Obs.findOnSave`, …), and a delete is read off the type, with
no premise about what the deleted node is.  The push/pop argument (section
2) and the memory and cross-domain lines (5–8) stay in the untyped algebra of
`Theory/Terms.lean`, the memory island's (`Calculus/MemTheory.lean`): there
`size` is a member written like any other, and the paths are `List Seg`, so
`alice·account·balance` is `[alice, account, balance]` and its `⟨f⟩` is `[f]`.

A root that the calculus invents is a variable `r`, not a numeral: the
`new(mem, r) →` premise says only that it is fresh, and a chain that picked
`7` would prove less.
-/

namespace Solidity.Examples.Tactics.Theory

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

/-! ## The two abbreviations

`M₁` and `S₁` are the names for the memory and storage terms a chain
has accumulated by the time the program is gone
in the memory-to-storage examples. -/

/-- `M₁ = write(mem, idC(r, ∅), a, v)` — one memory write to a fresh root. -/
private abbrev memWrite (r : IdentityPrim) (a : Seg) (v : Int) : Memory :=
  .write .mtMem (.idC r []) a (.prim (.int v))

/-- `S₁ = save(∅, p, v)` — one storage write. -/
private abbrev stSave (p : List Seg) (v : Int) : Struct :=
  save Struct.mtSt p (StValue.int v)

/-! ## 1 · Storage fields, in the typed Theory

A storage is its observations at typed locations (`TSto`,
`Theory/Typed/Obs.lean`): `alice.account.balance` is a location of
`StandardExample` holding a `uint`, and a write is a copy laid there
(`Obs.copyTo`).  The laws are solkey's, by name. -/

section Typed

/-- `alice`, `bob`, and the paths the examples read below a `Person`. -/
private abbrev aliceL : SLoc StandardExample (.ref (.struct "Person")) :=
  .ref (SRef.ofRoot "alice" rfl)
private abbrev bobL : SLoc StandardExample (.ref (.struct "Person")) :=
  .ref (SRef.ofRoot "bob" rfl)
private abbrev accountBalance : Path (.ref (.struct "Person")) .uint :=
  .field (f := "account") rfl (.field (s := "Account") (f := "balance") rfl .nil)
private abbrev accountTokenValue : Path (.ref (.struct "Person")) .uint :=
  .field (f := "account") rfl (.field (s := "Account") (f := "token") rfl
    (.field (s := "Token") (f := "value") rfl .nil))
private abbrev ageP : Path (.ref (.struct "Person")) .uint := .field (f := "age") rfl .nil
private abbrev accountP : Path (.ref (.struct "Person")) (.ref (.struct "Account")) :=
  .field (f := "account") rfl .nil

/-- A `uint` word as written. -/
private abbrev word (n : Int) (h : PrimTy.uint.inRange n = true := by rfl) : PrimTy.uint.Denote :=
  ⟨n, h⟩

/-- `alice.account.balance = 10; v = alice.account.balance;` — reading exactly
the written location (`findOnSave`). -/
theorem deepFieldWriteValue (s : TSto StandardExample) :
    (s.copyTo (ObsLoc.app aliceL accountBalance) (TVal.ofWord (word 10))).word
      (ObsLoc.app aliceL accountBalance) = word 10 :=
  Obs.findOnSave _ _ _

/-- **The frame.**  `bob.age` does not see the write: the locations part at
the root (`findOnSaveDifferent`, decided on the two literal locations). -/
theorem deepFieldWriteFrame (s : TSto StandardExample) :
    (s.copyTo (ObsLoc.app aliceL accountBalance) (TVal.ofWord (word 10))).word
      (ObsLoc.app bobL ageP) = s.word (ObsLoc.app bobL ageP) :=
  Obs.findOnSaveFrame _ _ (by decide +kernel)

/-- **Reading above the write.**  `alice` reads the write made below it
(`findOnSavePrefix`) — the step the calculus takes when an alias was captured
above the target. -/
theorem deepFieldWritePrefix (s : TSto StandardExample) (v : TVal .uint) :
    (s.copyTo (ObsLoc.app aliceL accountBalance) v).find aliceL =
      (s.find aliceL).copyTo accountBalance v :=
  Obs.findOnSavePrefix _ _ _ _

end Typed

/-! ## 2 · Storage arrays: the push/pop argument

The storage examples write this one entirely in the theory:
"Let S₁ = …", three `save`s, and then the read off them — the slot written
before the `pop()` is read through the `push()` that follows. -/

/-- `S₁ = save(delAt(∅, tokens[0]), tokens.length, 0)`, after the `pop()`. -/
private abbrev S1 : Struct :=
  save (delAt Struct.mtSt [tokens, .at 0]) [tokens, len] (StValue.int 0)
/-- `S₂ = save(S₁, tokens[0].value, 7)`. -/
private abbrev S2 : Struct := save S1 [tokens, .at 0, value] (StValue.int 7)
/-- `S₃ = save(S₂, tokens.length, 1)`, the `push()`. -/
private abbrev S3 : Struct := save S2 [tokens, len] (StValue.int 1)

/-- "The subsequent field read sees `findSt(S₃, tokens[0].value) = 7`." -/
theorem pushPopSlotValue : findSt S3 [tokens, .at 0, value] = StValue.int 7 :=
  calc findSt S3 [tokens, .at 0, value]
    _ = findSt S2 [tokens, .at 0, value] := find_save_frame _ _ _ _ (by decide)
                                                                   -- findOnSaveDifferent
    _ = StValue.int 7 := find_save_same _ (by simp) _              -- findOnSave

/-! ## 3 · `delete`, in the typed Theory

A delete resets what is below its location, read off the type
(`TVal.delR`): a word to its default, a struct member by member, a mapping's
entries and an array's slots past its end kept.  So the storage `delete`
trace needs no premise about what the deleted account is: its type says. -/

section TypedDelete

/-- `delete alice.age;` of a word: its default (`findOnDelAt`). -/
theorem deleteLeafDefault (s : TSto StandardExample) :
    (s.delAt (ObsLoc.app aliceL ageP)).word (ObsLoc.app aliceL ageP) = word 0 :=
  Obs.findOnDelAt _ _

/-- `S₁` of the storage `delete` example:
`alice.account.balance = 100; alice.account.token.value = 7;`. -/
private abbrev S1Del (s : TSto StandardExample) : TSto StandardExample :=
  (s.copyTo (ObsLoc.app aliceL accountBalance) (TVal.ofWord (word 100))).copyTo
    (ObsLoc.app aliceL accountTokenValue) (TVal.ofWord (word 7))

/-- `delete alice.account; b = alice.account.balance;` — the balance is below
the deleted account, a struct, and reads its default. -/
theorem deleteSubtreeBalance (s : TSto StandardExample) :
    ((S1Del s).delAt (ObsLoc.app aliceL accountP)).word (ObsLoc.app aliceL accountBalance) =
      word 0 := by
  rw [show ObsLoc.app aliceL accountBalance = ObsLoc.app (ObsLoc.app aliceL accountP)
      (.field (s := "Account") (f := "balance") rfl .nil) by
    rw [ObsLoc.app_app, Path.append_field, Path.append_nil],
    Obs.delAt_word_below]
  rfl

/-- `v = alice.account.token.value;` — two members below the deleted account:
the token is a struct too, and its value reads its default. -/
theorem deleteSubtreeTokenValue (s : TSto StandardExample) :
    ((S1Del s).delAt (ObsLoc.app aliceL accountP)).word (ObsLoc.app aliceL accountTokenValue) =
      word 0 := by
  rw [show ObsLoc.app aliceL accountTokenValue = ObsLoc.app (ObsLoc.app aliceL accountP)
      (.field (s := "Account") (f := "token") rfl (.field (s := "Token") (f := "value") rfl .nil)) by
    rw [ObsLoc.app_app, Path.append_field, Path.append_nil],
    Obs.delAt_word_below]
  rfl

end TypedDelete

/-! ## 5–7 · Memory

The last line of the aliasing example (`Memory.memoryAliasWrite`) is
pure term rewriting: the member of a freshly added root reads as `dflt`, and
the cast at the `Identity` sort turns that into the identity one field further
down.  That is how a reference member exists as soon as its parent does,
without anything being allocated for it. -/

/-- `Person memory carol; Account memory carolAcc = carol.account;` — the
identity `carolAcc` is bound to.  `r` is the root the calculus invents. -/
theorem memoryAliasIdentity (r : IdentityPrim) (ty : RefTy) :
    MemValue.asIdentity (Memory.readIn (.addM .mtMem r ty) (.idC r []) account) (.idC r []) account =
      Identity.idC r ([] ++ [account]) :=
  calc MemValue.asIdentity (Memory.readIn (.addM .mtMem r ty) (.idC r []) account) (.idC r []) account
    _ = MemValue.asIdentity .dflt (.idC r []) account := by
        rw [Memory.readAddEqual]                                   -- readAddEqual
    _ = Identity.idC r ([] ++ [account]) := Memory.initIdentity _ _ _  -- initIdentity

/-- The read-over-write the memory examples end on
(`Memory.memoryDeclFreshAlloc`: `carol.age = 34; x = carol.age;`). -/
theorem memoryFieldValue (r : IdentityPrim) :
    Memory.readR (memWrite r age 34) (.idC r []) [age] = MemValue.prim (PrimVal.int 34) :=
  calc Memory.readR (memWrite r age 34) (.idC r []) [age]
    _ = Memory.readIn (memWrite r age 34) (.idC r []) age := Memory.readREmpty _ _ _  -- readRSingleton
    _ = MemValue.prim (PrimVal.int 34) := by rw [Memory.readOnWrite]; simp  -- readWriteEqual

/-! ## 8 · Cross-domain copies

`copySt` and `copyMem` are the two lazy views (`Theory/CrossDomain.lean`).
Each chain starts where its calculus twin in `CrossDomain.lean` leaves the
read. -/

/-- `alice.age = 34; Person memory carol = alice; v = carol.age;` — the tail
of `CrossDomain.storageToMemoryRootCopy`.  The storage-to-memory example:
"the sixth step is `readCopySt`; the seventh is read-over-write on the
resulting `find`". -/
theorem storageToMemoryRootCopyValue (r : IdentityPrim) :
    Memory.readIn (.copySt .mtMem r (stSave [alice, age] 34)) (.idC r [alice]) age =
      MemValue.prim (PrimVal.int 34) :=
  calc Memory.readIn (.copySt .mtMem r (stSave [alice, age] 34)) (.idC r [alice]) age
    _ = StValue.toMemValue (find (stSave [alice, age] 34) ([alice] ++ [age])) :=
        Memory.readCopySt _ _ _ _ _                                      -- readCopySt
    _ = StValue.toMemValue (StValue.int 34) := rfl                      -- findOnSave
    _ = MemValue.prim (PrimVal.int 34) := rfl

/-- …and the same read below *another* root does not see the copy at all: the
frame of the storage-to-memory view. -/
theorem storageToMemoryOtherRoot (r1 r2 : IdentityPrim) (m : Memory) (s : Struct)
    (hne : r1 ≠ r2) :
    Memory.readIn (.copySt m r1 s) (.idC r2 [alice]) age = Memory.readIn m (.idC r2 [alice]) age :=
  calc Memory.readIn (.copySt m r1 s) (.idC r2 [alice]) age
    _ = Memory.readIn m (.idC r2 [alice]) age := Memory.readCopyStOther _ _ _ _ _ _ hne
                                                                   -- readCopyStOther

/-- `carol.age = 34; alice = carol; v = alice.age;` — the tail of
`CrossDomain.memoryToStorageRootCopy`, and the three lines spent on
it, at the sort `v` has.  The decisive one is `findCopyMem`: a storage read
becomes a memory read without either theory having walked anything. -/
theorem memoryToStorageRootCopyValue (r : IdentityPrim) :
    asInt (StValue.find (.storeSt Struct.mtSt alice (.st (.copyMem (memWrite r age 34) (.idC r []))))
      [alice, age]) = 34 :=
  calc asInt (StValue.find (.storeSt Struct.mtSt alice (.st (.copyMem (memWrite r age 34) (.idC r []))))
        [alice, age])
    _ = asInt (StValue.find (.copyMem (memWrite r age 34) (.idC r [])) [age]) := rfl  -- findPath
    _ = (Memory.readR (memWrite r age 34) (.idC r []) [age]).asInt :=
        findCopyMem _ _ _                                                   -- findCopyMem
    _ = (Memory.readIn (memWrite r age 34) (.idC r []) age).asInt := rfl  -- readRSingleton
    _ = 34 := by rw [Memory.readOnWrite]; simp [MemValue.asInt]            -- readWriteEqual

/-- `acc.balance = 10; alice.account = acc; v = alice.account.balance;` — the
tail of `CrossDomain.memoryToStorageFromAlias`: the view one selector deeper,
so the storage half of the read is two segments and the memory half one.
(`CrossDomain.memoryToStorageFromMemberSource` ends on the same pair of
rules, with the member `carol.account` where this has the local.) -/
theorem memoryToStorageFromAliasValue (r : IdentityPrim) :
    asInt (StValue.find (.storeSt Struct.mtSt alice
        (.st (.storeSt Struct.mtSt account (.st (.copyMem (memWrite r balance 10) (.idC r []))))))
      [alice, account, balance]) = 10 :=
  calc asInt (StValue.find (.storeSt Struct.mtSt alice
          (.st (.storeSt Struct.mtSt account (.st (.copyMem (memWrite r balance 10) (.idC r []))))))
        [alice, account, balance])
    _ = asInt (StValue.find (.storeSt Struct.mtSt account
          (.st (.copyMem (memWrite r balance 10) (.idC r [])))) [account, balance]) := rfl
                                                                            -- findPath
    _ = asInt (StValue.find (.copyMem (memWrite r balance 10) (.idC r [])) [balance]) := rfl
                                                                            -- findPath
    _ = (Memory.readR (memWrite r balance 10) (.idC r []) [balance]).asInt :=
        findCopyMem _ _ _                                                   -- findCopyMem
    _ = (Memory.readIn (memWrite r balance 10) (.idC r []) balance).asInt := rfl  -- readRSingleton
    _ = 10 := by rw [Memory.readOnWrite]; simp [MemValue.asInt]                -- readWriteEqual

/-- `t.value = 99; alice.account.token = t; v = alice.account.token.value;` —
the tail of `CrossDomain.memoryToStorageNonsimplePath`, where the *target* is
the nonsimple path: three storage selectors above the view. -/
theorem memoryToStorageNonsimplePathValue (r : IdentityPrim) :
    asInt (StValue.find (.storeSt Struct.mtSt alice
        (.st (.storeSt Struct.mtSt account
          (.st (.storeSt Struct.mtSt token (.st (.copyMem (memWrite r value 99) (.idC r []))))))))
      [alice, account, token, value]) = 99 :=
  calc asInt (StValue.find (.storeSt Struct.mtSt alice
          (.st (.storeSt Struct.mtSt account
            (.st (.storeSt Struct.mtSt token (.st (.copyMem (memWrite r value 99) (.idC r []))))))))
        [alice, account, token, value])
    _ = asInt (StValue.find (.copyMem (memWrite r value 99) (.idC r [])) [value]) := rfl
                                                                  -- findPath, three times
    _ = (Memory.readR (memWrite r value 99) (.idC r []) [value]).asInt :=
        findCopyMem _ _ _                                                   -- findCopyMem
    _ = (Memory.readIn (memWrite r value 99) (.idC r []) value).asInt := rfl   -- readRSingleton
    _ = 99 := by rw [Memory.readOnWrite]; simp [MemValue.asInt]                -- readWriteEqual

/-- A struct read *out of* a view — `bob.account = alice.account;` after
`alice = carol;` from memory, where `carol.account` was never assigned: memory
created it implicitly (`initIdentity`), and a write below it
(`carol.account.balance = 5`) is still there to be read.  The storage copy of
the member is the view one field down (`selectOnCopyMemRef`), and reading
through that one reaches the write. -/
theorem memoryToStorageMemberView (r : IdentityPrim) (ty : RefTy) :
    let M := Memory.write (.addM .mtMem r ty) (.idC r [account]) balance (.prim (PrimVal.int 5))
    asInt (StValue.find
        (asStruct (StValue.find (.storeSt Struct.mtSt alice (.st (.copyMem M (.idC r [])))) [alice, account]))
        [balance]) = 5 := by
  intro M
  calc asInt (StValue.find
          (asStruct (StValue.find (.storeSt Struct.mtSt alice (.st (.copyMem M (.idC r [])))) [alice, account]))
          [balance])
    _ = asInt (StValue.find (Struct.copyMem M (Memory.readId M (.idC r []) account)) [balance]) := by
        rw [show StValue.find (.storeSt Struct.mtSt alice (.st (.copyMem M (.idC r [])))) [alice, account]
              = StValue.find (.copyMem M (.idC r [])) [account] from rfl,       -- findPath
            selectOnCopyMemRef _ _ _ (by simp [M])]                           -- selectOnCopyMemRef
    _ = asInt (StValue.find (Struct.copyMem M (.idC r [account])) [balance]) := by
        simp [M, Memory.readId]                                  -- readAddEqual, initIdentity
    _ = (Memory.readIn M (.idC r [account]) balance).asInt := findCopyMem _ _ [balance]
                                                                  -- findCopyMem, readRSingleton
    _ = 5 := by simp [M, MemValue.asInt]                          -- readWriteEqual

end Solidity.Examples.Tactics.Theory
