import Solidity.Theory.Typed.Obs
import Solidity.Theory.Typed.Mem
import Solidity.Syntax

/-!
# The lines after the program: rewriting by the theories

A worked example does not end when the last statement is consumed.  The
calculus leaves an update whose right-hand sides are still terms —
`find(storage, …)`, `read(memory, …)`, `copySt`, `copyMem` — and the
derivation keeps rewriting them by the theories' rules until the value is
there.  Those lines are not steps of the calculus: no taclet fires, an
equation between terms is applied.  Here each is a law of the typed Theory
cited by its solkey name, on the example's own locations; the calculus side
of each example — the program run into those terms and read back — is
`StorageSteps.lean`, `Memory.lean` and `CrossDomain.lean`.

Storage (sections 1–3) is read in `Theory/Typed/Obs.lean`: a storage is its
observations at typed locations, a law is stated once by its solkey name
(`Obs.findOnSave`, …), and a delete is read off the type, with no premise
about what the deleted node is.  Memory and the copies between the two
(sections 5–8) are read in `Theory/Typed/Mem.lean`, on the typed heap.
-/

namespace Solidity.Examples.Tactics.Theory

open Semantics (lookupBy structDef)

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
the root (`findOnSaveFrame`, solkey's `selectOnSaveCons` `\else`, decided
on the two literal locations). -/
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

/-! ## 2 · Storage arrays: a push and a pop leave the rest

A push and a pop write the array's length and its last slot, and nothing
apart from the array (`findOnPushFrame`, `findOnPopFrame`): `alice.age`,
written before them, reads through both. -/

section TypedArrays

/-- `values`, a `uint[]`. -/
private abbrev valuesL : SLoc StandardExample (.ref (.array (.prim .uint))) :=
  .ref (SRef.ofRoot "values" rfl)

/-- `alice.age = 34; values.push(7); values.pop(); v = alice.age;`. -/
theorem pushPopFrame (s : TSto StandardExample) :
    ((((s.copyTo (ObsLoc.app aliceL ageP) (TVal.ofWord (word 34))).push valuesL
        (TVal.ofWord (word 7))).pop false valuesL).word (ObsLoc.app aliceL ageP)) = word 34 := by
  rw [Obs.findOnPopFrame _ _ (by decide +kernel), Obs.findOnPushFrame _ _ (by decide +kernel),
    Obs.findOnSave]
  rfl

end TypedArrays

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

/-! ## 5–7 · Memory, on the typed heap

A memory is a heap grown from the global part's (`Grown H`), an address an
identity with a member or an element (`MAddrT T`), and a read gives a word
or an identity (`Grown.readId`).  The laws are solkey's, by name
(`Theory/Typed/Mem.lean`).  An identity the calculus invents is a variable,
not a numeral: a chain that picked `7` would prove less. -/

section Memory

/-- `Person`'s member `age`. -/
private abbrev hAge : lookupBy "age" (structDef "Person") = some (.prim .uint) := rfl

/-- `carol.age`, for the `Person` at identity `carol`. -/
private abbrev ageAt (carol : Nat) : MAddrT (.prim .uint) := .field (s := "Person") carol hAge

/-- `carol.age = 34; x = carol.age;` — the read-over-write the memory
examples end on (solkey's `readOnWrite` `\then`). -/
theorem memoryFieldValue {H : HTy} {m m' : Grown H (fun _ => Unit)} (carol : Nat)
    (h : m.writeT (ageAt carol) (word 34) = some m') : m'.readId (ageAt carol) = some (word 34) :=
  Grown.readOnWrite h

/-- …and the same member of another object does not see it
(`readOnWrite` `\else`). -/
theorem memoryFieldFrame {H : HTy} {m m' : Grown H (fun _ => Unit)} (carol bob : Nat)
    (hne : ¬ carol = bob) (h : m.writeT (ageAt carol) (word 34) = some m') :
    m'.readId (ageAt bob) = m.readId (ageAt bob) :=
  Grown.readOnWriteFrame h _ (.inl hne)

/-- `Person memory carol; x = carol.age;` — a member of a fresh struct reads
its default (`readOnAddM` `\then`, then `initMember`). -/
theorem memoryDeclDefault {H : HTy} (hp : Heap H) :
    (hp.allocDefault (.struct "Person") rfl).heap.field
      (hp.allocDefault (.struct "Person") rfl).val hAge = word 0 :=
  (Heap.initMember hp rfl hAge).trans rfl

end Memory

/-! ## 8 · Cross-domain copies

A copy from storage into memory allocates fresh objects holding what the
storage held; a copy from memory into storage is a storage value holding
what the objects held.  Each is read back by solkey's law. -/

section CrossDomain

/-- `Person memory carol = alice; v = carol.age;` — the tail of
`CrossDomain.storageToMemoryRootCopy` (`readFromCopyToStorage` `\then`):
the copy's member
reads the storage struct's. -/
theorem storageToMemoryRootCopyValue {H : HTy} (hp : Heap H)
    (alice : SVal (.ref (.struct "Person"))) :
    (alice.copyStToM hp rfl).heap.field (alice.copyStToM hp rfl).val hAge =
      (((SVal.view alice : SFields _).get hAge).view : PrimTy.uint.Denote) :=
  SVal.readFromCopyToStorage hp alice rfl hAge

/-- …and an object older than the copy does not see it
(`readFromCopyToStorage` `\else`). -/
theorem storageToMemoryOtherRoot {H : HTy} (μ₀ : Grown H (fun _ => Unit))
    (alice : SVal (.ref (.struct "Person"))) (bob : Nat) (hid : bob < μ₀.H'.length) :
    (μ₀.then (alice.copyStToM μ₀.heap rfl)).readId (ageAt bob) = μ₀.readId (ageAt bob) :=
  Grown.readFromCopyToStorageFrame μ₀ alice rfl (ageAt bob) hid

/-- `alice = carol; v = alice.age;` — the tail of
`CrossDomain.memoryToStorageRootCopy` (`findOnCopy`): the storage copy's
member holds the object's. -/
theorem memoryToStorageRootCopyValue {H : HTy} (hp : Heap H) (carol : HRef H (.struct "Person")) :
    (MVal.copyMToSt hp (T := .ref (.struct "Person")) carol).find (.field hAge .nil) =
      some (.prim (hp.field carol hAge)) :=
  MVal.findOnCopy hp carol hAge

end CrossDomain

end Solidity.Examples.Tactics.Theory
