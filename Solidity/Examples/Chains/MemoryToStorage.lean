import Solidity.Calculus.Chains
import Solidity.FreshNames

/-!
# Memory-to-storage copies, as chains

The calculus's four worked examples of a copy from a memory object into
storage, each a `calc` for every modality `m` and postcondition `φ`
(`Calculus/Chains.lean`: `~[r]~>` is a printed `⇝` naming its rule).  A
chain starts under the update the declaration of the memory object leaves,
`{ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }`,
where the printed trace starts from an object it does not declare.  A read
of the copied storage is unfolded through aliases (`sp`, …), one rule per
selector, where the printed trace reads the path at once.

Not drawn: the lines after the program, where the printed trace merges the
memory write with the storage copy and reads it back (`findCopyMem`,
`readRSingleton`, `readWriteEqual`).  `sequentialToParallel` does not merge
an update that writes memory, and those laws are no chain rewrites yet.
-/

namespace Solidity.Examples.Chains.MemoryToStorage

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Symbolic Execution of Memory-to-Storage Copy with Lazy Read -/

namespace RootCopy

variable (m : Modality) (φ : Post StandardExample)

/-- `carol.age = 42; alice = carol; v = alice.age;` — a memory object copied
into a storage root (`copyMem`), and read back from storage. -/
def chain :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.age = 42; alice = carol; v = alice.age; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) }
                { storage := store(storage, alice, copyMem(mtSt, memory, carol)) }
                { v := find(storage, alice.age) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.age = 42; alice = carol; v = alice.age; ]⟩ φ }
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) } ⟨[ alice = carol; v = alice.age; ]⟩ φ } := rfl
    _ ~[memoryToStorageStoreRoot]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) }
                { storage := store(storage, alice, copyMem(mtSt, memory, carol)) }
                ⟨[ v = alice.age; ]⟩ φ } := rfl
    _ ~[storageFieldReadFind]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) }
                { storage := store(storage, alice, copyMem(mtSt, memory, carol)) }
                { v := find(storage, alice.age) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) }
                { storage := store(storage, alice, copyMem(mtSt, memory, carol)) }
                { v := find(storage, alice.age) } φ } := rfl

end RootCopy

/-! ## Example: Symbolic Execution of Memory-to-Storage Field Copy with Lazy Read -/

namespace FieldCopy

/-- The printed name of the storage alias the read unfolds through. -/
def names : FreshTable := [("acc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

/-- `carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance;`
— into a member of a storage root. -/
def chain :
    dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            ⟨[ carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance; ]⟩ φ }
    ~*> dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) }
                { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
                { acc := alice.account } { v := find(storage, acc.balance) } φ } :=
  calc dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
               ⟨[ carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance; ]⟩ φ }
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) }
                ⟨[ alice.account = carolAcc; v = alice.account.balance; ]⟩ φ } := rfl
    _ ~[memoryToStorageFieldCopyRoot]~>
        dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) }
                { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
                ⟨[ v = alice.account.balance; ]⟩ φ } := rfl
    _ ~[storageFieldRead_unfold_rightFst]~>
        dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) }
                { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
                ⟨[ Account storage acc = alice.account; v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                  { memory := write(memory, carolAcc.balance, 50) }
                  { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
                  { acc := alice.account } { v := find(storage, acc.balance) } φ } := by sol_chain

end FieldCopy

/-! ## Example: Symbolic Execution of Memory-to-Storage Copy with Nonsimple RHS and Lazy Read -/

namespace PathCopy

/-- The printed name of the memory alias of the source's member `carolAcc`;
`sp` is the storage alias the read unfolds through. -/
def names : FreshTable := [("carolAcc", "mv1"), ("sp", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

/-- `carol.account.balance = 50; alice.account = carol.account;
v = alice.account.balance;` — the source a member of a memory object: its
identity is read from memory, and what is copied. -/
def chain :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.account.balance = 50; alice.account = carol.account; v = alice.account.balance; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) } { memory := write(memory, carolAcc.balance, 50) }
                { storage := save(storage, alice.account, copyMem(mtSt, memory, read(memory, carol.account))) }
                { sp := alice.account } { v := find(storage, sp.balance) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.account.balance = 50; alice.account = carol.account;
                  v = alice.account.balance; ]⟩ φ }
    _ ~[memoryFieldWrite_unfold_leftFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory carolAcc = carol.account; carolAcc.balance = 50;
                   alice.account = carol.account; v = alice.account.balance; ]⟩ φ } := by sol_chain
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ carolAcc = carol.account; carolAcc.balance = 50;
                   alice.account = carol.account; v = alice.account.balance; ]⟩ φ where Account memory carolAcc } := rfl
    _ ~[memoryFieldReadAliasRoot]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                ⟨[ carolAcc.balance = 50; alice.account = carol.account; v = alice.account.balance; ]⟩ φ } := rfl
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) } { memory := write(memory, carolAcc.balance, 50) }
                ⟨[ alice.account = carol.account; v = alice.account.balance; ]⟩ φ } := rfl
    _ ~[memoryToStorageFieldCopyRoot]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) } { memory := write(memory, carolAcc.balance, 50) }
                { storage := save(storage, alice.account,
                    copyMem(mtSt, memory, read(memory, carol.account))) }
                ⟨[ v = alice.account.balance; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { carolAcc := read(memory, carol.account) } { memory := write(memory, carolAcc.balance, 50) }
                  { storage := save(storage, alice.account,
                      copyMem(mtSt, memory, read(memory, carol.account))) }
                  { sp := alice.account } { v := find(storage, sp.balance) } φ } := by sol_chain

end PathCopy

/-! ## Example: Symbolic Execution of Memory-to-Storage Nonsimple Path Copy -/

namespace NonsimplePath

/-- The printed names: `aliceAcc` is the alias of the target's prefix; the
read unfolds through `aliceTok` and `sp`. -/
def names : FreshTable := [("aliceAcc", "sp1"), ("aliceTok", "sp2"), ("sp", "sp3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

/-- `carolToken.value = 99; alice.account.token = carolToken;` — the target is
the nonsimple path: its prefix is aliased (`memoryToStorageField_unfold_leftFst`)
and the copy goes into the alias.  The memory source `carolToken` is already
a local, so there is no `tok` alias. -/
def copy :
    dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
            ⟨[ carolToken.value = 99; alice.account.token = carolToken;
               v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                ⟨[ v = alice.account.token.value; ]⟩ φ } :=
  calc dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
               ⟨[ carolToken.value = 99; alice.account.token = carolToken;
                  v = alice.account.token.value; ]⟩ φ }
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                ⟨[ alice.account.token = carolToken; v = alice.account.token.value; ]⟩ φ } := rfl
    _ ~[memoryToStorageField_unfold_leftFst]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                ⟨[ Account storage aliceAcc = alice.account; aliceAcc.token = carolToken;
                   v = alice.account.token.value; ]⟩ φ } := by sol_chain
    _ ~[storageLocalDeclInitDrop]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                ⟨[ aliceAcc = alice.account; aliceAcc.token = carolToken;
                   v = alice.account.token.value; ]⟩ φ } := rfl
    _ ~[storageFieldReadBindLocalRoot]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                ⟨[ aliceAcc.token = carolToken; v = alice.account.token.value; ]⟩ φ } := rfl
    _ ~[memoryToStorageFieldCopyRoot]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                ⟨[ v = alice.account.token.value; ]⟩ φ } := rfl

/-- … and `v = alice.account.token.value;` read through two more aliases, one
per selector. -/
def read :
    dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
            { memory := write(memory, carolToken.value, 99) }
            { aliceAcc := alice.account }
            { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
            ⟨[ v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                { sp := alice.account } { aliceTok := sp.token } { v := find(storage, aliceTok.value) } φ } :=
  calc dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
               { memory := write(memory, carolToken.value, 99) }
               { aliceAcc := alice.account }
               { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
               ⟨[ v = alice.account.token.value; ]⟩ φ }
    _ ~*> dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                  { memory := write(memory, carolToken.value, 99) }
                  { aliceAcc := alice.account }
                  { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                  { sp := alice.account } { aliceTok := sp.token } ⟨[ v = aliceTok.value; ]⟩ φ } := by
      sol_chain
    _ ~[storageFieldReadFind]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                { sp := alice.account } { aliceTok := sp.token } { v := find(storage, aliceTok.value) }
                ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                { sp := alice.account } { aliceTok := sp.token } { v := find(storage, aliceTok.value) } φ } := rfl

/-- `carolToken.value = 99; alice.account.token = carolToken;
v = alice.account.token.value;` — the copy, then the read. -/
def chain :
    dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
            ⟨[ carolToken.value = 99; alice.account.token = carolToken;
               v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                { sp := alice.account } { aliceTok := sp.token } { v := find(storage, aliceTok.value) } φ } :=
  (copy m φ).trans (read m φ)

end NonsimplePath

end Solidity.Examples.Chains.MemoryToStorage
