import Solidity.Calculus.LastLine
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

After the program the updates merge into one — the memory write
substituted for `memory` in the storage write, as the printed `S₁` reads
`copyMem(mtSt, M₁, carol)` — and the read is resolved by the laws of memory
reads (`EvalLaw`, `Calculus/ChainRewrites.lean`): `findCopyMem` sends the
`find` back into memory, `readOnWrite` reads the write.  A line that binds
an alias through another alias is crossed unwritten, the next written line
being its merge.  Each chain then merges the declaration's update into the
rest and drops the dead aliases (`~[simplifyUpdate]~>`); the identity-level
step of the member-source example (`i_rhs` and `i_acc` one identity) is
`readWriteDifferentIdentity`, the law at identity sort.
-/

namespace Solidity.Examples.Chains.MemoryToStorage

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Symbolic Execution of Memory-to-Storage Copy with Lazy Read -/

namespace RootCopy

variable (m : Modality) (φ : Post StandardExample)

set_option maxHeartbeats 4000000 in
/-- `carol.age = 42; alice = carol; v = alice.age;` — a memory object copied
into a storage root (`copyMem`), and read back from storage: the updates
merged, the read sent back into memory (`findCopyMem`), the write read
(`readOnWrite`). -/
theorem chain :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.age = 42; alice = carol; v = alice.age; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖
          memory := write(addM(memory, Person), freshId(addM(memory, Person)).age, 42) ‖
          storage :=
            store(storage, alice,
              copyMem(mtSt, write(addM(memory, Person), freshId(addM(memory, Person)).age, 42),
                freshId(addM(memory, Person)))) ‖
          v := 42 } φ } :=
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
    _ ~[sequentialToParallel]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) ‖
                  storage := store(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)) ‖
                  v := find(store(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)),
                            alice.age) } φ } := by sol_chain
    _ ~[findCopyMem]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) ‖
                  storage := store(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)) ‖
                  v := read(write(memory, carol.age, 42), carol.age) } φ } := by sol_chain
    _ ~[readOnWrite]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.age, 42) ‖
                  storage := store(storage, alice, copyMem(mtSt, write(memory, carol.age, 42), carol)) ‖
                  v := 42 } φ } := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain

#last_line chain

end RootCopy

/-! ## Example: Symbolic Execution of Memory-to-Storage Field Copy with Lazy Read -/

namespace FieldCopy

/-- The printed name of the storage alias the read unfolds through. -/
def names : FreshTable := [("acc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

set_option maxHeartbeats 4000000 in
/-- `carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance;`
— into a member of a storage root, read back through the alias `acc`: the
updates merged, the read sent back into memory, the write read. -/
theorem chain :
    dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            ⟨[ carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance; ]⟩ φ }
    ~~> dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖
          memory := write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50) ‖
          storage :=
            save(storage, alice.account,
              copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                freshId(addM(memory, Account)))) ‖
          v := 50 } φ } :=
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
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) ‖
                  storage := save(storage, alice.account,
                    copyMem(mtSt, write(memory, carolAcc.balance, 50), carolAcc)) ‖
                  acc := alice.account ‖
                  v := find(save(storage, alice.account,
                              copyMem(mtSt, write(memory, carolAcc.balance, 50), carolAcc)),
                            alice.account.balance) } φ } := by sol_chain
    _ ~[findCopyMem]~>
        dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) ‖
                  storage := save(storage, alice.account,
                    copyMem(mtSt, write(memory, carolAcc.balance, 50), carolAcc)) ‖
                  acc := alice.account ‖
                  v := read(write(memory, carolAcc.balance, 50), carolAcc.balance) } φ } := by sol_chain
    _ ~[readOnWrite]~>
        dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) ‖
                  storage := save(storage, alice.account,
                    copyMem(mtSt, write(memory, carolAcc.balance, 50), carolAcc)) ‖
                  acc := alice.account ‖ v := 50 } φ } := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[simplifyUpdate]~> _ := by sol_chain

#last_line chain

end FieldCopy

/-! ## Example: Symbolic Execution of Memory-to-Storage Copy with Nonsimple RHS and Lazy Read -/

namespace PathCopy

/-- The printed name of the memory alias of the source's member `carolAcc`;
`sp` is the storage alias the read unfolds through. -/
def names : FreshTable := [("carolAcc", "mv1"), ("sp", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

set_option maxHeartbeats 4000000 in
/-- `carol.account.balance = 50; alice.account = carol.account;
v = alice.account.balance;` — the source a member of a memory object: its
identity is read from memory, and what is copied.  The updates merge and
`findCopyMem` sends the read back into memory, at the identity the copy read
after the write, `read(write(memory, read(memory, carol.account).balance, 50), carol.account)`.
The printed trace reads the write through it as `50` because that identity
is the one written, `read(memory, carol.account)` — the write at `balance`
does not touch `account` — a frame law at the `Identity` sort, which no
term rewrite applies: a rewrite replaces value terms (`Tm.rw`). -/
theorem chain :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.account.balance = 50; alice.account = carol.account; v = alice.account.balance; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖
          carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
          memory :=
            write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50) ‖
          storage :=
            save(storage, alice.account,
              copyMem(mtSt,
                write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                read(addM(memory, Person), freshId(addM(memory, Person)).account))) ‖
          v := 50 } φ } :=
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
    _ ~[sequentialToParallel]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) ‖
                  memory := write(memory, read(memory, carol.account).balance, 50) ‖
                  storage := save(storage, alice.account,
                    copyMem(mtSt, write(memory, read(memory, carol.account).balance, 50),
                      read(write(memory, read(memory, carol.account).balance, 50), carol.account))) ‖
                  sp := alice.account ‖
                  v := find(save(storage, alice.account,
                              copyMem(mtSt, write(memory, read(memory, carol.account).balance, 50),
                                read(write(memory, read(memory, carol.account).balance, 50),
                                  carol.account))),
                            alice.account.balance) } φ } := by sol_chain
    _ ~[findCopyMem]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) ‖
                  memory := write(memory, read(memory, carol.account).balance, 50) ‖
                  storage := save(storage, alice.account,
                    copyMem(mtSt, write(memory, read(memory, carol.account).balance, 50),
                      read(write(memory, read(memory, carol.account).balance, 50), carol.account))) ‖
                  sp := alice.account ‖
                  v := read(write(memory, read(memory, carol.account).balance, 50),
                            read(write(memory, read(memory, carol.account).balance, 50),
                              carol.account).balance) } φ } := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[readWriteDifferentIdentity]~> _ := by sol_chain
    _ ~[readOnWrite]~> _ := by sol_chain
    _ ~[simplifyUpdate]~> _ := by sol_chain

#last_line chain

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

set_option maxHeartbeats 4000000 in
/-- … and `v = alice.account.token.value;` read through two more aliases, one
per selector (`sp`, then `aliceTok` through it: lines crossed unwritten), the
two merged with the read, which the merge resolves to
`find(storage, alice.account.token.value)`; then the updates the program
left merged into one, the read sent back into memory, the write read. -/
def read :
    dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
            { memory := write(memory, carolToken.value, 99) }
            { aliceAcc := alice.account }
            { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
            ⟨[ v = alice.account.token.value; ]⟩ φ }
    ~~> dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) ‖ aliceAcc := alice.account ‖
                  storage := save(storage, alice.account.token,
                    copyMem(mtSt, write(memory, carolToken.value, 99), carolToken)) ‖
                  sp := alice.account ‖ aliceTok := alice.account.token ‖ v := 99 } φ } :=
  calc dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
               { memory := write(memory, carolToken.value, 99) }
               { aliceAcc := alice.account }
               { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
               ⟨[ v = alice.account.token.value; ]⟩ φ }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                { sp := alice.account ‖ aliceTok := alice.account.token }
                { v := find(storage, aliceTok.value) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) }
                { aliceAcc := alice.account }
                { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                { sp := alice.account ‖ aliceTok := alice.account.token ‖
                  v := find(storage, alice.account.token.value) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) ‖ aliceAcc := alice.account ‖
                  storage := save(storage, alice.account.token,
                    copyMem(mtSt, write(memory, carolToken.value, 99), carolToken)) ‖
                  sp := alice.account ‖ aliceTok := alice.account.token ‖
                  v := find(save(storage, alice.account.token,
                              copyMem(mtSt, write(memory, carolToken.value, 99), carolToken)),
                            alice.account.token.value) } φ } := by sol_chain
    _ ~[findCopyMem]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) ‖ aliceAcc := alice.account ‖
                  storage := save(storage, alice.account.token,
                    copyMem(mtSt, write(memory, carolToken.value, 99), carolToken)) ‖
                  sp := alice.account ‖ aliceTok := alice.account.token ‖
                  v := read(write(memory, carolToken.value, 99), carolToken.value) } φ } := by sol_chain
    _ ~[readOnWrite]~>
        dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
                { memory := write(memory, carolToken.value, 99) ‖ aliceAcc := alice.account ‖
                  storage := save(storage, alice.account.token,
                    copyMem(mtSt, write(memory, carolToken.value, 99), carolToken)) ‖
                  sp := alice.account ‖ aliceTok := alice.account.token ‖ v := 99 } φ } := by sol_chain

/-- `carolToken.value = 99; alice.account.token = carolToken;
v = alice.account.token.value;` — the copy, then the read, to `99`. -/
theorem chain :
    dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
            ⟨[ carolToken.value = 99; alice.account.token = carolToken;
               v = alice.account.token.value; ]⟩ φ }
    ~~> dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖
          memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖
          storage :=
            save(storage, alice.account.token,
              copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                freshId(addM(memory, Token)))) ‖
          v := 99 } φ } :=
  calc dl![m]{ { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
               ⟨[ carolToken.value = 99; alice.account.token = carolToken;
                  v = alice.account.token.value; ]⟩ φ }
    _ ~*> _ := copy m φ
    _ ~~> _ := read m φ
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[simplifyUpdate]~> _ := by sol_chain

#last_line chain

end NonsimplePath

end Solidity.Examples.Chains.MemoryToStorage
