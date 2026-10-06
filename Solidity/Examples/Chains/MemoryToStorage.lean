import Solidity.Calculus.LastLine
import Solidity.Calculus.Chains
import Solidity.FreshNames

/-!
# Memory-to-storage copies, as chains

The calculus's four worked examples of a copy from a memory object into
storage, each one chain term over any modality `m` and postcondition `φ`
(`Examples/Chains/Storage.lean` says how to read one), in the printed names
(`FreshNames` tables).  A chain starts under the update the declaration of
the memory object leaves,
`{ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }`,
where the printed trace starts from an object it does not declare; that
update is the concrete starting state, and nothing else is needed: each
program reads only what it wrote, and its values are literals.

The strategy's steps are grouped as the paper prints them: a printed `⇝`
that fires several rules (the copy with the read after it, a declaration
dropped with the binding it leaves) is one `~*>`.  Past the program the
updates merge into one, the declaration's included — the memory write
substituted for `memory` in the storage write, as the printed `S₁` reads
`copyMem(mtSt, M₁, carol)` — and the read is resolved one law a link
(`Calculus/ChainRewrites.lean`), every capture kept to the last line:
`findMemberCons` and `selectOnSaveMember` walk the path down to the copy,
`findCopyMem` sends the `find` back into memory, `readOnWrite` reads the
write.  In the member-source example the copied identity is read after the
write, and `readWriteDifferentIdentity` (the write at `balance` leaves
`account` alone) reads it back to the identity written.
-/

namespace Solidity.Examples.Chains.MemoryToStorage

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Symbolic Execution of Memory-to-Storage Copy with Lazy Read -/

namespace RootCopy

variable (m : Modality) (φ : Post StandardExample)

/-- `carol.age = 42; alice = carol; v = alice.age;` — a memory object copied
into a storage root (`copyMem`), and read back from storage: the write, the
copy with the read (the paper's one `⇝`), the merge, the read sent back into
memory (`findCopyMem`), the write read (`readOnWrite`). -/
theorem chain :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        ⟨[ carol.age = 42; alice = carol; v = alice.age; ]⟩ φ }
    ~[memoryFieldWriteStore]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { memory := write(memory, carol.age, 42) } ⟨[ alice = carol; v = alice.age; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { memory := write(memory, carol.age, 42) }
            { storage := save(storage, alice, copyMem(mtSt, memory, carol)) } { v := find(storage, alice.age) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            memory := write(addM(memory, Person), freshId(addM(memory, Person)).age, 42) ‖
            storage :=
              save(storage, alice,
                copyMem(mtSt, write(addM(memory, Person), freshId(addM(memory, Person)).age, 42),
                  freshId(addM(memory, Person)))) ‖
            v :=
              find(save(storage, alice,
                  copyMem(mtSt, write(addM(memory, Person), freshId(addM(memory, Person)).age, 42),
                    freshId(addM(memory, Person)))),
                alice.age) }
          φ }
    ~[findCopyMem]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            memory := write(addM(memory, Person), freshId(addM(memory, Person)).age, 42) ‖
            storage :=
              save(storage, alice,
                copyMem(mtSt, write(addM(memory, Person), freshId(addM(memory, Person)).age, 42),
                  freshId(addM(memory, Person)))) ‖
            v := read(write(addM(memory, Person), freshId(addM(memory, Person)).age, 42), freshId(addM(memory, Person)).age) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            memory := write(addM(memory, Person), freshId(addM(memory, Person)).age, 42) ‖
            storage :=
              save(storage, alice,
                copyMem(mtSt, write(addM(memory, Person), freshId(addM(memory, Person)).age, 42),
                  freshId(addM(memory, Person)))) ‖
            v := 42 }
          φ } := by
  sol_chain

#last_line chain

end RootCopy

/-! ## Example: Symbolic Execution of Memory-to-Storage Field Copy with Lazy Read -/

namespace FieldCopy

/-- The printed name of the storage alias the read unfolds through. -/
def names : FreshTable := [("acc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

/-- `carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance;`
— into a member of a storage root, read back through the alias `acc`: the
write, the copy with the read unfolded, the alias bound and the read, the
merge; then the read walked down to the copy (`findMemberCons`,
`selectOnSaveMember`), sent back into memory, and the write read. -/
theorem chain :
    dl![m]{
      { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
        ⟨[ carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance; ]⟩ φ }
    ~[memoryFieldWriteStore]~> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
          { memory := write(memory, carolAcc.balance, 50) } ⟨[ alice.account = carolAcc; v = alice.account.balance; ]⟩ φ }
    ~*> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
          { memory := write(memory, carolAcc.balance, 50) }
            { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
              ⟨[ Account storage acc = alice.account; v = acc.balance; ]⟩ φ }
    ~*> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
          { memory := write(memory, carolAcc.balance, 50) }
            { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
              { acc := alice.account } { v := find(storage, acc.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖
            memory := write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                  freshId(addM(memory, Account)))) ‖
            acc := alice.account ‖
            v :=
              find(save(storage, alice.account,
                  copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                    freshId(addM(memory, Account)))),
                alice.account.balance) }
          φ }
    ~[findMemberCons]~> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖
            memory := write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                  freshId(addM(memory, Account)))) ‖
            acc := alice.account ‖
            v :=
              find(select(save(storage, alice.account,
                    copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                      freshId(addM(memory, Account)))),
                  alice),
                account.balance) }
          φ }
    ~[selectOnSaveMember]~> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖
            memory := write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                  freshId(addM(memory, Account)))) ‖
            acc := alice.account ‖
            v :=
              find(save(select(storage, alice), account,
                  copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                    freshId(addM(memory, Account)))),
                account.balance) }
          φ }
    ~[findCopyMem]~> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖
            memory := write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                  freshId(addM(memory, Account)))) ‖
            acc := alice.account ‖
            v :=
              read(write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                freshId(addM(memory, Account)).balance) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { carolAcc := freshId(addM(memory, Account)) ‖
            memory := write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt, write(addM(memory, Account), freshId(addM(memory, Account)).balance, 50),
                  freshId(addM(memory, Account)))) ‖
            acc := alice.account ‖ v := 50 }
          φ } := by
  sol_chain

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

/-- `carol.account.balance = 50; alice.account = carol.account;
v = alice.account.balance;` — the source a member of a memory object: its
identity is read from memory (`carolAcc`, the printed `i_acc`), and what is
copied is the identity read after the write (`i_rhs`).  After the merge the
read walks down to the copy and `findCopyMem` sends it back into memory, at
`i_rhs`; `readWriteDifferentIdentity` reads `i_rhs` back to `i_acc` (the
write at `balance` does not touch `account`), and `readOnWrite` reads the
write. -/
theorem chain :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        ⟨[ carol.account.balance = 50; alice.account = carol.account; v = alice.account.balance; ]⟩ φ }
    ~[memoryFieldWrite_unfold_leftFst]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ Account memory carolAcc = carol.account; carolAcc.balance = 50; alice.account = carol.account;
            v = alice.account.balance; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ carolAcc = carol.account; carolAcc.balance = 50; alice.account = carol.account;
            v = alice.account.balance; ]⟩ φ where Account memory carolAcc }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) }
            { memory := write(memory, carolAcc.balance, 50) }
              ⟨[ alice.account = carol.account; v = alice.account.balance; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) }
            { memory := write(memory, carolAcc.balance, 50) }
              { storage := save(storage, alice.account, copyMem(mtSt, memory, read(memory, carol.account))) }
                { sp := alice.account } { v := find(storage, sp.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt,
                  write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                  read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      50),
                    freshId(addM(memory, Person)).account))) ‖
            sp := alice.account ‖
            v :=
              find(save(storage, alice.account,
                  copyMem(mtSt,
                    write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      50),
                    read(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                      freshId(addM(memory, Person)).account))),
                alice.account.balance) }
          φ }
    ~[findMemberCons]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt,
                  write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                  read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      50),
                    freshId(addM(memory, Person)).account))) ‖
            sp := alice.account ‖
            v :=
              find(select(save(storage, alice.account,
                    copyMem(mtSt,
                      write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                        50),
                      read(write(addM(memory, Person),
                          read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                        freshId(addM(memory, Person)).account))),
                  alice),
                account.balance) }
          φ }
    ~[selectOnSaveMember]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt,
                  write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                  read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      50),
                    freshId(addM(memory, Person)).account))) ‖
            sp := alice.account ‖
            v :=
              find(save(select(storage, alice), account,
                  copyMem(mtSt,
                    write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      50),
                    read(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                      freshId(addM(memory, Person)).account))),
                account.balance) }
          φ }
    ~[findCopyMem]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt,
                  write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                  read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      50),
                    freshId(addM(memory, Person)).account))) ‖
            sp := alice.account ‖
            v :=
              read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      50),
                    freshId(addM(memory, Person)).account).balance) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt,
                  write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                  read(addM(memory, Person), freshId(addM(memory, Person)).account))) ‖
            sp := alice.account ‖
            v :=
              read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                read(addM(memory, Person), freshId(addM(memory, Person)).account).balance) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50) ‖
            storage :=
              save(storage, alice.account,
                copyMem(mtSt,
                  write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 50),
                  read(addM(memory, Person), freshId(addM(memory, Person)).account))) ‖
            sp := alice.account ‖ v := 50 }
          φ } := by
  sol_chain

#last_line chain

end PathCopy

/-! ## Example: Symbolic Execution of Memory-to-Storage Nonsimple Path Copy -/

namespace NonsimplePath

/-- `aliceAcc`, the printed alias of the target's prefix.  The read unfolds through two more aliases, which
the paper does not print; they are named here `aliceTok` and `sp`. -/
def names : FreshTable := [("aliceAcc", "sp1"), ("aliceTok", "sp2"), ("sp", "sp3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

/-- `carolToken.value = 99; alice.account.token = carolToken;
v = alice.account.token.value;` — the target is the nonsimple path: its
prefix is aliased (`memoryToStorageField_unfold_leftFst`) and the copy goes
into the alias.  The memory source `carolToken` is already a local, so there
is no printed `tok` alias.  The paper's one `⇝` to `S₁` binds `aliceAcc`,
copies, and reads through two more aliases, one per selector; then the
merge, the read walked down to the copy a member at a time, sent back into
memory, and the write read, to `99`. -/
theorem chain :
    dl![m]{
      { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
        ⟨[ carolToken.value = 99; alice.account.token = carolToken; v = alice.account.token.value; ]⟩ φ }
    ~[memoryFieldWriteStore]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
          { memory := write(memory, carolToken.value, 99) }
            ⟨[ alice.account.token = carolToken; v = alice.account.token.value; ]⟩ φ }
    ~[memoryToStorageField_unfold_leftFst]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
          { memory := write(memory, carolToken.value, 99) }
            ⟨[ Account storage aliceAcc = alice.account; aliceAcc.token = carolToken; v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖ memory := addM(memory, Token) }
          { memory := write(memory, carolToken.value, 99) }
            { aliceAcc := alice.account }
              { storage := save(storage, aliceAcc.token, copyMem(mtSt, memory, carolToken)) }
                { sp := alice.account } { aliceTok := sp.token } { v := find(storage, aliceTok.value) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖
            memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖ aliceAcc := alice.account ‖
            storage :=
              save(storage, alice.account.token,
                copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                  freshId(addM(memory, Token)))) ‖
            sp := alice.account ‖ aliceTok := alice.account.token ‖
            v :=
              find(save(storage, alice.account.token,
                  copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                    freshId(addM(memory, Token)))),
                alice.account.token.value) }
          φ }
    ~[findMemberCons]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖
            memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖ aliceAcc := alice.account ‖
            storage :=
              save(storage, alice.account.token,
                copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                  freshId(addM(memory, Token)))) ‖
            sp := alice.account ‖ aliceTok := alice.account.token ‖
            v :=
              find(select(save(storage, alice.account.token,
                    copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                      freshId(addM(memory, Token)))),
                  alice),
                account.token.value) }
          φ }
    ~[findMemberCons]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖
            memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖ aliceAcc := alice.account ‖
            storage :=
              save(storage, alice.account.token,
                copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                  freshId(addM(memory, Token)))) ‖
            sp := alice.account ‖ aliceTok := alice.account.token ‖
            v :=
              find(select(select(save(storage, alice.account.token,
                      copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                        freshId(addM(memory, Token)))),
                    alice),
                  account),
                token.value) }
          φ }
    ~[selectOnSaveMemberIn]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖
            memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖ aliceAcc := alice.account ‖
            storage :=
              save(storage, alice.account.token,
                copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                  freshId(addM(memory, Token)))) ‖
            sp := alice.account ‖ aliceTok := alice.account.token ‖
            v :=
              find(select(save(select(storage, alice), account.token,
                    copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                      freshId(addM(memory, Token)))),
                  account),
                token.value) }
          φ }
    ~[selectOnSaveMember]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖
            memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖ aliceAcc := alice.account ‖
            storage :=
              save(storage, alice.account.token,
                copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                  freshId(addM(memory, Token)))) ‖
            sp := alice.account ‖ aliceTok := alice.account.token ‖
            v :=
              find(save(select(select(storage, alice), account), token,
                  copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                    freshId(addM(memory, Token)))),
                token.value) }
          φ }
    ~[findCopyMem]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖
            memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖ aliceAcc := alice.account ‖
            storage :=
              save(storage, alice.account.token,
                copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                  freshId(addM(memory, Token)))) ‖
            sp := alice.account ‖ aliceTok := alice.account.token ‖
            v :=
              read(write(addM(memory, Token), freshId(addM(memory, Token)).value, 99), freshId(addM(memory, Token)).value) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { carolToken := freshId(addM(memory, Token)) ‖
            memory := write(addM(memory, Token), freshId(addM(memory, Token)).value, 99) ‖ aliceAcc := alice.account ‖
            storage :=
              save(storage, alice.account.token,
                copyMem(mtSt, write(addM(memory, Token), freshId(addM(memory, Token)).value, 99),
                  freshId(addM(memory, Token)))) ‖
            sp := alice.account ‖ aliceTok := alice.account.token ‖ v := 99 }
          φ } := by
  sol_chain

#last_line chain

end NonsimplePath

end Solidity.Examples.Chains.MemoryToStorage
