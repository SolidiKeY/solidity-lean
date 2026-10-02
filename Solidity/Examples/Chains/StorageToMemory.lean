import Solidity.Calculus.Chains
import Solidity.FreshNames

/-!
# Storage-to-memory copies, as chains

The calculus's three worked examples of a copy from storage into a fresh
memory object, each a `calc` for every modality `m` and postcondition `φ`
(`Calculus/Chains.lean`: `~[r]~>` is a printed `⇝` naming its rule, `~*>` a `⇝*`).
The printed `memoryStorageCopyRoot` is `memoryStorageCopy` here.  The root `r`
the copy allocates is `freshId(copySt(memory, …))`, and the update stays as
the rules leave it.

Not drawn: the lines after the copy, where the printed trace merges the
storage write over the memory updates and reads the copy back
(`readCopySt`, `findOnSave`).  `sequentialToParallel` does not substitute
into a memory term, and `readCopySt` is no chain rewrite yet.
-/

namespace Solidity.Examples.Chains.StorageToMemory

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Symbolic Execution of Storage-to-Memory Copy with Lazy Read -/

namespace RootCopy

variable (m : Modality) (φ : Post StandardExample)

/-- `alice.age = 25; Person memory carol = alice; v = carol.age;` — the copy is
a fresh object holding a snapshot of `alice`, and the read is a read of it.
The line the declaration leaves says `carol` is a memory local. -/
def chain :
    dl![m]{ ⟨[ alice.age = 25; Person memory carol = alice; v = carol.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 25) }
                { carol := freshId(copySt(memory, find(storage, alice))) ‖
                  memory := copySt(memory, find(storage, alice)) }
                { v := read(memory, carol.age) } φ } :=
  calc dl![m]{ ⟨[ alice.age = 25; Person memory carol = alice; v = carol.age; ]⟩ φ }
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { storage := save(storage, alice.age, 25) }
                ⟨[ Person memory carol = alice; v = carol.age; ]⟩ φ } := rfl
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { storage := save(storage, alice.age, 25) }
                ⟨[ carol = alice; v = carol.age; ]⟩ φ where Person memory carol } := rfl
    _ ~[memoryStorageCopy]~>
        dl![m]{ { storage := save(storage, alice.age, 25) }
                { carol := freshId(copySt(memory, find(storage, alice))) ‖
                  memory := copySt(memory, find(storage, alice)) }
                ⟨[ v = carol.age; ]⟩ φ } := rfl
    _ ~[memoryFieldReadHeap]~>
        dl![m]{ { storage := save(storage, alice.age, 25) }
                { carol := freshId(copySt(memory, find(storage, alice))) ‖
                  memory := copySt(memory, find(storage, alice)) }
                { v := read(memory, carol.age) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { storage := save(storage, alice.age, 25) }
                { carol := freshId(copySt(memory, find(storage, alice))) ‖
                  memory := copySt(memory, find(storage, alice)) }
                { v := read(memory, carol.age) } φ } := rfl

end RootCopy

/-! ## Example: Symbolic Execution of Storage-to-Memory Field Copy with Lazy Read -/

namespace FieldCopy

/-- The printed names of the rules' fresh variables: the value `pv`, the
storage aliases `aliceAcc` and `sp`. -/
def names : FreshTable := [("pv", "se1"), ("aliceAcc", "sp1"), ("sp", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

/-- `alice.account.balance = 10;` of the program: unfolded through the alias
`aliceAcc`, then written. -/
def write :
    dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~*> dl![m]{ { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
                ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    _ ~[storageFieldWrite_unfold_leftFst]~>
        dl![m]{ ⟨[ uint pv = 10; Account storage aliceAcc = alice.account; aliceAcc.balance = pv;
                   Account memory acc = alice.account; v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { pv := 10 } { aliceAcc := alice.account }
                  ⟨[ aliceAcc.balance = pv; Account memory acc = alice.account; v = acc.balance; ]⟩ φ } := by
      sol_chain
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
                ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ } := rfl

/-- `Account memory acc = alice.account;` — the declaration dropped, the member
source captured in the alias `sp`, and the three updates the program left
merged. -/
def source :
    dl![m]{ { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
            ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~~> dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc } :=
  calc dl![m]{ { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
               ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
                ⟨[ acc = alice.account; v = acc.balance; ]⟩ φ where Account memory acc } := rfl
    _ ~[memoryStorageCopyUnfold]~>
        dl![m]{ { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
                ⟨[ Account storage sp = alice.account; acc = sp; v = acc.balance; ]⟩ φ
                where Account memory acc } := by sol_chain
    _ ~*> dl![m]{ { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
                  { sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc } := by
      sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc } := by
      sol_chain

/-- … then `acc` a copy of the object `sp` names, and `v = acc.balance;` a read
of the copy. -/
def install :
    dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
              sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc }
    ~*> dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp))) ‖
                  memory := copySt(memory, find(storage, sp)) }
                { v := read(memory, acc.balance) } φ } :=
  calc dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                 sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc }
    _ ~[memoryStorageCopy]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp))) ‖
                  memory := copySt(memory, find(storage, sp)) }
                ⟨[ v = acc.balance; ]⟩ φ } := rfl
    _ ~[memoryFieldReadHeap]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp))) ‖
                  memory := copySt(memory, find(storage, sp)) }
                { v := read(memory, acc.balance) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp))) ‖
                  memory := copySt(memory, find(storage, sp)) }
                { v := read(memory, acc.balance) } φ } := rfl

/-- `alice.account.balance = 10; Account memory acc = alice.account;
v = acc.balance;` — the write unfolds through the alias `aliceAcc`, and the
member source of the copy is captured in a second alias `sp`; the updates the
program left merge once `sp` is bound. -/
def chain :
    dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~~> dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp))) ‖
                  memory := copySt(memory, find(storage, sp)) }
                { v := read(memory, acc.balance) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    _ ~*> _ := write m φ
    _ ~~> _ := source m φ
    _ ~*> _ := install m φ

end FieldCopy

/-! ## Example: Symbolic Execution of `Token memory t = alice.account.token` -/

namespace TokenCopy

/-- The nonsimple source is captured in `aliceTok`, which resolves through
`aliceAcc`, the alias the second unfolding declares. -/
def names : FreshTable := [("aliceTok", "sp1"), ("aliceAcc", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (m : Modality) (φ : Post StandardExample)

/-- `Token memory t = alice.account.token;` — the declaration dropped, the
source captured in `aliceTok`; `aliceAcc` is dead once the two aliases merge. -/
def source :
    dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    ~~> dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t } :=
  calc dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ ⟨[ t = alice.account.token; ]⟩ φ where Token memory t } := rfl
    _ ~[memoryStorageCopyUnfold]~>
        dl![m]{ ⟨[ Token storage aliceTok = alice.account.token; t = aliceTok; ]⟩ φ where Token memory t } :=
      by sol_chain
    _ ~*> dl![m]{ { aliceAcc := alice.account } { aliceTok := aliceAcc.token } ⟨[ t = aliceTok; ]⟩ φ
                  where Token memory t } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { aliceAcc := alice.account ‖ aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ
                where Token memory t } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t } := by sol_chain

/-- … then `t` a copy of the object `aliceTok` names, and the updates merged. -/
def install :
    dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t }
    ~~> dl![m]{ { aliceTok := alice.account.token ‖
                  t := freshId(copySt(memory, find(storage, alice.account.token))) ‖
                  memory := copySt(memory, find(storage, alice.account.token)) } φ } :=
  calc dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t }
    _ ~[memoryStorageCopy]~>
        dl![m]{ { aliceTok := alice.account.token }
                { t := freshId(copySt(memory, find(storage, aliceTok))) ‖
                  memory := copySt(memory, find(storage, aliceTok)) } ⟨[ ]⟩ φ } := by sol_chain
    _ ~[emptyModality]~>
        dl![m]{ { aliceTok := alice.account.token }
                { t := freshId(copySt(memory, find(storage, aliceTok))) ‖
                  memory := copySt(memory, find(storage, aliceTok)) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { aliceTok := alice.account.token ‖
                  t := freshId(copySt(memory, find(storage, alice.account.token))) ‖
                  memory := copySt(memory, find(storage, alice.account.token)) } φ } := by sol_chain

/-- `Token memory t = alice.account.token;` — the declaration dropped, the
nonsimple source captured in `aliceTok`, which resolves through `aliceAcc`,
and the copy installed. -/
def chain :
    dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    ~~> dl![m]{ { aliceTok := alice.account.token ‖
                  t := freshId(copySt(memory, find(storage, alice.account.token))) ‖
                  memory := copySt(memory, find(storage, alice.account.token)) } φ } :=
  calc dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    _ ~~> _ := source m φ
    _ ~~> _ := install m φ

end TokenCopy

end Solidity.Examples.Chains.StorageToMemory
