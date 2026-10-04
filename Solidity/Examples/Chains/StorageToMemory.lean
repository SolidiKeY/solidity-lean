import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.FreshNames

/-!
# Storage-to-memory copies, as chains

The calculus's three worked examples of a copy from storage into a fresh
memory object, each a `calc` for every modality `m` and postcondition `φ`
(`Calculus/Chains.lean`: `~[r]~>` is a printed `⇝` naming its rule, `~*>` a `⇝*`).
The printed `memoryStorageCopyRoot` is `memoryStorageCopy` here.  The root `r`
the copy allocates is `freshId(copySt(memory, …))`, and the update stays as
the rules leave it.

After the copy the updates merge into one — the copy's identity and memory
substituted into the read, the storage write into the copy — and the read
is resolved by the laws of memory reads (`EvalLaw`,
`Calculus/ChainRewrites.lean`): `readCopySt` reads the copy out of the
storage it copied, then `findOnSave` the write.  A line that binds an alias
through another alias is crossed unwritten, the next written line being its
merge.
-/

namespace Solidity.Examples.Chains.StorageToMemory

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Symbolic Execution of Storage-to-Memory Copy with Lazy Read -/

namespace RootCopy

variable (m : Modality) (φ : Post StandardExample)

set_option maxHeartbeats 4000000 in
/-- `alice.age = 25; Person memory carol = alice; v = carol.age;` — the copy is
a fresh object holding a snapshot of `alice`, and the read is a read of it.
The line the declaration leaves says `carol` is a memory local.  The updates
merged, the read of the copy is a read of the storage copied (`readCopySt`),
which the write answers (`findOnSave`). -/
theorem chain :
    dl![m]{ ⟨[ alice.age = 25; Person memory carol = alice; v = carol.age; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 25) ‖
                  carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
                  memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
                  v := 25 } φ } :=
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
    _ ~*>
        dl![m]{ { storage := save(storage, alice.age, 25) }
                { carol := freshId(copySt(memory, find(storage, alice))) ‖
                  memory := copySt(memory, find(storage, alice)) }
                { v := read(memory, carol.age) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, alice.age, 25) ‖
                  carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
                  memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
                  v := read(copySt(memory, find(save(storage, alice.age, 25), alice)),
                            freshId(copySt(memory, find(save(storage, alice.age, 25), alice))).age) } φ } := by
      sol_chain
    _ ~[readCopySt]~>
        dl![m]{ { storage := save(storage, alice.age, 25) ‖
                  carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
                  memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
                  v := find(save(storage, alice.age, 25), alice.age) } φ } := by sol_chain
    _ ~[findOnSave]~>
        dl![m]{ { storage := save(storage, alice.age, 25) ‖
                  carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
                  memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
                  v := 25 } φ } := by sol_chain

#last_line chain
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
theorem source :
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

set_option maxHeartbeats 4000000 in
/-- … then `acc` a copy of the object `sp` names, and `v = acc.balance;` a read
of the copy: the updates merged, the read of the copy a read of the storage
copied (`readCopySt`), which the write answers (`findOnSave`). -/
theorem install :
    dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
              sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc }
    ~~> dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account ‖
                  acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
                  memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
                  v := 10 } φ } :=
  calc dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                 sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc }
    _ ~[memoryStorageCopy]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp))) ‖
                  memory := copySt(memory, find(storage, sp)) }
                ⟨[ v = acc.balance; ]⟩ φ } := rfl
    _ ~*>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp))) ‖
                  memory := copySt(memory, find(storage, sp)) }
                { v := read(memory, acc.balance) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account ‖
                  acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
                  memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
                  v := read(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)),
                            freshId(copySt(memory, find(save(storage, alice.account.balance, 10),
                              alice.account))).balance) } φ } := by sol_chain
    _ ~[readCopySt]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account ‖
                  acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
                  memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
                  v := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ } := by
      sol_chain
    _ ~[findOnSave]~>
        dl![m]{ { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
                  sp := alice.account ‖
                  acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
                  memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
                  v := 10 } φ } := by sol_chain

/-- `alice.account.balance = 10; Account memory acc = alice.account;
v = acc.balance;` — the write unfolds through the alias `aliceAcc`, and the
member source of the copy is captured in a second alias `sp`; the updates the
program left merge once `sp` is bound, and the read resolves to `10`. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
                  acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
                  memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
                  v := 10 } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    _ ~*> _ := write m φ
    _ ~~> _ := source m φ
    _ ~~> _ := install m φ
    _ ~[simplifyUpdate]~>
        dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
                  acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
                  memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
                  v := 10 } φ } := by sol_chain
#last_line chain

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
source captured in `aliceTok`, through `aliceAcc` (the steps binding them are
crossed unwritten; the merge binds `aliceTok` to `alice.account.token`);
`aliceAcc` is dead once the two aliases merge. -/
theorem source :
    dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    ~~> dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t } :=
  calc dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ ⟨[ t = alice.account.token; ]⟩ φ where Token memory t } := rfl
    _ ~[memoryStorageCopyUnfold]~>
        dl![m]{ ⟨[ Token storage aliceTok = alice.account.token; t = aliceTok; ]⟩ φ where Token memory t } :=
      by sol_chain
    _ ~*> dl![m]{ ⟨[ aliceTok = alice.account.token; t = aliceTok; ]⟩ φ where Token memory t } := by
      sol_chain
    _ ~[storageFieldRead_unfold_rightFst]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { aliceAcc := alice.account ‖ aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ
                where Token memory t } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t } := by sol_chain

/-- … then `t` a copy of the object `aliceTok` names, and the updates merged. -/
theorem install :
    dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t }
    ~~> dl![m]{ { aliceTok := alice.account.token ‖
                  t := freshId(copySt(memory, find(storage, alice.account.token))) ‖
                  memory := copySt(memory, find(storage, alice.account.token)) } φ } :=
  calc dl![m]{ { aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t }
    _ ~*>
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
theorem chain :
    dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    ~~> dl![m]{ { t := freshId(copySt(memory, find(storage, alice.account.token))) ‖
                  memory := copySt(memory, find(storage, alice.account.token)) } φ } :=
  calc dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    _ ~~> _ := source m φ
    _ ~~> _ := install m φ
    _ ~[simplifyUpdate]~>
        dl![m]{ { t := freshId(copySt(memory, find(storage, alice.account.token))) ‖
                  memory := copySt(memory, find(storage, alice.account.token)) } φ } := by sol_chain
#last_line chain

end TokenCopy

end Solidity.Examples.Chains.StorageToMemory
