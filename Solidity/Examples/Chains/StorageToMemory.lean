import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.FreshNames

/-!
# Storage-to-memory copies, as chains

The calculus's three worked examples of a copy from storage into a fresh memory object, each one chain term
over any modality `m` and postcondition `φ` (`Examples/Chains/Storage.lean` says how to read one), in the
printed names (`FreshNames` tables).  The root `r` the copy allocates is `freshId(copySt(memory, …))`.

Where the paper prints the updates merged before the copy (the alias `sp`, `aliceTok`), the chain merges
there too (`~[sequentialToParallel]~>` under the open modality), and again past the program.  The read of the
copy is then resolved one law a link (`Calculus/ChainRewrites.lean`): `readCopySt` reads the copy out of the
storage it copied, `findOnSave` the write.  Every capture stays to the last line, which `#last_line` checks.
The copied struct itself (`find(S, alice)`) is a struct read and has no literal: no law reads a struct
through a write below it.
-/

namespace Solidity.Examples.Chains.StorageToMemory

local instance : InContract := ⟨StandardExample⟩

section
variable (m : Modality) (φ : Post StandardExample)

/-! ## Example: Symbolic Execution of Storage-to-Memory Copy with Lazy Read -/

namespace RootCopy
/-- `alice.age = 25; Person memory carol = alice; v = carol.age;` — the copy is a fresh object holding a
snapshot of `alice`, and the read is a read of it.  The line the declaration leaves says `carol` is a memory
local.  The updates merged, the read of the copy is a read of the storage copied (`readCopySt`), which the
write answers (`findOnSave`). -/
theorem chain :
    dl![m]{ ⟨[ alice.age = 25; Person memory carol = alice; v = carol.age; ]⟩ φ }
    ~[storageFieldWriteSave]~>
      dl![m]{ { storage := save(storage, alice.age, 25) } ⟨[ Person memory carol = alice; v = carol.age; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { storage := save(storage, alice.age, 25) } ⟨[ carol = alice; v = carol.age; ]⟩ φ where Person memory carol }
    ~[memoryStorageCopy]~> dl![m]{
        { storage := save(storage, alice.age, 25) }
          { carol := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
          ⟨[ v = carol.age; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, alice.age, 25) }
          { carol := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
          { v := read(memory, carol.age) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, alice.age, 25) ‖
            carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
            memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
            v := read(copySt(memory, find(save(storage, alice.age, 25), alice)),
                freshId(copySt(memory, find(save(storage, alice.age, 25), alice))).age) } φ }
    ~[readCopySt]~> dl![m]{
        { storage := save(storage, alice.age, 25) ‖
            carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
            memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖
            v := find(save(storage, alice.age, 25), alice.age) } φ }
    ~[findOnSave]~> dl![m]{
        { storage := save(storage, alice.age, 25) ‖
            carol := freshId(copySt(memory, find(save(storage, alice.age, 25), alice))) ‖
            memory := copySt(memory, find(save(storage, alice.age, 25), alice)) ‖ v := 25 } φ } := by
  sol_chain
#last_line chain
end RootCopy

/-! ## Example: Symbolic Execution of Storage-to-Memory Field Copy with Lazy Read -/

namespace FieldCopy
/-- The printed names of the rules' fresh variables: the value `pv`, the storage aliases `aliceAcc` and
`sp`. -/
def names : FreshTable := [("pv", "se1"), ("aliceAcc", "sp1"), ("sp", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `alice.account.balance = 10; Account memory acc = alice.account;` up to the copy: the write unfolded
through the alias `aliceAcc` and saved, the declaration dropped, the member source captured in a second alias
`sp` (the paper's `⇝*` binds it), and the updates merged, as the paper prints them before the copy. -/
theorem source :
    dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~> dl![m]{
        ⟨[ uint pv = 10; Account storage aliceAcc = alice.account; aliceAcc.balance = pv;
          Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~*> dl![m]{ { pv := 10 } { aliceAcc := alice.account }
        ⟨[ aliceAcc.balance = pv; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl![m]{
        { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
          ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
          ⟨[ acc = alice.account; v = acc.balance; ]⟩ φ where Account memory acc }
    ~[memoryStorageCopyUnfold]~> dl![m]{
        { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
          ⟨[ Account storage sp = alice.account; acc = sp; v = acc.balance; ]⟩ φ where Account memory acc }
    ~*> dl![m]{
        { pv := 10 } { aliceAcc := alice.account } { storage := save(storage, aliceAcc.balance, pv) }
          { sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc }
    ~[sequentialToParallel]~> dl![m]{
        { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
            sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc } := by
  sol_chain

/-- … then `acc` a copy of the object `sp` names, and `v = acc.balance;` a read of the copy: the updates
merged, the read of the copy a read of the storage copied (`readCopySt`), which the write answers
(`findOnSave`). -/
theorem copy :
    dl![m]{
      { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
          sp := alice.account } ⟨[ acc = sp; v = acc.balance; ]⟩ φ where Account memory acc }
    ~[memoryStorageCopy]~> dl![m]{
        { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
            sp := alice.account }
          { acc := freshId(copySt(memory, find(storage, sp))) ‖ memory := copySt(memory, find(storage, sp)) }
          ⟨[ v = acc.balance; ]⟩ φ }
    ~*> dl![m]{
        { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
            sp := alice.account }
          { acc := freshId(copySt(memory, find(storage, sp))) ‖ memory := copySt(memory, find(storage, sp)) }
          { v := read(memory, acc.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
            sp := alice.account ‖
            acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
            memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
            v := read(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)),
                freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))).balance) } φ }
    ~[readCopySt]~> dl![m]{
        { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
            sp := alice.account ‖
            acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
            memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
            v := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ }
    ~[findOnSave]~> dl![m]{
        { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
            sp := alice.account ‖
            acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
            memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
            v := 10 } φ } := by
  sol_chain

/-- `alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance;`: `source` then
`copy`. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~~> dl![m]{
        { pv := 10 ‖ aliceAcc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
            sp := alice.account ‖
            acc := freshId(copySt(memory, find(save(storage, alice.account.balance, 10), alice.account))) ‖
            memory := copySt(memory, find(save(storage, alice.account.balance, 10), alice.account)) ‖
            v := 10 } φ } :=
  (source ..).leads.via (copy ..)
#last_line chain
end FieldCopy

/-! ## Example: Symbolic Execution of `Token memory t = alice.account.token` -/

namespace TokenCopy
/-- The nonsimple source is captured in `aliceTok`, which resolves through `aliceAcc`, the alias the second
unfolding declares. -/
def names : FreshTable := [("aliceTok", "sp1"), ("aliceAcc", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `Token memory t = alice.account.token;` from a storage where `alice.account.token.value` is 5: the
declaration dropped, the source captured in `aliceTok`, bound through `aliceAcc` (the paper's `⇝*`), the
updates merged, which binds `aliceTok` to `alice.account.token`, and the copy installed.  The copy holds the
token read in the starting storage; a struct read has no literal. -/
theorem chain :
    dl![m]{ { storage := save(storage, alice.account.token.value, 5) } ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { storage := save(storage, alice.account.token.value, 5) } ⟨[ t = alice.account.token; ]⟩ φ
          where Token memory t }
    ~[memoryStorageCopyUnfold]~> dl![m]{
        { storage := save(storage, alice.account.token.value, 5) }
          ⟨[ Token storage aliceTok = alice.account.token; t = aliceTok; ]⟩ φ where Token memory t }
    ~*> dl![m]{
        { storage := save(storage, alice.account.token.value, 5) } { aliceAcc := alice.account }
          { aliceTok := aliceAcc.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, alice.account.token.value, 5) ‖ aliceAcc := alice.account ‖
            aliceTok := alice.account.token } ⟨[ t = aliceTok; ]⟩ φ where Token memory t }
    ~*> dl![m]{
        { storage := save(storage, alice.account.token.value, 5) ‖ aliceAcc := alice.account ‖
            aliceTok := alice.account.token }
          { t := freshId(copySt(memory, find(storage, aliceTok))) ‖ memory := copySt(memory, find(storage, aliceTok)) }
          φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, alice.account.token.value, 5) ‖ aliceAcc := alice.account ‖
            aliceTok := alice.account.token ‖
            t := freshId(copySt(memory, find(save(storage, alice.account.token.value, 5), alice.account.token))) ‖
            memory := copySt(memory, find(save(storage, alice.account.token.value, 5), alice.account.token)) } φ } := by
  sol_chain
#last_line chain
end TokenCopy

end

end Solidity.Examples.Chains.StorageToMemory
