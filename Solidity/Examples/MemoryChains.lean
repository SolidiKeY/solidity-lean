import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# The calculus's memory traces as chains

The derivations of the memory examples,
the memory `delete` examples, the storage-to-memory copies and
memory-to-storage copies, written as the calculus draws them: a `calc`
whose lines are formulas `dl![m]{ … }`, for every modality `m` and
postcondition `φ` (`Examples/Chains.lean` says how to read one).  A `⇝` of
the calculus is a `~[r]~>` naming the rule, a `⇝*` a `~*>`.  Each is a `def`:
the chain is data, and each line is checked against the strategy.  Their
validity, at a postcondition, is `Examples/Memory.lean`'s and
`Examples/CrossDomain.lean`'s.

A memory object is declared by the program (`Person memory carol;`), or,
where the printed trace starts from an object it does not declare
(`carol.account = david.account;`), the chain starts under the update the
declaration leaves,
`{ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }`:
the printed `new(eMem, ρ) → {carol := id(ρ, [])}{mem := addIdentity(eMem, ρ)}`
as one parallel update.  An update binds a memory local under it, and a
program's `carolAcc = carol.account;` (what `memoryLocalDeclInitDrop` leaves of
a declaration) binds one in it (`Calculus/Notation.lean`).

The lines are the strategy's where they differ from the printed ones: the rules'
fresh names (`mv1`, `sp1` for the printed `acc`), a simple value written
without a capture, one rule where the printed trace takes two
(`memoryFieldWriteCopy` for `carol.account = david.account;`), and updates
left as the rules leave them (the printed trace merges them and resolves the reads,
`Theory/`).  The printed `v`, `oldAge`, `oldBal` are left undeclared, as it
leaves them: parameters of the formula, `uint` locals.

The line a storage copy's declaration leaves does not read back: `carol =
alice;` is what `memoryLocalDeclInitDrop` leaves of `Person memory carol =
alice;`, and also what `storageLocalDeclInitDrop` leaves of `Person storage
carol = alice;`, and a line is read on its own, so it reads as the storage
alias (`Calculus/Notation.lean`).  §3's chains go over it with `~*>`.

Not here: the array traces (an allocation of an
array prints `addM(memory)`, which does not read back), the ones through a
call (`choosePersonMem().account = makeAccount();`), and the third delete
trace, whose `carol.account.tokens` `Account` does not have here
(`Examples/Memory.lean`'s docstring).
-/

namespace Solidity.Examples.MemoryChains

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · Memory examples -/

/-- `Person memory carol; Account memory carolAcc = carol.account;
carolAcc.balance = 100;` — the alias binds the identity `carol.account`
holds, and the write goes through it. -/
def aliasing (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account;
               carolAcc.balance = 100; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               { carolAcc := read(memory, carol.account) }
               { memory := write(memory, carolAcc.balance, 100) } φ } :=
  calc dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account;
                  carolAcc.balance = 100; ]⟩ φ }
    _ ~[memoryReferenceDeclFreshAlloc]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory carolAcc = carol.account; carolAcc.balance = 100; ]⟩ φ } := rfl
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ carolAcc = carol.account; carolAcc.balance = 100; ]⟩ φ } := rfl
    _ ~[memoryFieldReadAliasRoot]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) } ⟨[ carolAcc.balance = 100; ]⟩ φ } := rfl
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                { memory := write(memory, carolAcc.balance, 100) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                { memory := write(memory, carolAcc.balance, 100) } φ } := rfl

/-- `carol.account = david.account;` — the source is a memory path: the
identity it holds is written, no copy. -/
def fieldCopy (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.account = david.account; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.account, read(memory, david.account)) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.account = david.account; ]⟩ φ }
    _ ~[memoryFieldWriteCopy]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.account, read(memory, david.account)) } ⟨[ ]⟩ φ } :=
      rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.account, read(memory, david.account)) } φ } := rfl

/-- `carol.account.balance = 10;` — the memory twin of the headline
(`Examples/Chains.lean`): the receiver is bound to a memory local, then
written through. -/
def deepWrite (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.account.balance = 10; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { mv1 := read(memory, carol.account) } { memory := write(memory, mv1.balance, 10) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.account.balance = 10; ]⟩ φ }
    _ ~[memoryFieldWrite_unfold_leftFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory mv1 = carol.account; mv1.balance = 10; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv1 := read(memory, carol.account) } { memory := write(memory, mv1.balance, 10) }
                  φ } := by sol_chain

/-- `v = carol.account.balance;` — the receiver is bound first, then the
member read out of the heap. -/
def fieldRead (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ v = carol.account.balance; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { mv1 := read(memory, carol.account) } { v := read(memory, mv1.balance) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ v = carol.account.balance; ]⟩ φ }
    _ ~[memoryFieldRead_unfold_rightFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory mv1 = carol.account; v = mv1.balance; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv1 := read(memory, carol.account) } { v := read(memory, mv1.balance) } φ } := by
      sol_chain

section
variable (m : Modality) (φ : Post StandardExample)

/-! `Person memory carol; Person memory carolAlias = carol;` — memory
reference aliasing via the declaration drop: the alias binds `carol`'s
identity, and nothing is written. -/

/--
info:     dl{ ⟨[ Person memory carol; Person memory carolAlias = carol; ]⟩ φ }
  ~[memoryReferenceDeclFreshAlloc]~>
    dl{
  { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
    ⟨[ Person memory carolAlias = carol; ]⟩ φ }
  ~[memoryLocalDeclInitDrop]~>
    dl{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ carolAlias = carol; ]⟩ φ }
  ~[memoryRootAlias]~>
    dl{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { carolAlias := carol } ⟨[ ]⟩ φ }
  ~[emptyModality]~>
    dl{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { carolAlias := carol } φ }
-/
#guard_msgs in
#derivation dl![m]{ ⟨[ Person memory carol; Person memory carolAlias = carol; ]⟩ φ }

end

/-- `Token memory t = carol.account.token;` — one selector deeper: each
receiver is bound by a read of the identity it holds. -/
def deepAlias (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ Token memory t = carol.account.token; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { mv1 := read(memory, carol.account) } { t := read(memory, mv1.token) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ Token memory t = carol.account.token; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ t = carol.account.token; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv1 := read(memory, carol.account) } ⟨[ t = mv1.token; ]⟩ φ } := by sol_chain
    _ ~[memoryFieldReadAliasRoot]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { mv1 := read(memory, carol.account) } { t := read(memory, mv1.token) } ⟨[ ]⟩ φ } :=
      rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { mv1 := read(memory, carol.account) } { t := read(memory, mv1.token) } φ } := rfl

/-- `v = carol;` — a memory local assigned a memory local is rebound to its
identity (`v` a `Person` by what the program assigns it). -/
def rootAlias (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ v = carol; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { v := carol } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ v = carol; ]⟩ φ }
    _ ~[memoryRootAlias]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { v := carol } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { v := carol } φ } := rfl

/-- `carol = david;` — the same rule: `carol` now names `david`'s object. -/
def rootAssign (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol = david; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carol := david } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol = david; ]⟩ φ }
    _ ~[memoryRootAlias]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carol := david } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carol := david } φ } := rfl

/-- `carol.age = a + b;` — a computed value is captured before the write. -/
def capturedRhs (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.age = a + b; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { se1 := a + b } { memory := write(memory, carol.age, se1) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.age = a + b; ]⟩ φ }
    _ ~[memoryFieldWriteUnfoldSource]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ uint se1 = a + b; carol.age = se1; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { se1 := a + b } { memory := write(memory, carol.age, se1) } φ } := by sol_chain

/-- `carolAcc = david.account;` — a memory field on the right rebinds the
local to the identity the member holds. -/
def rebind (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            ⟨[ carolAcc = david.account; ]⟩ φ }
    ~*> dl![m]{ { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { carolAcc := read(memory, david.account) } φ } :=
  calc dl![m]{ { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
               ⟨[ carolAcc = david.account; ]⟩ φ }
    _ ~[memoryFieldReadAliasRoot]~>
        dl![m]{ { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { carolAcc := read(memory, david.account) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { carolAcc := read(memory, david.account) } φ } := rfl

/-! ## 2 · Memory delete -/

/-- `Person memory carol; Person memory carolAlias = carol; carol.age = 33;
delete carol; oldAge = carolAlias.age; newAge = carol.age;` — `delete`
rebinds `carol` to a fresh default object, and the alias keeps the old one. -/
def rootDelete (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Person memory carol; Person memory carolAlias = carol; carol.age = 33; delete carol;
               oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAlias := carol } { memory := write(memory, carol.age, 33) }
                { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { oldAge := read(memory, carolAlias.age) } { newAge := read(memory, carol.age) } φ } :=
  calc dl![m]{ ⟨[ Person memory carol; Person memory carolAlias = carol; carol.age = 33; delete carol;
                  oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ }
    _ ~[memoryReferenceDeclFreshAlloc]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Person memory carolAlias = carol; carol.age = 33; delete carol;
                   oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ } := rfl
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ carolAlias = carol; carol.age = 33; delete carol;
                   oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { carolAlias := carol } { memory := write(memory, carol.age, 33) }
                  ⟨[ delete carol; oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ } := by sol_chain
    _ ~[memoryRootDeleteFreshRebind]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAlias := carol } { memory := write(memory, carol.age, 33) }
                { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { carolAlias := carol } { memory := write(memory, carol.age, 33) }
                  { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { oldAge := read(memory, carolAlias.age) } { newAge := read(memory, carol.age) } φ } :=
      by sol_chain

/-- `Person memory carol; Account memory carolAcc = carol.account;
carolAcc.balance = 100; delete carol.account; oldBal = carolAcc.balance;
newBal = carol.account.balance;` — the member gets a fresh default object,
and `carolAcc` keeps the old one. -/
def fieldDeleteRef (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100;
               delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                { memory := write(memory, carolAcc.balance, 100) }
                { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) }
                { oldBal := read(memory, carolAcc.balance) }
                { mv1 := read(memory, carol.account) } { newBal := read(memory, mv1.balance) } φ } :=
  calc dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100;
                  delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { carolAcc := read(memory, carol.account) }
                  { memory := write(memory, carolAcc.balance, 100) }
                  ⟨[ delete carol.account; oldBal = carolAcc.balance;
                     newBal = carol.account.balance; ]⟩ φ } := by sol_chain
    _ ~[memoryFieldDeleteReference]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                { memory := write(memory, carolAcc.balance, 100) }
                { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) }
                ⟨[ oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { carolAcc := read(memory, carol.account) }
                  { memory := write(memory, carolAcc.balance, 100) }
                  { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) }
                  { oldBal := read(memory, carolAcc.balance) }
                  { mv1 := read(memory, carol.account) } { newBal := read(memory, mv1.balance) } φ } :=
      by sol_chain

/-! ## 3 · Storage to memory -/

/-- `alice.age = 25; Person memory carol = alice; v = carol.age;` — the
copy is a fresh object holding a snapshot of `alice`, and the read is a read
of it. -/
def storageCopy (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ alice.age = 25; Person memory carol = alice; v = carol.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 25) }
                { carol := freshId(copySt(memory, find(storage, alice))) ‖
                  memory := copySt(memory, find(storage, alice)) }
                { v := read(memory, carol.age) } φ } :=
  calc dl![m]{ ⟨[ alice.age = 25; Person memory carol = alice; v = carol.age; ]⟩ φ }
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { storage := save(storage, alice.age, 25) }
                ⟨[ Person memory carol = alice; v = carol.age; ]⟩ φ } := rfl
    -- `memoryLocalDeclInitDrop`, `memoryStorageCopy`
    _ ~*> dl![m]{ { storage := save(storage, alice.age, 25) }
                  { carol := freshId(copySt(memory, find(storage, alice))) ‖
                    memory := copySt(memory, find(storage, alice)) }
                  ⟨[ v = carol.age; ]⟩ φ } := by sol_chain
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

/-- `alice.account.balance = 10; Account memory acc = alice.account;
v = acc.balance;` — a member copied: its path is bound to a storage alias
first. -/
def storageFieldCopy (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                { sp2 := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp2))) ‖
                  memory := copySt(memory, find(storage, sp2)) }
                { v := read(memory, acc.balance) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    _ ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                  ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ } := by sol_chain
    -- `memoryLocalDeclInitDrop`, `memoryStorageCopyUnfold` (`acc = sp2;`, `sp2` bound to
    -- `alice.account`), `memoryStorageCopy`
    _ ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                  { sp2 := alice.account }
                  { acc := freshId(copySt(memory, find(storage, sp2))) ‖
                    memory := copySt(memory, find(storage, sp2)) }
                  ⟨[ v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~[memoryFieldReadHeap]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                { sp2 := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp2))) ‖
                  memory := copySt(memory, find(storage, sp2)) }
                { v := read(memory, acc.balance) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                { sp2 := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp2))) ‖
                  memory := copySt(memory, find(storage, sp2)) }
                { v := read(memory, acc.balance) } φ } := rfl

/-! ## 4 · Memory to storage -/

/-- `carol.age = 42; alice = carol; v = alice.age;` — a memory object
copied into a storage root (`copyMem`), and read back from storage. -/
def memoryCopy (m : Modality) (φ : Post StandardExample) :
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

/-- `carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance;`
— into a member of a storage root. -/
def memoryFieldCopy (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            ⟨[ carolAcc.balance = 50; alice.account = carolAcc; v = alice.account.balance; ]⟩ φ }
    ~*> dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                { memory := write(memory, carolAcc.balance, 50) }
                { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
                { sp1 := alice.account } { v := find(storage, sp1.balance) } φ } :=
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
    _ ~*> dl![m]{ { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
                  { memory := write(memory, carolAcc.balance, 50) }
                  { storage := save(storage, alice.account, copyMem(mtSt, memory, carolAcc)) }
                  { sp1 := alice.account } { v := find(storage, sp1.balance) } φ } := by sol_chain

/-- `carol.account.balance = 50; alice.account = carol.account;
v = alice.account.balance;` — the source a member of a memory object: the
identity it holds is what is copied. -/
def memoryPathCopy (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.account.balance = 50; alice.account = carol.account; v = alice.account.balance; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { mv1 := read(memory, carol.account) } { memory := write(memory, mv1.balance, 50) }
                { storage := save(storage, alice.account, copyMem(mtSt, memory, read(memory, carol.account))) }
                { sp2 := alice.account } { v := find(storage, sp2.balance) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.account.balance = 50; alice.account = carol.account;
                  v = alice.account.balance; ]⟩ φ }
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv1 := read(memory, carol.account) } { memory := write(memory, mv1.balance, 50) }
                  ⟨[ alice.account = carol.account; v = alice.account.balance; ]⟩ φ } := by sol_chain
    _ ~[memoryToStorageFieldCopyRoot]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { mv1 := read(memory, carol.account) } { memory := write(memory, mv1.balance, 50) }
                { storage := save(storage, alice.account,
                    copyMem(mtSt, memory, read(memory, carol.account))) }
                ⟨[ v = alice.account.balance; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv1 := read(memory, carol.account) } { memory := write(memory, mv1.balance, 50) }
                  { storage := save(storage, alice.account,
                      copyMem(mtSt, memory, read(memory, carol.account))) }
                  { sp2 := alice.account } { v := find(storage, sp2.balance) } φ } := by sol_chain

end Solidity.Examples.MemoryChains
