import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# The calculus's memory traces as chains

The derivations of the memory examples,
the memory `delete` examples, the storage-to-memory copies,
the memory-to-storage copies and the memory arrays,
written as drawn there: a `calc`
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

The line a storage copy's declaration leaves, `carol = alice;`, is also what
`storageLocalDeclInitDrop` leaves of `Person storage carol = alice;`; a line
is read on its own, so it says which: `… where Person memory carol`, as it
prints (`Calculus/Notation.lean`).

Not here: the traces through a call (`choosePersonMem().account =
makeAccount();`, `carolValues[i] = makeValue();`, `Examples/CallOperands.lean`),
and those through `carol.account.tokens` or `carol.account.values`, members
`Account` does not have here (`Examples/Memory.lean`'s docstring).
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
of it.  The line the declaration leaves says `carol` is a memory local. -/
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

/-- `Account memory acc = alice.account;` after `alice.account.balance = 10;`:
the declaration dropped, and the member's path bound to a storage alias
(`sp2`, printed `sp`). -/
def storageFieldAlias (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
            ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                { sp2 := alice.account } ⟨[ acc = sp2; v = acc.balance; ]⟩ φ where Account memory acc } :=
  calc dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
               ⟨[ Account memory acc = alice.account; v = acc.balance; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                ⟨[ acc = alice.account; v = acc.balance; ]⟩ φ where Account memory acc } := rfl
    _ ~[memoryStorageCopyUnfold]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                ⟨[ Account storage sp2 = alice.account; acc = sp2; v = acc.balance; ]⟩ φ
                where Account memory acc } := by sol_chain
    _ ~[storageLocalDeclInitDrop]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                ⟨[ sp2 = alice.account; acc = sp2; v = acc.balance; ]⟩ φ where Account memory acc } := rfl
    _ ~[storageFieldReadBindLocalRoot]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                { sp2 := alice.account } ⟨[ acc = sp2; v = acc.balance; ]⟩ φ where Account memory acc } :=
      rfl

/-- … then `acc` a copy of the object `sp2` names, and `v = acc.balance;` a
read of the copy. -/
def storageFieldRead (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
            { sp2 := alice.account } ⟨[ acc = sp2; v = acc.balance; ]⟩ φ where Account memory acc }
    ~*> dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                { sp2 := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp2))) ‖
                  memory := copySt(memory, find(storage, sp2)) }
                { v := read(memory, acc.balance) } φ } :=
  calc dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
               { sp2 := alice.account } ⟨[ acc = sp2; v = acc.balance; ]⟩ φ where Account memory acc }
    _ ~[memoryStorageCopy]~>
        dl![m]{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
                { sp2 := alice.account }
                { acc := freshId(copySt(memory, find(storage, sp2))) ‖
                  memory := copySt(memory, find(storage, sp2)) }
                ⟨[ v = acc.balance; ]⟩ φ } := rfl
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

/-- `alice.account.balance = 10; Account memory acc = alice.account;
v = acc.balance;` — a member copied: the write, then `storageFieldAlias` and
`storageFieldRead`.  One `calc` of the eleven lines is past the heartbeat
budget: each line is read at compile time (`elabAgainst`). -/
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
    _ ~*> _ := (storageFieldAlias m φ).trans (storageFieldRead m φ)

/-- `Token memory t = alice.account.token;` — a nonsimple source is aliased
(`sp1`, printed `aliceTok`), and the alias resolved one selector at a
time. -/
def storageDeepCopy (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    ~*> dl![m]{ { sp2 := alice.account } { sp1 := sp2.token }
                { t := freshId(copySt(memory, find(storage, sp1))) ‖
                  memory := copySt(memory, find(storage, sp1)) } φ } :=
  calc dl![m]{ ⟨[ Token memory t = alice.account.token; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ ⟨[ t = alice.account.token; ]⟩ φ where Token memory t } := rfl
    _ ~[memoryStorageCopyUnfold]~>
        dl![m]{ ⟨[ Token storage sp1 = alice.account.token; t = sp1; ]⟩ φ where Token memory t } :=
      by sol_chain
    _ ~*> dl![m]{ { sp2 := alice.account } { sp1 := sp2.token } ⟨[ t = sp1; ]⟩ φ
                  where Token memory t } := by sol_chain
    _ ~[memoryStorageCopy]~>
        dl![m]{ { sp2 := alice.account } { sp1 := sp2.token }
                { t := freshId(copySt(memory, find(storage, sp1))) ‖
                  memory := copySt(memory, find(storage, sp1)) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { sp2 := alice.account } { sp1 := sp2.token }
                { t := freshId(copySt(memory, find(storage, sp1))) ‖
                  memory := copySt(memory, find(storage, sp1)) } φ } := rfl

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


/-! ## 5 · Memory arrays

The arrays are allocated as `uint[] memory carolValues;` leaves them,
`addM(memory, uint[])`.  A read or a write of an element takes no bounds
branch here: an index out of range halts the read (`Term.read` is undefined
there), where the printed trace splits on `0 ≤ i < ℓ`.  A nonsimple index is
captured by the elaborator (`uint se1; se1 = ++i;`), so the printed first
line is the formula it writes. -/

/-- `v = carolValues[i];` -/
def indexRead (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[i]; ]⟩ φ }
    ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { v := read(memory, carolValues[i]) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[i]; ]⟩ φ }
    _ ~[memoryIndexReadHeap]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { v := read(memory, carolValues[i]) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { v := read(memory, carolValues[i]) } φ } := rfl

/-- `carolValues[i] = 100;` -/
def indexWrite (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[i] = 100; ]⟩ φ }
    ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { memory := write(memory, carolValues[i], 100) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[i] = 100; ]⟩ φ }
    _ ~[memoryIndexWriteStore]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { memory := write(memory, carolValues[i], 100) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { memory := write(memory, carolValues[i], 100) } φ } := rfl

/-- `v = carolValues[++i];` — the index captured, then read at. -/
def indexReadCaptured (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[++i]; ]⟩ φ }
    ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } { v := read(memory, carolValues[se1]) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[++i]; ]⟩ φ }
    _ = dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ uint se1; se1 = ++i; v = carolValues[se1]; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } ⟨[ v = carolValues[se1]; ]⟩ φ } := by sol_chain
    _ ~[memoryIndexReadHeap]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } { v := read(memory, carolValues[se1]) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } { v := read(memory, carolValues[se1]) } φ } := rfl

/-- `carolValues[++i] = val;` — the right-hand side is snapshot before the
index runs (`se1`, printed `pv`); the receiver, simple, is not re-aliased
(printed `mv1`, `Examples/CallOperands.lean`). -/
def indexWriteCaptured (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[++i] = val; ]⟩ φ }
    ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
                { memory := write(memory, carolValues[se2], se1) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[++i] = val; ]⟩ φ }
    _ = dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ uint se1 = val; uint se2; se2 = ++i; carolValues[se2] = se1; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
                  ⟨[ carolValues[se2] = se1; ]⟩ φ } := by sol_chain
    _ ~[memoryIndexWriteStore]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
                { memory := write(memory, carolValues[se2], se1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se1 := val } { se2 := 0 } { i := i + 1 ‖ se2 := i + 1 }
                { memory := write(memory, carolValues[se2], se1) } φ } := rfl

/-- `carolTokens[i] = david.account.token;` — the source's receiver bound
(`mv1`), and the element written with the identity the member holds (the
printed `tok`). -/
def elementFromField (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ carolTokens[i] = david.account.token; ]⟩ φ }
    ~*> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { mv1 := read(memory, david.account) }
                { memory := write(memory, carolTokens[i], read(memory, mv1.token)) } φ } :=
  calc dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ carolTokens[i] = david.account.token; ]⟩ φ }
    _ ~[memoryFieldRead_unfold_rightFst]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ Account memory mv1 = david.account; carolTokens[i] = mv1.token; ]⟩ φ } :=
      by sol_chain
    _ ~*> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { mv1 := read(memory, david.account) } ⟨[ carolTokens[i] = mv1.token; ]⟩ φ } :=
      by sol_chain
    _ ~[memoryIndexWriteCopy]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { mv1 := read(memory, david.account) }
                { memory := write(memory, carolTokens[i], read(memory, mv1.token)) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { mv1 := read(memory, david.account) }
                { memory := write(memory, carolTokens[i], read(memory, mv1.token)) } φ } := rfl

/-- `carol.account.token = davidTokens[i];` — the target's receiver bound
(`mv1`), and the member written with the element's
identity. -/
def fieldFromElement (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ carol.account.token = davidTokens[i]; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { mv1 := read(memory, carol.account) }
                { memory := write(memory, mv1.token, read(memory, davidTokens[i])) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ carol.account.token = davidTokens[i]; ]⟩ φ }
    _ ~[memoryFieldWrite_unfold_leftFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ Account memory mv1 = carol.account; mv1.token = davidTokens[i]; ]⟩ φ } :=
      by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { mv1 := read(memory, carol.account) } ⟨[ mv1.token = davidTokens[i]; ]⟩ φ } :=
      by sol_chain
    _ ~[memoryFieldWriteCopy]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { mv1 := read(memory, carol.account) }
                { memory := write(memory, mv1.token, read(memory, davidTokens[i])) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { mv1 := read(memory, carol.account) }
                { memory := write(memory, mv1.token, read(memory, davidTokens[i])) } φ } := rfl

/-- `Token memory tok = carolTokens[++i];` — the index captured, the
declaration dropped, and `tok` bound to the element's identity. -/
def elementAlias (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ Token memory tok = carolTokens[++i]; ]⟩ φ }
    ~*> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } { tok := read(memory, carolTokens[se1]) } φ } :=
  calc dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ Token memory tok = carolTokens[++i]; ]⟩ φ }
    _ = dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ uint se1; se1 = ++i; Token memory tok = carolTokens[se1]; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } ⟨[ Token memory tok = carolTokens[se1]; ]⟩ φ } := by sol_chain
    _ ~[memoryLocalDeclInitDrop]~> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } ⟨[ tok = carolTokens[se1]; ]⟩ φ } := rfl
    _ ~[memoryIndexReadAliasRoot]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } { tok := read(memory, carolTokens[se1]) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { se1 := 0 } { i := i + 1 ‖ se1 := i + 1 } { tok := read(memory, carolTokens[se1]) } φ } := rfl

end Solidity.Examples.MemoryChains
