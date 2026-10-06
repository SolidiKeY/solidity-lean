import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# Memory examples as chains

The calculus's worked memory examples, in order, each one chain term over any modality `m` and
postcondition `φ` (`Examples/Chains/Storage.lean` says how to read one), in the printed names
(`FreshNames` tables: `acc`, `pv`, `mv`).

* A program that declares its objects (`Person memory carol;`) is drawn from the declaration.  Where
  the printed trace starts from objects it does not declare, the first line puts in front of the
  program the update their declarations leave,
  `{ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }` (the printed
  `new(eMem, ρ) → {carol := id(ρ, [])}{mem := addIdentity(eMem, ρ)}`); a free parameter (`a`, `b`),
  a member the program reads (`carol.account.balance`) and the storage it copies (`alice`) get a
  concrete value there too.
* A memory reference is bound without a value capture where the value is simple
  (`carol.account.balance = 10;`), and `memoryFieldWriteCopy` is one rule where the printed trace
  unfolds a source path into a local.
* Past the program the stack merges (`~[sequentialToParallel]~>`) and each read is resolved by a law
  of memory reads (`readWriteDifferentIdentity`, `readOnWrite`, `readAddDifferentIdentity`,
  `EvalLaw`), one link each, every capture kept to the last line, which `#last_line` checks.  Not
  drawn: the printed lines that resolve a read through the identity (`memReadIn`,
  `idConstructor(ρ, [account])`), for which there is no law.
-/

namespace Solidity.Examples.Chains.Memory

local instance : InContract := ⟨StandardExample⟩

section
variable (m : Modality) (φ : Post StandardExample)

/-! ## Example: Symbolic Execution of Memory Aliasing -/

namespace Aliasing

/-- `Person memory carol; Account memory carolAcc = carol.account;
carolAcc.balance = 100;` — the alias binds the identity `carol.account` holds,
and the write goes through it.  The last line keeps the read of that identity:
no law reads a struct member of a fresh object to its identity (the printed
`idConstructor(ρ, [account])`). -/
theorem chain :
    dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100; ]⟩ φ }
    ~[memoryReferenceDeclFreshAlloc]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ Account memory carolAcc = carol.account; carolAcc.balance = 100; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ carolAcc = carol.account; carolAcc.balance = 100; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) } ⟨[ carolAcc.balance = 100; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) } { memory := write(memory, carolAcc.balance, 100) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100) }
          φ } := by
  sol_chain
#last_line chain

end Aliasing

/-! ## Example: Symbolic Execution of `carol.account = david.account` -/

namespace FieldCopy

/-- `carol.account = david.account;` — the source is a memory path, so the
identity it holds is written, not a copy.  One rule where the printed trace
unfolds the source into a local `acc` first, so the paper's `⇝` and `⇝*` are one
`~*>`. -/
theorem chain :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ carol.account = david.account; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            { memory := write(memory, carol.account, read(memory, david.account)) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ david := freshId(addM(addM(memory, Person), Person)) ‖
            memory :=
              write(addM(addM(memory, Person), Person), freshId(addM(memory, Person)).account,
                read(addM(addM(memory, Person), Person), freshId(addM(addM(memory, Person), Person)).account)) }
          φ } := by
  sol_chain
#last_line chain

end FieldCopy

/-! ## Example: Symbolic Execution of `carol.account.balance = 10` -/

namespace DeepWrite

/-- `acc`, the alias of `carol.account`. -/
def names : FreshTable := [("acc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carol.account.balance = 10;` — the receiver is bound to a memory local
`acc`, then written through.  The value `10` is simple, so no `pv` is declared. -/
theorem chain :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ carol.account.balance = 10; ]⟩ φ }
    ~[memoryFieldWrite_unfold_leftFst]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ Account memory acc = carol.account; acc.balance = 10; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { acc := read(memory, carol.account) } ⟨[ acc.balance = 10; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { acc := read(memory, carol.account) } { memory := write(memory, acc.balance, 10) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ acc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10) }
          φ } := by
  sol_chain
#last_line chain

end DeepWrite

/-! ## Example: Symbolic Execution of `v = carol.account.balance` -/

namespace FieldRead

def names : FreshTable := [("acc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `v = carol.account.balance;` from a memory where it is 10 — the receiver is
bound first, then the member read out of the heap.  Past the merge the read of
`carol.account` passes the write to `balance` (`readWriteDifferentIdentity`),
and the member read is that write's value (`readOnWrite`). -/
theorem chain :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        { memory := write(memory, read(memory, carol.account).balance, 10) } ⟨[ v = carol.account.balance; ]⟩ φ }
    ~[memoryFieldRead_unfold_rightFst]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { memory := write(memory, read(memory, carol.account).balance, 10) }
            ⟨[ Account memory acc = carol.account; v = acc.balance; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { memory := write(memory, read(memory, carol.account).balance, 10) }
            ⟨[ acc = carol.account; v = acc.balance; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { memory := write(memory, read(memory, carol.account).balance, 10) }
            { acc := read(memory, carol.account) } ⟨[ v = acc.balance; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { memory := write(memory, read(memory, carol.account).balance, 10) }
            { acc := read(memory, carol.account) } { v := read(memory, acc.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10) ‖
            acc :=
              read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10),
                freshId(addM(memory, Person)).account) ‖
            v :=
              read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10),
                read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                      10),
                    freshId(addM(memory, Person)).account).balance) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10) ‖
            acc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            v :=
              read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10),
                read(addM(memory, Person), freshId(addM(memory, Person)).account).balance) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            memory :=
              write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10) ‖
            acc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖ v := 10 }
          φ } := by
  sol_chain
#last_line chain

end FieldRead

/-! ## Example: Memory Reference Aliasing via Declaration Drop -/

namespace DeclDrop

/-- `Person memory carol; Person memory carolAlias = carol;` — the alias binds
`carol`'s identity, and nothing is written. -/
theorem chain :
    dl![m]{ ⟨[ Person memory carol; Person memory carolAlias = carol; ]⟩ φ }
    ~[memoryReferenceDeclFreshAlloc]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ Person memory carolAlias = carol; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ carolAlias = carol; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { carolAlias := carol } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
            carolAlias := freshId(addM(memory, Person)) }
          φ } := by
  sol_chain
#last_line chain

end DeclDrop

/-! ## Example: Symbolic Execution of `Token memory t = carol.account.token` -/

namespace TokenAlias

/-- `carolAcc`, the alias of `carol.account`. -/
def names : FreshTable := [("carolAcc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `Token memory t = carol.account.token;` — the declaration dropped, then
each receiver bound by a read of the identity it holds.  As in `Aliasing`, no
law reads a member of the fresh `carol` to its identity. -/
theorem chain :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        ⟨[ Token memory t = carol.account.token; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ t = carol.account.token; ]⟩ φ }
    ~[memoryFieldRead_unfold_rightFst]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ Account memory carolAcc = carol.account; t = carolAcc.token; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ carolAcc = carol.account; t = carolAcc.token; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) } ⟨[ t = carolAcc.token; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) } { t := read(memory, carolAcc.token) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            t := read(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).token) }
          φ } := by
  sol_chain
#last_line chain

end TokenAlias

/-! ## Example: Symbolic Execution of `v = carol` -/

namespace RootAlias

/-- `v = carol;` — a memory local assigned a memory local is rebound to its
identity (`v` is a `Person` by what the program assigns it). -/
theorem chain :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ v = carol; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { v := carol } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖ v := freshId(addM(memory, Person)) } φ } := by
  sol_chain
#last_line chain

end RootAlias

/-! ## Example: Symbolic Execution of `carol = david` -/

namespace RootAssign

/-- `carol = david;` — the same rule, with a memory target: `carol` is
rebound to `david`'s identity, and the heap is untouched. -/
theorem chain :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ carol = david; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } { carol := david } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ david := freshId(addM(addM(memory, Person), Person)) ‖
            memory := addM(addM(memory, Person), Person) ‖ carol := freshId(addM(addM(memory, Person), Person)) }
          φ } := by
  sol_chain
#last_line chain

end RootAssign

/-! ## Example: Additional Memory Write Cases -/

namespace CapturedRhs

/-- `pv`, the captured value. -/
def names : FreshTable := [("pv", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carol.age = a + b;` with `a` 3 and `b` 4 — a computed value is captured
before the write; the paper's one `⇝*` declares, binds and writes it.  The sum
folds to `7` in `pv` and in the write at once (`add_literals`, which rewrites
inside a memory term too). -/
theorem chain :
    dl![m]{
      { a := 3 ‖ b := 4 ‖ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        ⟨[ carol.age = a + b; ]⟩ φ }
    ~[memoryFieldWriteUnfoldSource]~> dl![m]{
        { a := 3 ‖ b := 4 ‖ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ uint pv = a + b; carol.age = pv; ]⟩ φ }
    ~*> dl![m]{
        { a := 3 ‖ b := 4 ‖ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { pv := a + b } { memory := write(memory, carol.age, pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { a := 3 ‖ b := 4 ‖ carol := freshId(addM(memory, Person)) ‖ pv := 3 + 4 ‖
            memory := write(addM(memory, Person), freshId(addM(memory, Person)).age, 3 + 4) }
          φ }
    ~[add_literals]~> dl![m]{
        { a := 3 ‖ b := 4 ‖ carol := freshId(addM(memory, Person)) ‖ pv := 7 ‖
            memory := write(addM(memory, Person), freshId(addM(memory, Person)).age, 7) }
          φ } := by
  sol_chain
#last_line chain

end CapturedRhs

namespace Rebind

/-- `carolAcc = david.account;` — a memory field on the right rebinds the
local to the identity the member holds; past the merge the read passes the
later allocation of `carolAcc`'s object (`readAddDifferentIdentity`). -/
theorem chain :
    dl![m]{
      { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) } ⟨[ carolAcc = david.account; ]⟩ φ }
    ~*> dl![m]{
        { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { carolAcc := read(memory, david.account) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { david := freshId(addM(memory, Person)) ‖ carolAcc := freshId(addM(addM(memory, Person), Account)) ‖
            memory := addM(addM(memory, Person), Account) ‖
            carolAcc := read(addM(addM(memory, Person), Account), freshId(addM(memory, Person)).account) }
          φ }
    ~[readAddDifferentIdentity]~> dl![m]{
        { david := freshId(addM(memory, Person)) ‖ carolAcc := freshId(addM(addM(memory, Person), Account)) ‖
            memory := addM(addM(memory, Person), Account) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) }
          φ } := by
  sol_chain
#last_line chain

end Rebind

end

namespace CallWrite

/-- `makeAccount` writes its named return variable; `choosePersonMem` returns a
copy of the state variable `alice`. -/
def Calls : Contract := contract!{
  Person alice;
  function makeAccount() returns (Account memory a) { a.balance = 100; }
  function choosePersonMem() returns (Person memory) { return alice; }
}

local instance : InContract := ⟨Calls⟩

/-- `pv` the captured value, `mv` the captured receiver. -/
def names : FreshTable := [("pv", "mv1"), ("mv", "mv3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Calls names).isEmpty

/-- The printed first line: the right-hand side, then the receiver, captured. -/
example : Prog.toStr (sol[Calls]{ choosePersonMem().account = makeAccount(); } : Prog Calls) =
    "Account memory pv = makeAccount(); Person memory mv = choosePersonMem(); mv.account = pv;" :=
  rfl

/-- `choosePersonMem().account = makeAccount();` from a storage where `alice.age`
is 10, to its last line.  The program is the elaborator's capture (above), the
paper's only printed step.  Past it each call is inlined (`functionBodyExpand`):
`makeAccount`'s object allocated (`mv2`) and written, its result bound
(`pv := mv2`); `choosePersonMem`'s object allocated (`mv4`) and overwritten by
a copy of `alice` (`memoryStorageCopy`), bound (`mv := mv4`); and the member
written.  The copy reads `alice` as a struct, which has no literal: nothing
reads a member of it in the last line. -/
theorem chain (m : Modality) (φ : Post Calls) :
    dl![m]{ { storage := save(storage, alice.age, 10) } ⟨[ choosePersonMem().account = makeAccount(); ]⟩ φ }
    ~[functionBodyExpand]~> dl![m]{
        { storage := save(storage, alice.age, 10) }
          ⟨[ Account memory mv2; mv2.balance = 100; Account memory pv = mv2; Person memory mv = choosePersonMem();
            mv.account = pv; ]⟩ φ }
    ~[memoryReferenceDeclFreshAlloc]~> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            ⟨[ mv2.balance = 100; Account memory pv = mv2; Person memory mv = choosePersonMem(); mv.account = pv; ]⟩ φ }
    ~[memoryFieldWrite]~> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { memory := write(memory, mv2.balance, 100) }
              ⟨[ Account memory pv = mv2; Person memory mv = choosePersonMem(); mv.account = pv; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { memory := write(memory, mv2.balance, 100) }
              { pv := mv2 } ⟨[ Person memory mv = choosePersonMem(); mv.account = pv; ]⟩ φ }
    ~[functionBodyExpand]~> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { memory := write(memory, mv2.balance, 100) }
              { pv := mv2 } ⟨[ Person memory mv4; mv4 = alice; Person memory mv = mv4; mv.account = pv; ]⟩ φ }
    ~[memoryReferenceDeclFreshAlloc]~> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { memory := write(memory, mv2.balance, 100) }
              { pv := mv2 }
                { mv4 := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  ⟨[ mv4 = alice; Person memory mv = mv4; mv.account = pv; ]⟩ φ }
    ~[memoryStorageCopy]~> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { memory := write(memory, mv2.balance, 100) }
              { pv := mv2 }
                { mv4 := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv4 := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
                    ⟨[ Person memory mv = mv4; mv.account = pv; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { memory := write(memory, mv2.balance, 100) }
              { pv := mv2 }
                { mv4 := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv4 := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
                    { mv := mv4 } ⟨[ mv.account = pv; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, alice.age, 10) }
          { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
            { memory := write(memory, mv2.balance, 100) }
              { pv := mv2 }
                { mv4 := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { mv4 := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
                    { mv := mv4 } { memory := write(memory, mv.account, pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, alice.age, 10) ‖ mv2 := freshId(addM(memory, Account)) ‖
            pv := freshId(addM(memory, Account)) ‖
            mv4 := freshId(addM(write(addM(memory, Account), freshId(addM(memory, Account)).balance, 100), Person)) ‖
            mv4 :=
              freshId(copySt(addM(write(addM(memory, Account), freshId(addM(memory, Account)).balance, 100), Person),
                  find(save(storage, alice.age, 10), alice))) ‖
            mv :=
              freshId(copySt(addM(write(addM(memory, Account), freshId(addM(memory, Account)).balance, 100), Person),
                  find(save(storage, alice.age, 10), alice))) ‖
            memory :=
              write(copySt(addM(write(addM(memory, Account), freshId(addM(memory, Account)).balance, 100), Person),
                  find(save(storage, alice.age, 10), alice)),
                freshId(copySt(addM(write(addM(memory, Account), freshId(addM(memory, Account)).balance, 100), Person),
                      find(save(storage, alice.age, 10), alice))).account,
                freshId(addM(memory, Account))) }
          φ } := by
  sol_chain
#last_line chain

end CallWrite

end Solidity.Examples.Chains.Memory
