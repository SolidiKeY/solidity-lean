import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# Memory examples as chains

The calculus's worked memory examples, one namespace each, as a `calc` of
formulas `dl![m]{ … }` for every modality `m` and postcondition `φ`: a printed
`⇝` is `~[r]~>` naming the rule, a printed `⇝*` is `~*>`.

* A program that declares its objects (`Person memory carol;`) is drawn from the
  declaration.  Where the printed trace starts from objects it does not declare,
  the chain starts under the update their declarations leave,
  `{ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }`
  (the printed `new(eMem, ρ) → {carol := id(ρ, [])}{mem := addIdentity(eMem, ρ)}`).
* The rules' fresh names are the printed ones (`acc`, `pv`, `mv`).  A memory
  reference is bound without a value capture where the value is simple
  (`carol.account.balance = 10;`), and `memoryFieldWriteCopy` is one rule where
  the printed trace unfolds a source path into a local.
* Past the program the updates merge (`~[sequentialToParallel]~>`), and a
  read the merge leaves over a fresh object resolves by a law of memory reads
  (`~[readAddEqual]~>`, `EvalLaw`): a refinement of the interpreter, applied
  where the update holds the write it reads back.  Not drawn: the printed
  lines that resolve a read through the identity (`memReadIn`,
  `idConstructor(ρ, [account])`).
-/

namespace Solidity.Examples.Chains.Memory

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Symbolic Execution of Memory Aliasing -/

namespace Aliasing

/-- `Person memory carol; Account memory carolAcc = carol.account;
carolAcc.balance = 100;` — the alias binds the identity `carol.account` holds,
and the write goes through it. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account;
               carolAcc.balance = 100; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖
          carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
          memory := write(addM(memory, Person),
            read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100) } φ } :=
  calc dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account;
                  carolAcc.balance = 100; ]⟩ φ }
    _ ~[memoryReferenceDeclFreshAlloc]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory carolAcc = carol.account; carolAcc.balance = 100; ]⟩ φ } := by
      sol_chain
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ carolAcc = carol.account; carolAcc.balance = 100; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { carolAcc := read(memory, carol.account) } ⟨[ carolAcc.balance = 100; ]⟩ φ } := by
      sol_chain
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                { memory := write(memory, carolAcc.balance, 100) } ⟨[ ]⟩ φ } := by sol_chain
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                { memory := write(memory, carolAcc.balance, 100) } φ } := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain

end Aliasing

/-! ## Example: Symbolic Execution of `carol.account = david.account` -/

namespace FieldCopy

/-- `carol.account = david.account;` — the source is a memory path, so the
identity it holds is written, not a copy.  One rule where the printed trace
unfolds the source into a local `acc` first. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.account = david.account; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖
          david := freshId(addM(addM(memory, Person), Person)) ‖
          memory := write(addM(addM(memory, Person), Person),
            freshId(addM(memory, Person)).account,
            read(addM(addM(memory, Person), Person),
              freshId(addM(addM(memory, Person), Person)).account)) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.account = david.account; ]⟩ φ }
    _ ~[memoryFieldWriteCopy]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.account, read(memory, david.account)) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { memory := write(memory, carol.account, read(memory, david.account)) } φ } := rfl
    _ ~[sequentialToParallel]~> _ := by sol_chain
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
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.account.balance = 10; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖
          acc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
          memory := write(addM(memory, Person),
            read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 10) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.account.balance = 10; ]⟩ φ }
    _ ~[memoryFieldWrite_unfold_leftFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory acc = carol.account; acc.balance = 10; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { acc := read(memory, carol.account) } ⟨[ acc.balance = 10; ]⟩ φ } := by sol_chain
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { acc := read(memory, carol.account) }
                { memory := write(memory, acc.balance, 10) } ⟨[ ]⟩ φ } := by sol_chain
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { acc := read(memory, carol.account) }
                { memory := write(memory, acc.balance, 10) } φ } := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain

end DeepWrite

/-! ## Example: Symbolic Execution of `v = carol.account.balance` -/

namespace FieldRead

def names : FreshTable := [("acc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `v = carol.account.balance;` — the receiver is bound first, then the
member read out of the heap.  The printed `v` is a parameter of the formula. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ v = carol.account.balance; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) ‖
          acc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
          v := 0 } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ v = carol.account.balance; ]⟩ φ }
    _ ~[memoryFieldRead_unfold_rightFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory acc = carol.account; v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ acc = carol.account; v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { acc := read(memory, carol.account) } ⟨[ v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~[memoryFieldReadHeap]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { acc := read(memory, carol.account) } { v := read(memory, acc.balance) } ⟨[ ]⟩ φ } := by
      sol_chain
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { acc := read(memory, carol.account) } { v := read(memory, acc.balance) } φ } := by
      sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[readAddEqual]~> _ := by sol_chain
#last_line chain

end FieldRead

/-! ## Example: Memory Reference Aliasing via Declaration Drop -/

namespace DeclDrop

/-- `Person memory carol; Person memory carolAlias = carol;` — the alias binds
`carol`'s identity, and nothing is written. -/
def chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Person memory carol; Person memory carolAlias = carol; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAlias := carol } φ } :=
  calc dl![m]{ ⟨[ Person memory carol; Person memory carolAlias = carol; ]⟩ φ }
    _ ~[memoryReferenceDeclFreshAlloc]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Person memory carolAlias = carol; ]⟩ φ } := rfl
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ carolAlias = carol; ]⟩ φ } := rfl
    _ ~[memoryRootAlias]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAlias := carol } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAlias := carol } φ } := rfl

end DeclDrop

/-! ## Example: Symbolic Execution of `Token memory t = carol.account.token` -/

namespace TokenAlias

/-- `carolAcc`, the alias of `carol.account`. -/
def names : FreshTable := [("carolAcc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `Token memory t = carol.account.token;` — the declaration dropped, then
each receiver bound by a read of the identity it holds. -/
def chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ Token memory t = carol.account.token; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) } { t := read(memory, carolAcc.token) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ Token memory t = carol.account.token; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ t = carol.account.token; ]⟩ φ } := rfl
    _ ~[memoryFieldRead_unfold_rightFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory carolAcc = carol.account; t = carolAcc.token; ]⟩ φ } := by sol_chain
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ carolAcc = carol.account; t = carolAcc.token; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { carolAcc := read(memory, carol.account) } ⟨[ t = carolAcc.token; ]⟩ φ } := by
      sol_chain
    _ ~[memoryFieldReadAliasRoot]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) } { t := read(memory, carolAcc.token) } ⟨[ ]⟩ φ } :=
      rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) } { t := read(memory, carolAcc.token) } φ } := rfl

end TokenAlias

/-! ## Example: Symbolic Execution of `v = carol` -/

namespace RootAlias

/-- `v = carol;` — a memory local assigned a memory local is rebound to its
identity (`v` is a `Person` by what the program assigns it). -/
def chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ v = carol; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { v := carol } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) } ⟨[ v = carol; ]⟩ φ }
    _ ~[memoryRootAlias]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { v := carol } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { v := carol } φ } := rfl

end RootAlias

/-! ## Example: Symbolic Execution of `carol = david` -/

namespace RootAssign

/-- `carol = david;` — the same rule, with a memory target: `carol` is
rebound to `david`'s identity, and the heap is untouched. -/
def chain (m : Modality) (φ : Post StandardExample) :
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

end RootAssign

/-! ## Example: Additional Memory Write Cases -/

namespace CapturedRhs

/-- `pv`, the captured value. -/
def names : FreshTable := [("pv", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carol.age = a + b;` — a computed value is captured before the write. -/
def chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carol.age = a + b; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { pv := a + b } { memory := write(memory, carol.age, pv) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carol.age = a + b; ]⟩ φ }
    _ ~[memoryFieldWriteUnfoldSource]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ uint pv = a + b; carol.age = pv; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { pv := a + b } ⟨[ carol.age = pv; ]⟩ φ } := by sol_chain
    _ ~[memoryFieldWriteStore]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { pv := a + b } { memory := write(memory, carol.age, pv) } ⟨[ ]⟩ φ } := by sol_chain
    _ ~[emptyModality]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { pv := a + b } { memory := write(memory, carol.age, pv) } φ } := by sol_chain

end CapturedRhs

namespace Rebind

/-- `carolAcc = david.account;` — a memory field on the right rebinds the
local to the identity the member holds. -/
def chain (m : Modality) (φ : Post StandardExample) :
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

end Rebind

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

/-- `choosePersonMem().account = makeAccount();` from the statement to its last
line.  The printed first line is the elaborator's capture (above); a line naming
`mv` numbers the callees past it, so it is not drawn between.  Past it each call is
inlined: `makeAccount`'s body (`mv2`), its result bound (`pv := mv2`),
`choosePersonMem`'s copy of `alice` (`mv4`), bound (`mv := mv4`), and the member
written. -/
def chain (m : Modality) (φ : Post Calls) :
    dl![m]{ ⟨[ choosePersonMem().account = makeAccount(); ]⟩ φ }
    ~*> dl![m]{ { mv2 := freshId(addM(memory, Account)) ‖ memory := addM(memory, Account) }
          { memory := write(memory, mv2.balance, 100) } { pv := mv2 }
          { mv4 := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { mv4 := freshId(copySt(memory, find(storage, alice))) ‖
            memory := copySt(memory, find(storage, alice)) }
          { mv := mv4 } { memory := write(memory, mv.account, pv) } φ } := by
  sol_chain

end CallWrite

end Solidity.Examples.Chains.Memory
