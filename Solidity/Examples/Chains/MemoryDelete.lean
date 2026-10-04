import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The memory `delete` examples as chains

The calculus's memory `delete` examples, each one chain term over any modality `m` and postcondition `φ`
(`Examples/Chains/Storage.lean` says how to read one).  A `delete` of an identity rebinds the root, or
writes a fresh default object into the field or element; the alias keeps the old identity.

* The strategy's runs are grouped as the paper prints them.  The printed trace drops the second
  declaration first; the strategy allocates the first object before it (`memoryReferenceDeclFreshAlloc`),
  so the printed first `⇝` is that allocation here, and the drop is in the `⇝*` after it.
* Past the merge each read is resolved by a law of memory reads (`readAddEqual`, `readAddDifferent`,
  `readOnWrite`, `readWriteDifferent` and their identity forms), one link each, every capture kept, to the
  printed `33` and `0`, `100` and `0`, `9` and `0`.  The aliases keep their reads of a fresh object's
  member (`carolAcc`, `toks`, `tk`): no law reads that to its identity (the printed
  `idConstructor(ρ, [account])`).  The element `[1 + 1]` folds to `[2]` with `i`, in every memory
  term it stands in.
* The indexed delete is stated in `TestSuite`, where `Account` has no `tokens`: a
  `TokenBucket memory b` stands for `carol` and its `b.tokens` for `carol.account.tokens`, one selector
  shorter; `tk` stands for `tok`.  The printed `delete toks[i]` is `delete b.tokens[i]`, its array bound
  again by the rules (`mv3`), and so is the last read's (`mv5`, `mv4`).  Its first line puts `b`'s
  declaration and `i` 1 in front of the program; the other two declare their objects and read nothing
  written before them, so they start from the program alone.
-/

namespace Solidity.Examples.Chains.MemoryDelete

/-! ## Example: Memory Delete Cases -/

section
local instance : InContract := ⟨StandardExample⟩
variable (m : Modality) (φ : Post StandardExample)

namespace RootDelete

/-- `Person memory carol; Person memory carolAlias = carol; carol.age = 33;
delete carol; oldAge = carolAlias.age; newAge = carol.age;` — `carol` allocated (the paper's first `⇝`,
the module docstring says why), the run to the delete (`⇝*`),
`delete` rebinding `carol` to a fresh default object (`⇝`), the two reads (`⇝*`) and the merge.  The
alias keeps the old object: `newAge` reads the fresh one, the default `0` (`readAddEqual`); `oldAge` reads
past that allocation (`readAddDifferent`) the write, `33` (`readOnWrite`). -/
theorem chain :
    dl![m]{
      ⟨[ Person memory carol; Person memory carolAlias = carol; carol.age = 33; delete carol; oldAge = carolAlias.age;
        newAge = carol.age; ]⟩ φ }
    ~[memoryReferenceDeclFreshAlloc]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ Person memory carolAlias = carol; carol.age = 33; delete carol; oldAge = carolAlias.age; newAge = carol.age; ]⟩
            φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAlias := carol }
            { memory := write(memory, carol.age, 33) } ⟨[ delete carol; oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ }
    ~[memoryRootDeleteFreshRebind]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAlias := carol }
            { memory := write(memory, carol.age, 33) }
              { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAlias := carol }
            { memory := write(memory, carol.age, 33) }
              { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { oldAge := read(memory, carolAlias.age) } { newAge := read(memory, carol.age) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ carolAlias := freshId(addM(memory, Person)) ‖
            carol := freshId(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person)) ‖
            memory := addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person) ‖
            oldAge :=
              read(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person),
                freshId(addM(memory, Person)).age) ‖
            newAge :=
              read(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person),
                freshId(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person)).age) }
          φ }
    ~[readAddEqual]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ carolAlias := freshId(addM(memory, Person)) ‖
            carol := freshId(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person)) ‖
            memory := addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person) ‖
            oldAge :=
              read(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person),
                freshId(addM(memory, Person)).age) ‖
            newAge := 0 }
          φ }
    ~[readAddDifferent]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ carolAlias := freshId(addM(memory, Person)) ‖
            carol := freshId(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person)) ‖
            memory := addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person) ‖
            oldAge :=
              read(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), freshId(addM(memory, Person)).age) ‖
            newAge := 0 }
          φ }
    ~[readOnWrite]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ carolAlias := freshId(addM(memory, Person)) ‖
            carol := freshId(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person)) ‖
            memory := addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person) ‖ oldAge := 33 ‖
            newAge := 0 }
          φ } := by
  sol_chain
#last_line chain

end RootDelete

namespace FieldDeleteRef

/-- `acc`, the receiver of the last read. -/
def names : FreshTable := [("acc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100;
delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance;` run: `carol` allocated (the
paper's first `⇝`), to the delete (`⇝*`), `delete` writing a fresh default `Account` into `carol.account` (`⇝`), the two reads
(`⇝*`), the merge, and `acc`, read at `carol.account`, the fresh object the delete wrote there
(`readOnWriteIdentity`). -/
theorem run :
    dl![m]{
      ⟨[ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100; delete carol.account;
        oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    ~[memoryReferenceDeclFreshAlloc]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ Account memory carolAcc = carol.account; carolAcc.balance = 100; delete carol.account; oldBal = carolAcc.balance;
            newBal = carol.account.balance; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) }
            { memory := write(memory, carolAcc.balance, 100) }
              ⟨[ delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    ~[memoryFieldDeleteReference]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) }
            { memory := write(memory, carolAcc.balance, 100) }
              { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) }
                ⟨[ oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    ~*> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { carolAcc := read(memory, carol.account) }
            { memory := write(memory, carolAcc.balance, 100) }
              { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) }
                { oldBal := read(memory, carolAcc.balance) }
                  { acc := read(memory, carol.account) } { newBal := read(memory, acc.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))) ‖
            oldBal :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                read(addM(memory, Person), freshId(addM(memory, Person)).account).balance) ‖
            acc :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                freshId(addM(memory, Person)).account) ‖
            newBal :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                read(write(addM(write(addM(memory, Person),
                          read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                        Account),
                      freshId(addM(memory, Person)).account,
                      freshId(addM(write(addM(memory, Person),
                            read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                          Account))),
                    freshId(addM(memory, Person)).account).balance) }
          φ }
    ~[readOnWriteIdentity]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))) ‖
            oldBal :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                read(addM(memory, Person), freshId(addM(memory, Person)).account).balance) ‖
            acc :=
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account)) ‖
            newBal :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account)).balance) }
          φ } := by
  sol_chain

/-- The rest of `FieldDeleteRef.run`: `oldBal` read past the delete's write and allocation
(`readWriteDifferent`, `readAddDifferent`) to the write through `carolAcc`, `100`; `newBal`, `acc`'s
`balance`, past the delete's write to the fresh object's default, `0` (`readAddEqual`). -/
theorem reads :
    dl![m]{
      { carol := freshId(addM(memory, Person)) ‖
          carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
          memory :=
            write(addM(write(addM(memory, Person),
                  read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                Account),
              freshId(addM(memory, Person)).account,
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account))) ‖
          oldBal :=
            read(write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))),
              read(addM(memory, Person), freshId(addM(memory, Person)).account).balance) ‖
          acc :=
            freshId(addM(write(addM(memory, Person),
                  read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                Account)) ‖
          newBal :=
            read(write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))),
              freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account)).balance) }
        φ }
    ~[readWriteDifferent]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))) ‖
            oldBal :=
              read(addM(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                    100),
                  Account),
                read(addM(memory, Person), freshId(addM(memory, Person)).account).balance) ‖
            acc :=
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account)) ‖
            newBal :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account)).balance) }
          φ }
    ~[readAddDifferent]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))) ‖
            oldBal :=
              read(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                  100),
                read(addM(memory, Person), freshId(addM(memory, Person)).account).balance) ‖
            acc :=
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account)) ‖
            newBal :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account)).balance) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))) ‖
            oldBal := 100 ‖
            acc :=
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account)) ‖
            newBal :=
              read(write(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account),
                  freshId(addM(memory, Person)).account,
                  freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account))),
                freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account)).balance) }
          φ }
    ~[readWriteDifferent]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))) ‖
            oldBal := 100 ‖
            acc :=
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account)) ‖
            newBal :=
              read(addM(write(addM(memory, Person), read(addM(memory, Person), freshId(addM(memory, Person)).account).balance,
                    100),
                  Account),
                freshId(addM(write(addM(memory, Person),
                        read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                      Account)).balance) }
          φ }
    ~[readAddEqual]~> dl![m]{
        { carol := freshId(addM(memory, Person)) ‖
            carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account),
                freshId(addM(memory, Person)).account,
                freshId(addM(write(addM(memory, Person),
                      read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                    Account))) ‖
            oldBal := 100 ‖
            acc :=
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account)) ‖
            newBal := 0 }
          φ } := by
  sol_chain

/-- `Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100;
delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance;`: `run` then `reads`.
The member gets a fresh default object, and `carolAcc` keeps the old one: `100` through `carolAcc`, the
default `0` through `carol.account`. -/
theorem chain :
    dl![m]{
      ⟨[ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100; delete carol.account;
        oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    ~~> dl![m]{
      { carol := freshId(addM(memory, Person)) ‖
          carolAcc := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
          memory :=
            write(addM(write(addM(memory, Person),
                  read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                Account),
              freshId(addM(memory, Person)).account,
              freshId(addM(write(addM(memory, Person),
                    read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                  Account))) ‖
          oldBal := 100 ‖
          acc :=
            freshId(addM(write(addM(memory, Person),
                  read(addM(memory, Person), freshId(addM(memory, Person)).account).balance, 100),
                Account)) ‖
          newBal := 0 }
        φ } :=
  (run ..).leads.via (reads ..)
#last_line chain

end FieldDeleteRef

end

namespace IndexedDelete

local instance : InContract := ⟨TestSuite⟩
variable (m : Modality) (φ : Post TestSuite)

/-- `toks` and `idx`, the receiver and the captured index. -/
def names : FreshTable := [("toks", "mv1"), ("idx", "se2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty

/-- `Token memory tk = b.tokens[++i]; tk.value = 9; delete b.tokens[i]; oldValue = tk.value;
newValue = b.tokens[i].value;` with `i` 1, run.  The elaborator captures the receiver and the index
before the statement (`toks = b.tokens; uint idx; idx = ++i; tk = toks[idx];`, the paper's first `⇝`
and `⇝*`); the run binding `toks`, `idx`, `i` and `tk` and writing `tk.value`, to the delete (`⇝*`);
`delete` writing a fresh default `Token` at the element (`⇝`); the two reads (`⇝*`); the merge, which
resolves the element to `toks[1 + 1]`; then the references: the array read again (`mv3`, `mv5`) is
`toks`'s, past `tk.value`'s write and the delete's write and allocation, and the element `mv4` the fresh
object the delete wrote (`readOnWriteIdentity`). -/
theorem run :
    dl![m]{
      { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
        ⟨[ Token memory tk = b.tokens[++i]; tk.value = 9; delete b.tokens[i];
          oldValue = tk.value; newValue = b.tokens[i].value; ]⟩ φ }
    ~*> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
          { toks := read(memory, b.tokens) }
            { idx := 0 }
              { i := i + 1 ‖ idx := i + 1 }
                { tk := read(memory, toks[idx]) }
                  { memory := write(memory, tk.value, 9) }
                    { mv3 := read(memory, b.tokens) }
                      ⟨[ delete mv3[i]; oldValue = tk.value; newValue = b.tokens[i].value; ]⟩ φ }
    ~[memoryIndexDeleteReference]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
          { toks := read(memory, b.tokens) }
            { idx := 0 }
              { i := i + 1 ‖ idx := i + 1 }
                { tk := read(memory, toks[idx]) }
                  { memory := write(memory, tk.value, 9) }
                    { mv3 := read(memory, b.tokens) }
                      { memory := write(addM(memory, Token), mv3[i], freshId(addM(memory, Token))) }
                        ⟨[ oldValue = tk.value; newValue = b.tokens[i].value; ]⟩ φ }
    ~*> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
          { toks := read(memory, b.tokens) }
            { idx := 0 }
              { i := i + 1 ‖ idx := i + 1 }
                { tk := read(memory, toks[idx]) }
                  { memory := write(memory, tk.value, 9) }
                    { mv3 := read(memory, b.tokens) }
                      { memory := write(addM(memory, Token), mv3[i], freshId(addM(memory, Token))) }
                        { oldValue := read(memory, tk.value) }
                          { mv5 := read(memory, b.tokens) }
                            { mv4 := read(memory, mv5[i]) } { newValue := read(memory, mv4.value) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 :=
              read(write(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                  9),
                freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        Token),
                      read(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                      freshId(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token))),
                    freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        Token),
                      read(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                      freshId(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token))),
                    read(write(addM(write(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket),
                                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                              9),
                            Token),
                          read(write(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket),
                                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                                9),
                              freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                          freshId(addM(write(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket),
                                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                                9),
                              Token))),
                        freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        Token),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                      freshId(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token))),
                    freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        Token),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                      freshId(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token))),
                    read(write(addM(write(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket),
                                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                              9),
                            Token),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                          freshId(addM(write(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket),
                                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                                9),
                              Token))),
                        freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 :=
              read(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token),
                    freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        Token),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                      freshId(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token))),
                    read(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token),
                        freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) }
          φ }
    ~[readAddDifferentIdentity]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 :=
              read(write(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                  9),
                freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        Token),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                      freshId(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token))),
                    read(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) }
          φ }
    ~[readWriteDifferentIdentity]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(write(addM(write(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket),
                              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                          9),
                        Token),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                      freshId(addM(write(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket),
                                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                            9),
                          Token))),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) }
          φ }
    ~[readOnWriteIdentity]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token)) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token)).value) }
          φ } := by
  sol_chain

/-- The rest of `IndexedDelete.run`: `oldValue` read past the delete's write and allocation to the write
through `tk`, `9`; `newValue`, `mv4`'s `value`, past the delete's write to the fresh object's default,
`0`; `i`, `idx` and the element `[1 + 1]` fold to `2` (`add_literals`, inside the memory terms too). -/
theorem reads :
    dl![m]{
      { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
          toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
          idx := 1 + 1 ‖
          tk :=
            read(addM(memory, TokenBucket),
              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
          mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
          memory :=
            write(addM(write(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                  9),
                Token),
              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token))) ‖
          oldValue :=
            read(write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))),
              read(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
          mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
          mv4 :=
            freshId(addM(write(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                  9),
                Token)) ‖
          newValue :=
            read(write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))),
              freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token)).value) }
        φ }
    ~[readWriteDifferent]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token)) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token)).value) }
          φ }
    ~[readAddDifferent]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue :=
              read(write(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                  9),
                read(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value) ‖
            mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token)) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token)).value) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue := 9 ‖ mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token)) ‖
            newValue :=
              read(write(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token),
                  read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                  freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token))),
                freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token)).value) }
          φ }
    ~[readWriteDifferent]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue := 9 ‖ mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token)) ‖
            newValue :=
              read(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                freshId(addM(write(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket),
                            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                        9),
                      Token)).value) }
          φ }
    ~[readAddEqual]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            tk :=
              read(addM(memory, TokenBucket),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                      9),
                    Token))) ‖
            oldValue := 9 ‖ mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[1 + 1]).value,
                    9),
                  Token)) ‖
            newValue := 0 }
          φ }
    ~[add_literals]~> dl![m]{
        { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
            toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 2 ‖
            idx := 2 ‖
            tk :=
              read(addM(memory, TokenBucket), read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]) ‖
            mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            memory :=
              write(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]).value,
                    9),
                  Token),
                read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2],
                freshId(addM(write(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket),
                          read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]).value,
                      9),
                    Token))) ‖
            oldValue := 9 ‖ mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            mv4 :=
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]).value,
                    9),
                  Token)) ‖
            newValue := 0 }
          φ } := by
  sol_chain

/-- `Token memory tk = b.tokens[++i]; tk.value = 9; delete b.tokens[i]; oldValue = tk.value;
newValue = b.tokens[i].value;` with `i` 1: `run` then `reads`.  The element position is overwritten
with a fresh default object, and `tk` keeps the old one: `9` through `tk`, the default `0` at the
overwritten position. -/
theorem chain :
    dl![m]{
      { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
        ⟨[ Token memory tk = b.tokens[++i]; tk.value = 9; delete b.tokens[i];
          oldValue = tk.value; newValue = b.tokens[i].value; ]⟩ φ }
    ~~> dl![m]{
      { i := 1 ‖ b := freshId(addM(memory, TokenBucket)) ‖
          toks := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖ idx := 0 ‖ i := 2 ‖
          idx := 2 ‖
          tk :=
            read(addM(memory, TokenBucket), read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]) ‖
          mv3 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
          memory :=
            write(addM(write(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]).value,
                  9),
                Token),
              read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2],
              freshId(addM(write(addM(memory, TokenBucket),
                    read(addM(memory, TokenBucket),
                        read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]).value,
                    9),
                  Token))) ‖
          oldValue := 9 ‖ mv5 := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
          mv4 :=
            freshId(addM(write(addM(memory, TokenBucket),
                  read(addM(memory, TokenBucket),
                      read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]).value,
                  9),
                Token)) ‖
          newValue := 0 }
        φ } :=
  (run ..).leads.via (reads ..)
#last_line chain

end IndexedDelete

end Solidity.Examples.Chains.MemoryDelete
