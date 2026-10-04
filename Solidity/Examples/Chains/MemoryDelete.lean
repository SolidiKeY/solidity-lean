import Solidity.Calculus.Chains
import Solidity.Calculus.ChainGen
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# Memory delete examples as chains

The calculus's worked memory `delete` examples, as `calc`s of formulas
`dl![m]{ … }` for every modality `m` and postcondition `φ` (see `Chains/Memory.lean`
for the conventions: printed `⇝` is `~[r]~>`, printed `⇝*` is `~*>`).

* A `delete` of an identity rebinds the root, or writes a fresh default object into
  the field or element; the alias keeps the old identity.
* The printed `oldAge = carolAlias.age` and the like leave their locals as
  parameters of the formula; the resolved reads of the last printed line are
  not drawn (no rewrite link states a memory law yet), and a line that binds a
  local by a captured index (`toks[idx]`) is crossed unwritten, the next written
  line being its merge.
* The indexed delete is stated in `TestSuite`, where `Account` has no `tokens`: a
  `TokenBucket memory b` stands for `carol` and its `b.tokens` for
  `carol.account.tokens`, one selector shorter; `tk` stands for `tok`, a state
  variable there.  The printed `delete toks[i]` is `delete b.tokens[i]`, bound again
  by the rules (`mv3`).
-/

namespace Solidity.Examples.Chains.MemoryDelete

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Memory Delete Cases -/

namespace RootDelete

/-- `Person memory carol; Person memory carolAlias = carol; carol.age = 33;
delete carol; oldAge = carolAlias.age; newAge = carol.age;` — `delete` rebinds
`carol` to a fresh default object, and the alias keeps the old one: the
reads resolve to `33` through the alias and to the default `0` through
`carol`. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Person memory carol; Person memory carolAlias = carol; carol.age = 33; delete carol;
               oldAge = carolAlias.age; newAge = carol.age; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ carolAlias := freshId(addM(memory, Person)) ‖
          carol := freshId(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person)) ‖
          memory := addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person) ‖
          oldAge := 33 ‖ newAge := 0 } φ } :=
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
    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ carolAlias := freshId(addM(memory, Person)) ‖
          carol := freshId(addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person)) ‖
          memory := addM(write(addM(memory, Person), freshId(addM(memory, Person)).age, 33), Person) ‖
          oldAge := 33 ‖ newAge := 0 } φ } := by
      sol_rws [readAddEqual, readAddDifferent, readOnWrite]
#last_line chain

end RootDelete

namespace FieldDeleteRef

/-- `acc`, the receiver of the last read. -/
def names : FreshTable := [("acc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `Person memory carol; Account memory carolAcc = carol.account;
carolAcc.balance = 100; delete carol.account; oldBal = carolAcc.balance;
newBal = carol.account.balance;` — the member gets a fresh default object, and
`carolAcc` keeps the old one. -/
def chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100;
               delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { carolAcc := read(memory, carol.account) }
                { memory := write(memory, carolAcc.balance, 100) }
                { memory := write(addM(memory, Account), carol.account, freshId(addM(memory, Account))) }
                { oldBal := read(memory, carolAcc.balance) }
                { acc := read(memory, carol.account) } { newBal := read(memory, acc.balance) } φ } :=
  calc dl![m]{ ⟨[ Person memory carol; Account memory carolAcc = carol.account; carolAcc.balance = 100;
                  delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ }
    _ ~[memoryReferenceDeclFreshAlloc]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory carolAcc = carol.account; carolAcc.balance = 100;
                   delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ } :=
      rfl
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ carolAcc = carol.account; carolAcc.balance = 100;
                   delete carol.account; oldBal = carolAcc.balance; newBal = carol.account.balance; ]⟩ φ } :=
      rfl
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
                  { acc := read(memory, carol.account) } { newBal := read(memory, acc.balance) } φ } :=
      by sol_chain

end FieldDeleteRef

namespace IndexedDelete

local instance : InContract := ⟨TestSuite⟩

/-- `toks` and `idx`, the receiver and the captured index. -/
def names : FreshTable := [("toks", "mv1"), ("idx", "se2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty

/-- `Token memory tk = b.tokens[++i]; tk.value = 9; delete b.tokens[i];
oldValue = tk.value; newValue = b.tokens[i].value;` — the element position is
overwritten with a fresh default object, and `tk` keeps the old one.  Lean's
first lines fold the printed second and third (the declaration dropped, the
receiver and the index captured); the stack the strategy leaves binds `tk` by
the captured index (`toks[idx]`), so it is crossed unwritten, and the merge of
the capture with the bind resolves the element read to `toks[i + 1]`. -/
def chain (m : Modality) (φ : Post TestSuite) :
    dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
            ⟨[ Token memory tk = b.tokens[++i]; tk.value = 9; delete b.tokens[i];
               oldValue = tk.value; newValue = b.tokens[i].value; ]⟩ φ }
    ~~> dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
                { toks := read(memory, b.tokens) } { idx := 0 }
                { i := i + 1 ‖ idx := i + 1 ‖ tk := read(memory, toks[i + 1]) }
                { memory := write(memory, tk.value, 9) }
                { mv3 := read(memory, b.tokens) }
                { memory := write(addM(memory, Token), mv3[i], freshId(addM(memory, Token))) }
                { oldValue := read(memory, tk.value) }
                { mv5 := read(memory, b.tokens) }
                { mv4 := read(memory, mv5[i]) } { newValue := read(memory, mv4.value) } φ } :=
  calc dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
               ⟨[ Token memory tk = b.tokens[++i]; tk.value = 9; delete b.tokens[i];
                  oldValue = tk.value; newValue = b.tokens[i].value; ]⟩ φ }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
                { toks := read(memory, b.tokens) } { idx := 0 }
                { i := i + 1 ‖ idx := i + 1 ‖ tk := read(memory, toks[i + 1]) }
                { memory := write(memory, tk.value, 9) }
                { mv3 := read(memory, b.tokens) }
                { memory := write(addM(memory, Token), mv3[i], freshId(addM(memory, Token))) }
                { oldValue := read(memory, tk.value) }
                { mv5 := read(memory, b.tokens) }
                { mv4 := read(memory, mv5[i]) } { newValue := read(memory, mv4.value) } φ } := by
      sol_chain

end IndexedDelete

end Solidity.Examples.Chains.MemoryDelete
