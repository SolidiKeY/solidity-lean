import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The storage worked examples as chains

The calculus's storage examples, in order, each a chain over any modality `m` and postcondition `φ`
(`Calculus/Chains.lean`): a printed `⇝` is `~[r]~>`, a `⇝*` a `~*>`, and where a printed line merges its
updates into one parallel update the chain reaches it with `~[sequentialToParallel]~>` (`~~>`), in the
printed names (`FreshNames` tables).  Stand-ins are named at the declaration: `total`, `basketA.items`,
`tokens`, `bucket.tokens` for `pVal`, `alice.accounts`, `alice.account.tokens`.
A line of the strategy that binds an alias through another alias (`{ aliceTok := aliceAcc.token }`) or
indexes by a capture (`sp[idx]`) is crossed unwritten (`_ ~> _`, `_ ~*> _`), the next written line being
its merge, which binds the alias to its path as the printed line does.  Every chain ends at one parallel
update, its reads resolved and its dead captures dropped (`~[simplifyUpdate]~>`, the last link), which
`#last_line` checks after it.  Not drawn: the bounds branches (an out-of-range index reverts in the path's
own check).
-/

namespace Solidity.Examples.Chains.Storage

local instance : InContract := ⟨StandardExample⟩

section
variable (m : Modality) (φ : Post StandardExample)

/-! ## Example: Symbolic Execution of `alice.age = ageVal` -/

namespace AgeWrite
/-- `alice.age = ageVal;`: the field write, then the empty program. -/
def chain :
    dl![m]{ ⟨[ alice.age = ageVal; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, ageVal) } φ } :=
  calc dl![m]{ ⟨[ alice.age = ageVal; ]⟩ φ }
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { storage := save(storage, alice.age, ageVal) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { storage := save(storage, alice.age, ageVal) } φ } := rfl
#last_line chain
end AgeWrite

/-! ## Example: Symbolic Execution of `alice.account = acc` -/

namespace AccountCopy
/-- `Account storage acc = bob.account; alice.account = acc;`: the write stores the value found at the alias's path (`find(storage, acc)`), not the alias path; the last line has the alias substituted. -/
theorem chain :
    dl![m]{ ⟨[ Account storage acc = bob.account; alice.account = acc; ]⟩ φ }
    ~~> dl![m]{ { acc := bob.account ‖ storage := save(storage, alice.account, find(storage, bob.account)) } φ } :=
  calc dl![m]{ ⟨[ Account storage acc = bob.account; alice.account = acc; ]⟩ φ }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~> dl![m]{ { acc := bob.account ‖ storage := save(storage, alice.account, find(storage, bob.account)) } φ } := by sol_chain
#last_line chain
end AccountCopy

/-! ## Example: Symbolic Execution of `alice.account.balance = 10` -/

namespace BalanceWrite
def names : FreshTable := [("pv", "se1"), ("acc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
/-- `alice.account.balance = 10;`.  The printed `int pv` is `uint pv` here, the type of the
place written; the captures, dead once the write holds them, go last. -/
set_option maxHeartbeats 400000 in
theorem chain :
    dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.account.balance, 10) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    _ ~[storageFieldWrite_unfold_leftFst]~>
        dl![m]{ ⟨[ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { pv := 10 } { acc := alice.account } ⟨[ acc.balance = pv; ]⟩ φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account } ⟨[ acc.balance = pv; ]⟩ φ } := by rfl
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account } { storage := save(storage, acc.balance, pv) } ⟨[ ]⟩ φ } :=
      rfl
    _ ~[emptyModality]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account } { storage := save(storage, acc.balance, pv) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } := by rfl
    _ ~[simplifyUpdate]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) } φ } := by sol_chain
#last_line chain
end BalanceWrite

/-! ## Example: Symbolic Execution of `v = alice.account.balance` -/

namespace BalanceRead
def names : FreshTable := [("acc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
/-- `v = alice.account.balance;`: the receiver is aliased (`acc`), the alias bound, the field read into `v`, and the updates merged. -/
theorem chain :
    dl![m]{ ⟨[ v = alice.account.balance; ]⟩ φ }
    ~~> dl![m]{ { v := find(storage, alice.account.balance) } φ } :=
  calc dl![m]{ ⟨[ v = alice.account.balance; ]⟩ φ }
    _ ~[storageFieldRead_unfold_rightFst]~>
        dl![m]{ ⟨[ Account storage acc = alice.account; v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { acc := alice.account } ⟨[ v = acc.balance; ]⟩ φ } := by sol_chain
    _ ~[storageFieldReadFind]~>
        dl![m]{ { acc := alice.account } { v := find(storage, acc.balance) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { acc := alice.account } { v := find(storage, acc.balance) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { acc := alice.account ‖ v := find(storage, alice.account.balance) } φ } := by rfl
    _ ~[simplifyUpdate]~> dl![m]{ { v := find(storage, alice.account.balance) } φ } := by sol_chain
#last_line chain
end BalanceRead

/-! ## Example: Symbolic Execution of `alice.account.token.value = 5` -/

namespace TokenWrite
def names : FreshTable := [("pv", "se1"), ("aliceTok", "sp1"), ("aliceAcc", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
set_option maxHeartbeats 300000 in
/-- `alice.account.token.value = 5;`: two aliases, `aliceTok` and `aliceAcc`.  The printed line with `Account storage aliceAcc = alice.account;` is left `_`: `dl!{ … }` cannot read an alias typed from another alias's path (`Calculus/Notation.lean`); so is the step binding `aliceTok` through `aliceAcc`, whose merge binds it to `alice.account.token`. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.token.value = 5; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.account.token.value, 5) } φ } :=
  calc dl![m]{ ⟨[ alice.account.token.value = 5; ]⟩ φ }
    _ ~[storageFieldWrite_unfold_leftFst]~>
        dl![m]{ ⟨[ uint pv = 5; Token storage aliceTok = alice.account.token; aliceTok.value = pv; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { pv := 5 } ⟨[ aliceTok = alice.account.token; aliceTok.value = pv; ]⟩ φ } := by sol_chain
    _ ~[storageFieldRead_unfold_rightFst]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 5 ‖ aliceAcc := alice.account ‖ aliceTok := alice.account.token }
          ⟨[ aliceTok.value = pv; ]⟩ φ } := by sol_chain
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { pv := 5 ‖ aliceAcc := alice.account ‖ aliceTok := alice.account.token }
          { storage := save(storage, aliceTok.value, pv) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { pv := 5 ‖ aliceAcc := alice.account ‖ aliceTok := alice.account.token }
          { storage := save(storage, aliceTok.value, pv) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 5 ‖ aliceAcc := alice.account ‖ aliceTok := alice.account.token ‖
          storage := save(storage, alice.account.token.value, 5) } φ } := by rfl
    _ ~[simplifyUpdate]~> dl![m]{ { storage := save(storage, alice.account.token.value, 5) } φ } := by sol_chain
#last_line chain
end TokenWrite

/-! ## Example: A write read back, member by member -/

namespace AgeWriteRead
set_option maxHeartbeats 2000000 in
/-- `alice.age = 42; uint x = alice.age;`: the write, the read, merged; then the read of the write resolved as
solkey reads a path, from its head (`findMemberCons`), the write seen from `alice` (`selectOnSaveMember`),
and the word read back at the member (`findOnSave`). -/
theorem chain :
    dl![m]{ ⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } :=
  calc dl![m]{ ⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ }
    _ ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ } := by
      sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := find(save(storage, alice.age, 42), alice.age) } φ } := by sol_chain
    _ ~[findMemberCons]~>
        dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := select(select(save(storage, alice.age, 42), alice), age) } φ } := by sol_chain
    _ ~[selectOnSaveMember]~>
        dl![m]{ { storage := save(storage, alice.age, 42) ‖
          x := select(save(select(storage, alice), age, 42), age) } φ } := by sol_chain
    _ ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by sol_chain
#last_line chain
end AgeWriteRead

namespace BalanceWriteRead
def names : FreshTable := [("pv", "se1"), ("acc", "sp1"), ("acc2", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
set_option maxHeartbeats 2000000 in
/-- `alice.account.balance = 10; uint x = alice.account.balance;`: the write and the read through their
aliases, merged, the dead captures dropped; then the read of the write resolved a member at a time, `alice`
then `account`, to `10`. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.balance = 10; uint x = alice.account.balance; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖ x := 10 } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 10; uint x = alice.account.balance; ]⟩ φ }
    _ ~*> dl![m]{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
          { acc2 := alice.account } { x := find(storage, acc2.balance) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
          acc2 := alice.account ‖ x := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ } := by
      sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
          x := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ } := by sol_chain
    _ ~[findMemberCons]~>
        dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
          x := find(select(save(storage, alice.account.balance, 10), alice), account.balance) } φ } := by
      sol_chain
    _ ~[selectOnSaveMember]~>
        dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
          x := find(save(select(storage, alice), account.balance, 10), account.balance) } φ } := by sol_chain
    _ ~[findMemberCons]~>
        dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
          x := select(select(save(select(storage, alice), account.balance, 10), account), balance) } φ } := by
      sol_chain
    _ ~[selectOnSaveMember]~>
        dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
          x := select(save(select(select(storage, alice), account), balance, 10), balance) } φ } := by
      sol_chain
    _ ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖ x := 10 } φ } := by
      sol_chain
#last_line chain
end BalanceWriteRead

/-! ## Example: Symbolic Execution of reading a storage root -/

namespace RootRead
/-- `uint v = total;`: the state variable is read with `select`. -/
def chain :
    dl![m]{ ⟨[ uint v = total; ]⟩ φ }
    ~*> dl![m]{ { v := select(storage, total) } φ } :=
  calc dl![m]{ ⟨[ uint v = total; ]⟩ φ }
    _ ~[localValueDeclInitDrop]~> dl![m]{ ⟨[ v = total; ]⟩ φ } := rfl
    _ ~[storageRootReadSelect]~> dl![m]{ { v := select(storage, total) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { v := select(storage, total) } φ } := rfl
#last_line chain
end RootRead

/-! ## Example: Symbolic Execution of whole-struct write `alice = pVal` -/

namespace RootWrite
/-- `total = pVal;`: a value written to a state variable.  Stand-in: the printed `alice = pVal;` has a
struct-valued `pVal`, which has no spelling here (a memory struct fires `memoryToStorageStoreRoot`); a
`uint` root fires the same `storageRootWriteStore`. -/
def store :
    dl![m]{ ⟨[ total = pVal; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, total, pVal) } φ } :=
  calc dl![m]{ ⟨[ total = pVal; ]⟩ φ }
    _ ~[storageRootWriteStore]~> dl![m]{ { storage := store(storage, total, pVal) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { storage := store(storage, total, pVal) } φ } := rfl

/-- `alice = bob;`: a storage path on the right is copied by reading the value there (`find(storage, bob)`,
the printed `select`). -/
def copy :
    dl![m]{ ⟨[ alice = bob; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, alice, find(storage, bob)) } φ } :=
  calc dl![m]{ ⟨[ alice = bob; ]⟩ φ }
    _ ~[storageRootWriteCopySource]~>
        dl![m]{ { storage := store(storage, alice, find(storage, bob)) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { storage := store(storage, alice, find(storage, bob)) } φ } := rfl
#last_line store
#last_line copy
end RootWrite

end

/-! ## Example: Local Storage Rebinding Versus Global Root Copy -/

/-- `StandardExample` with a state variable `account` of its own: the global root. -/
def Roots : Contract := contract!{ Account account; Person alice; Person bob; }

section
local instance : InContract := ⟨Roots⟩
variable (m : Modality) (φ : Post Roots)

namespace Rebind
/-- `Account storage acc = alice.account; acc = bob.account; acc.balance = 10;`: `acc = bob.account` rebinds the
alias; the stack the strategy leaves, merged, then the capture it overwrites dropped. -/
def chain :
    dl![m]{ ⟨[ Account storage acc = alice.account; acc = bob.account; acc.balance = 10; ]⟩ φ }
    ~~> dl![m]{ { acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } φ } :=
  calc dl![m]{ ⟨[ Account storage acc = alice.account; acc = bob.account; acc.balance = 10; ]⟩ φ }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { acc := alice.account ‖ acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } φ } := by sol_chain
#last_line chain
end Rebind

namespace GlobalCopy
/-- `account = bob.account;` with `account` a state variable (`Roots`): a global left-hand side copies. -/
def chain :
    dl![m]{ ⟨[ account = bob.account; ]⟩ φ }
    ~*> dl![m]{ { storage := store(storage, account, find(storage, bob.account)) } φ } :=
  calc dl![m]{ ⟨[ account = bob.account; ]⟩ φ }
    _ ~[storageFieldReadStoreRoot]~>
        dl![m]{ { storage := store(storage, account, find(storage, bob.account)) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { storage := store(storage, account, find(storage, bob.account)) } φ } := rfl
#last_line chain
end GlobalCopy
end

/-! ## Example: Index Read and Write on a Storage Array -/

section
variable (m : Modality) (φ : Post StandardExample)

namespace IndexRead
/-- `v = values[i];`.  One normal branch: the bounds check is the path's own (`State.checkIndex`), so the
rule does not branch and there is no `i < 0 ∨ i ≥ ℓ` sequent; `ℓ` is `values.length`. -/
def chain :
    dl![m]{ ⟨[ v = values[i]; ]⟩ φ }
    ~*> dl![m]{ { v := find(storage, values[i]) } φ } :=
  calc dl![m]{ ⟨[ v = values[i]; ]⟩ φ }
    _ ~[storageIndexReadArrayFind]~> dl![m]{ { v := find(storage, values[i]) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { v := find(storage, values[i]) } φ } := rfl
#last_line chain
end IndexRead

namespace IndexWrite
/-- `values[i] = 100;`.  One normal branch, as for the read. -/
def chain :
    dl![m]{ ⟨[ values[i] = 100; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, values[i], 100) } φ } :=
  calc dl![m]{ ⟨[ values[i] = 100; ]⟩ φ }
    _ ~[storageIndexWriteArraySave]~> dl![m]{ { storage := save(storage, values[i], 100) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { storage := save(storage, values[i], 100) } φ } := rfl
#last_line chain
end IndexWrite

namespace MappingRead
/-- `v = balances[a];`: a mapping key, no length check. -/
def chain :
    dl![m]{ ⟨[ v = balances[a]; ]⟩ φ }
    ~*> dl![m]{ { v := find(storage, balances[a]) } φ } :=
  calc dl![m]{ ⟨[ v = balances[a]; ]⟩ φ }
    _ ~[storageIndexReadMappingFind]~> dl![m]{ { v := find(storage, balances[a]) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { v := find(storage, balances[a]) } φ } := rfl
#last_line chain
end MappingRead
end

section
local instance : InContract := ⟨TestSuite⟩
variable (m : Modality) (φ : Post TestSuite)

namespace IndexWriteStruct
def names : FreshTable := [("bobAcc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `Token storage tokRef = bob.account.token; tokens[i] = tokRef;` (`TestSuite`): the element written is the value found at the alias path.  The nested initialiser is aliased one member at a time (`bobAcc`, then `tokRef` through it), lines crossed unwritten; the merge binds `tokRef` to `bob.account.token`, as printed. -/
theorem chain :
    dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens[i] = tokRef; ]⟩ φ }
    ~~> dl![m]{ { tokRef := bob.account.token ‖
          storage := save(storage, tokens[i], find(storage, bob.account.token)) } φ } :=
  calc dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens[i] = tokRef; ]⟩ φ }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
          storage := save(storage, tokens[i], find(storage, bob.account.token)) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { tokRef := bob.account.token ‖
          storage := save(storage, tokens[i], find(storage, bob.account.token)) } φ } := by sol_chain
#last_line chain
end IndexWriteStruct

/-! ## Example: Push and Pop on a Storage Array -/

namespace Push
/-- `values.push(42);` (`TestSuite`): the element at the old length and the length in one update; `values.length` is the printed `n`. -/
def chain :
    dl![m]{ ⟨[ values.push(42); ]⟩ φ }
    ~*> dl![m]{ { storage := save(save(storage, values[values.length], 42), values.length, values.length + 1) } φ } :=
  calc dl![m]{ ⟨[ values.push(42); ]⟩ φ }
    _ ~[storagePushValueSave]~>
        dl![m]{ { storage := save(save(storage, values[values.length], 42), values.length, values.length + 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { storage := save(save(storage, values[values.length], 42), values.length, values.length + 1) } φ } := rfl
#last_line chain
end Push

namespace Pop
/-- `tokens.pop();`: the last slot cleared with `delAt` and the length decremented, `tokens.length` the printed `ℓ`.  One branch: an empty array reverts by itself, so there is no `ℓ ≤ 0` sequent. -/
def chain :
    dl![m]{ ⟨[ tokens.pop(); ]⟩ φ }
    ~*> dl![m]{ { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) } φ } :=
  calc dl![m]{ ⟨[ tokens.pop(); ]⟩ φ }
    _ ~[storagePopSave]~>
        dl![m]{ { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) } φ } := rfl
#last_line chain
end Pop

namespace PushAfterPop
/-- `tokens.push(); tokens[0].value = 7; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value;`: the push, the write, the pop, then a bound push (`storageLocalRootPushBind`, which only bumps the length).  Stand-in: the printed `tokens.push().value` is a member of a call, which is refused; `sp` binds the slot.  The chain stops at the updates the program leaves: the push's alias `sp` (`tokens[tokens.length]`) checks the length in the state it runs in, so no storage write merges over it, and reading `i` through the cleared slot stays the Theory's (`delAt`, `findOnSave`).  -/
def chain :
    dl![m]{ ⟨[ tokens.push(); tokens[0].value = 7; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~*> dl![m]{
      { storage := save(storage, tokens.length, tokens.length + 1) }
      { se1 := 7 }
      { sp1 := tokens[0] }
      { storage := save(storage, sp1.value, se1) }
      { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) }
      { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
      { i := find(storage, sp.value) } φ } :=
  calc dl![m]{ ⟨[ tokens.push(); tokens[0].value = 7; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    _ ~[storagePushLengthSaveReferenceElement]~>
        dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) }
          ⟨[ tokens[0].value = 7; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) } { se1 := 7 } { sp1 := tokens[0] }
          { storage := save(storage, sp1.value, se1) }
          { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) }
          ⟨[ Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{
      { storage := save(storage, tokens.length, tokens.length + 1) }
      { se1 := 7 }
      { sp1 := tokens[0] }
      { storage := save(storage, sp1.value, se1) }
      { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) }
      { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
      { i := find(storage, sp.value) } φ } := by sol_chain
end PushAfterPop

/-! ## Example: Pop After Push -/

namespace PopAfterPush
/-- `values.push(); values.pop();`: the push clears the appended slot and bumps the length (`storagePushLengthSave`), then the pop.  One branch (`n + 1 > 0`); there is no `sizeNotNegative`.  The two storage writes merge into one (a pop is one term; its `values[values.length - 1]` is printed, not a check). -/
theorem chain :
    dl![m]{ ⟨[ values.push(); values.pop(); ]⟩ φ }
    ~~> dl![m]{ { storage := save(delAt(save(delAt(storage, values[values.length]), values.length, values.length + 1),
            values[values.length - 1]), values.length, values.length - 1) } φ } :=
  calc dl![m]{ ⟨[ values.push(); values.pop(); ]⟩ φ }
    _ ~[storagePushLengthSave]~>
        dl![m]{ { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) }
          ⟨[ values.pop(); ]⟩ φ } := rfl
    _ ~[storagePopSave]~>
        dl![m]{ { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) }
          { storage := save(delAt(storage, values[values.length - 1]), values.length, values.length - 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) }
          { storage := save(delAt(storage, values[values.length - 1]), values.length, values.length - 1) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(delAt(save(delAt(storage, values[values.length]), values.length, values.length + 1),
            values[values.length - 1]), values.length, values.length - 1) } φ } := by sol_chain
#last_line chain
end PopAfterPush

/-! ## Example: Nonsimple Path Index Write `alice.accounts[0] = 100` -/

namespace AccountsWrite
def names : FreshTable := [("pv", "se1"), ("sp", "sp1"), ("idx", "ie1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `basketA.items[0] = 100;` (`TestSuite`), the `uint[]` member of a struct: stands for `alice.accounts[0] = 100;`, which `StandardExample` has no member for.  One normal branch. -/
theorem chain :
    dl![m]{ ⟨[ basketA.items[0] = 100; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, basketA.items[0], 100) } φ } :=
  calc dl![m]{ ⟨[ basketA.items[0] = 100; ]⟩ φ }
    _ ~[storageIndexWriteCaptureAllComplexRecv]~>
        dl![m]{ ⟨[ uint pv = 100; uint[] storage sp = basketA.items; uint idx = 0; sp[idx] = pv; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { pv := 100 } { sp := basketA.items } { idx := 0 } ⟨[ sp[idx] = pv; ]⟩ φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 100 ‖ sp := basketA.items ‖ idx := 0 } ⟨[ sp[idx] = pv; ]⟩ φ } := by rfl
    _ ~[storageIndexWriteArraySave]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 100 ‖ sp := basketA.items ‖ idx := 0 ‖ storage := save(storage, basketA.items[0], 100) } φ } := by sol_chain
    _ ~[simplifyUpdate]~> dl![m]{ { storage := save(storage, basketA.items[0], 100) } φ } := by sol_chain
#last_line chain
end AccountsWrite

/-! ## Example: Nonsimple Path and Index Write -/

namespace AccountsWriteIncrement
def names : FreshTable := [("pv", "se1"), ("sp", "sp2"), ("idx", "se3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `basketA.items[++i] = valueVal;` (stands for `alice.accounts[++i] = valueVal;`): the value snapshotted, the receiver aliased, the index captured, in that order.  The elaborator takes this step (an equality), declaring `idx` then assigning it; the chain goes on to the write and the merge, which resolves the element written, `basketA.items[i + 1]`; then the alias and the overwritten `idx := 0` go, while `pv := valueVal` and `i := i + 1` stay (a read of a local and an addition may halt). -/
theorem chain :
    dl![m]{ ⟨[ basketA.items[++i] = valueVal; ]⟩ φ }
    ~~> dl![m]{ { pv := valueVal ‖ i := i + 1 ‖ idx := i + 1 ‖
          storage := save(storage, basketA.items[i + 1], valueVal) } φ } :=
  calc dl![m]{ ⟨[ basketA.items[++i] = valueVal; ]⟩ φ }
    _ = dl![m]{ ⟨[ uint pv = valueVal; uint[] storage sp = basketA.items; uint idx; idx = ++i; sp[idx] = pv; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { pv := valueVal } { sp := basketA.items } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          ⟨[ sp[idx] = pv; ]⟩ φ } := by sol_chain
    _ ~[storageIndexWriteArraySave]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := valueVal ‖ sp := basketA.items ‖ idx := 0 ‖ i := i + 1 ‖ idx := i + 1 ‖
          storage := save(storage, basketA.items[i + 1], valueVal) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { pv := valueVal ‖ i := i + 1 ‖ idx := i + 1 ‖
          storage := save(storage, basketA.items[i + 1], valueVal) } φ } := by sol_chain
#last_line chain
end AccountsWriteIncrement
end

/-! ## Example: Side Effects in the Receiver and in the Index -/

section
variable (φ : Post StandardExample)

namespace MatrixRow
def names : FreshTable := [("idx1", "se1"), ("sp", "sp2"), ("idx2", "se3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
/-- `matrix[i++][i++] = 77;`, at the box.  The elaborator captures both increments before the write (the first step, an equality); `77` is a value, so `pv` is not declared.  The stack the strategy leaves indexes by the captures (`matrix[idx1]`, `sp[idx2]`) and is crossed unwritten; its merge resolves them; then the dead `idx1 := 0`, `idx2 := 0` go, while `i := i + 1` stays (an addition may halt) and `i + 1 + 1` is not shortened to `i + 2`. -/
theorem chain :
    dl![.box]{ ⟨[ matrix[i++][i++] = 77; ]⟩ φ }
    ~~> dl![.box]{ { i := i + 1 ‖ idx1 := i ‖ sp := matrix[i] ‖ i := i + 1 + 1 ‖ idx2 := i + 1 ‖
          storage := save(storage, matrix[i][i + 1], 77) } φ } :=
  calc dl![.box]{ ⟨[ matrix[i++][i++] = 77; ]⟩ φ }
    _ = dl![.box]{ ⟨[ uint idx1; idx1 = i++; uint[] storage sp = matrix[idx1]; uint idx2; idx2 = i++; sp[idx2] = 77; ]⟩ φ } := rfl
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![.box]{ { idx1 := 0 ‖ i := i + 1 ‖ idx1 := i ‖ sp := matrix[i] ‖ idx2 := 0 ‖ i := i + 1 + 1 ‖ idx2 := i + 1 ‖
          storage := save(storage, matrix[i][i + 1], 77) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![.box]{ { i := i + 1 ‖ idx1 := i ‖ sp := matrix[i] ‖ i := i + 1 + 1 ‖ idx2 := i + 1 ‖
          storage := save(storage, matrix[i][i + 1], 77) } φ } := by sol_chain
#last_line chain
end MatrixRow
end

end Solidity.Examples.Chains.Storage
