import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The storage worked examples as chains

The calculus's storage examples, in order, each one chain term over any modality `m` (the box where a step
needs it) and postcondition `φ` (`Calculus/Chains.lean`, `.claude/rules/derivations.md`), in the printed
names (`FreshNames` tables).  Stand-ins are named at the declaration: `total`, `basketA.items`, `tokens`,
`bucket.tokens` for `pVal`, `alice.accounts`, `alice.account.tokens`.  Not drawn: the bounds branches (an
out-of-range index reverts in the path's own check).

Every line is written, a printed `⇝` is a `~[r]~>` and a `⇝*` a `~*>`; past the program the stack merges
(`~[sequentialToParallel]~>`) and each read is resolved one law a link, every capture kept to the last line,
which `#last_line` checks.  A free parameter (`ageVal`, `i`, `a`) and the storage a program reads get a
concrete value in an update on the first line, so the reads end at literals where a law reads them.  Where
none does (a struct read, a read at a symbolic length, a read past an index check under any modality but the
box) the declaration says what is missing; a starting length has no spelling at all.
-/

namespace Solidity.Examples.Chains.Storage

local instance : InContract := ⟨StandardExample⟩

section
variable (m : Modality) (φ : Post StandardExample)

/-! ## Example: Symbolic Execution of `alice.age = ageVal` -/

namespace AgeWrite
/-- `alice.age = ageVal;` with `ageVal` 42: the field write, then the empty program; the merge puts the
value in the write. -/
theorem chain :
    dl![m]{ { ageVal := 42 } ⟨[ alice.age = ageVal; ]⟩ φ }
    ~*> dl![m]{ { ageVal := 42 } { storage := save(storage, alice.age, ageVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { ageVal := 42 ‖ storage := save(storage, alice.age, 42) } φ } := by
  sol_chain
#last_line chain
end AgeWrite

/-! ## Example: Symbolic Execution of `alice.account = acc` -/

namespace AccountCopy
/-- `Account storage acc = bob.account; alice.account = acc;` from a storage where `bob.account.balance` is
10: the write stores the value found at the alias's path (`find(storage, acc)`), not the alias path.  The
paper's one `⇝*`; the merge substitutes the alias and reads `bob.account` in the starting storage.  A
struct read has no literal: no law reads `bob.account` through the write below it. -/
theorem chain :
    dl![m]{ { storage := save(storage, bob.account.balance, 10) }
        ⟨[ Account storage acc = bob.account; alice.account = acc; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, bob.account.balance, 10) }
        { acc := bob.account } { storage := save(storage, alice.account, find(storage, acc)) } φ }
    ~[sequentialToParallel]~> dl![m]{ { acc := bob.account ‖
        storage := save(save(storage, bob.account.balance, 10), alice.account,
          find(save(storage, bob.account.balance, 10), bob.account)) } φ } := by
  sol_chain
#last_line chain
end AccountCopy

/-! ## Example: Symbolic Execution of `alice.account.balance = 10` -/

namespace BalanceWrite
def names : FreshTable := [("pv", "se1"), ("acc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
/-- `alice.account.balance = 10;`: the value captured (`pv`) and the receiver aliased (`acc`), the write
through the alias; the merge puts both in it. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.balance = 10; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~>
      dl![m]{ ⟨[ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 10 } { acc := alice.account } ⟨[ acc.balance = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ } := by
  sol_chain
#last_line chain
end BalanceWrite

/-! ## Example: Symbolic Execution of `v = alice.account.balance` -/

namespace BalanceRead
def names : FreshTable := [("acc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
/-- `v = alice.account.balance;` from a storage where it is 10: the receiver is aliased (`acc`), the alias
bound, the field read into `v`, the updates merged, and the read of the write resolved (`findOnSave`). -/
theorem chain :
    dl![m]{ { storage := save(storage, alice.account.balance, 10) } ⟨[ v = alice.account.balance; ]⟩ φ }
    ~[storageFieldRead_unfold_rightFst]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) }
        ⟨[ Account storage acc = alice.account; v = acc.balance; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.account.balance, 10) } { acc := alice.account }
        ⟨[ v = acc.balance; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.account.balance, 10) } { acc := alice.account }
        { v := find(storage, acc.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖
        acc := alice.account ‖ v := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ }
    ~[findOnSave]~>
      dl![m]{ { storage := save(storage, alice.account.balance, 10) ‖ acc := alice.account ‖ v := 10 } φ } := by
  sol_chain
#last_line chain
end BalanceRead

/-! ## Example: Symbolic Execution of `alice.account.token.value = 5` -/

namespace TokenWrite
def names : FreshTable := [("pv", "se1"), ("aliceTok", "sp1"), ("aliceAcc", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
/-- `alice.account.token.value = 5;`: two aliases, `aliceTok`, then `aliceAcc` for its initialiser's
receiver, `aliceTok` bound through `aliceAcc`; the merge binds it to `alice.account.token`. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.token.value = 5; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~>
      dl![m]{ ⟨[ uint pv = 5; Token storage aliceTok = alice.account.token; aliceTok.value = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 5 } ⟨[ aliceTok = alice.account.token; aliceTok.value = pv; ]⟩ φ }
    ~[storageFieldRead_unfold_rightFst]~>
      dl![m]{ { pv := 5 } ⟨[ Account storage aliceAcc = alice.account; aliceTok = aliceAcc.token; aliceTok.value = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 5 } { aliceAcc := alice.account } { aliceTok := aliceAcc.token } ⟨[ aliceTok.value = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 5 } { aliceAcc := alice.account } { aliceTok := aliceAcc.token }
        { storage := save(storage, aliceTok.value, pv) } φ }
    ~[sequentialToParallel]~> dl![m]{ { pv := 5 ‖ aliceAcc := alice.account ‖ aliceTok := alice.account.token ‖
        storage := save(storage, alice.account.token.value, 5) } φ } := by
  sol_chain
#last_line chain
end TokenWrite

/-! ## Example: A write read back, member by member -/

namespace AgeWriteRead
/-- `alice.age = 42; uint x = alice.age;`: the write, the read, merged; then the read of the write resolved as
solkey reads a path, from its head (`findMemberCons`), the write seen from `alice` (`selectOnSaveMember`),
and the word read back at the member (`findOnSave`). -/
theorem chain :
    dl![m]{ ⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ uint x = alice.age; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := find(save(storage, alice.age, 42), alice.age) } φ }
    ~[findMemberCons]~>
      dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := find(select(save(storage, alice.age, 42), alice), age) } φ }
    ~[selectOnSaveMember]~>
      dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := find(save(select(storage, alice), age, 42), age) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ x := 42 } φ } := by
  sol_chain
#last_line chain
end AgeWriteRead

namespace BalanceWriteRead
def names : FreshTable := [("pv", "se1"), ("acc", "sp1"), ("acc2", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty
/-- `alice.account.balance = 10; uint x = alice.account.balance;` run: the write through its alias `acc`, the
read through its alias `acc2`, and the merge. -/
theorem run :
    dl![m]{ ⟨[ alice.account.balance = 10; uint x = alice.account.balance; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~> dl![m]{
        ⟨[ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; uint x = alice.account.balance; ]⟩ φ }
    ~*> dl![m]{ { pv := 10 } { acc := alice.account } ⟨[ acc.balance = pv; uint x = alice.account.balance; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl![m]{
        { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
          ⟨[ uint x = alice.account.balance; ]⟩ φ }
    ~[localValueDeclInitDrop]~> dl![m]{
        { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
          ⟨[ x = alice.account.balance; ]⟩ φ }
    ~[storageFieldRead_unfold_rightFst]~> dl![m]{
        { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
          ⟨[ Account storage acc2 = alice.account; x = acc2.balance; ]⟩ φ }
    ~*> dl![m]{
        { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) } { acc2 := alice.account }
          ⟨[ x = acc2.balance; ]⟩ φ }
    ~*> dl![m]{
        { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) } { acc2 := alice.account }
          { x := find(storage, acc2.balance) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖ acc2 := alice.account ‖
            x := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ } := by
  sol_chain

/-- The read of the merged line resolved a member at a time, as solkey reads a path: from its head
(`findMemberCons`), the write seen from `alice` (`selectOnSaveMember`), again from `account`, and the word read
back at the member (`findOnSave`). -/
theorem reads :
    dl![m]{
        { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖ acc2 := alice.account ‖
            x := find(save(storage, alice.account.balance, 10), alice.account.balance) } φ }
    ~[findMemberCons]~> dl![m]{
        { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖ acc2 := alice.account ‖
            x := find(select(save(storage, alice.account.balance, 10), alice), account.balance) } φ }
    ~[selectOnSaveMember]~> dl![m]{
        { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖ acc2 := alice.account ‖
            x := find(save(select(storage, alice), account.balance, 10), account.balance) } φ }
    ~[findMemberCons]~> dl![m]{
        { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖ acc2 := alice.account ‖
            x := find(select(save(select(storage, alice), account.balance, 10), account), balance) } φ }
    ~[selectOnSaveMember]~> dl![m]{
        { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖ acc2 := alice.account ‖
            x := find(save(select(select(storage, alice), account), balance, 10), balance) } φ }
    ~[findOnSave]~> dl![m]{
        { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖ acc2 := alice.account ‖
            x := 10 } φ } := by
  sol_chain

/-- `alice.account.balance = 10; uint x = alice.account.balance;`: `run` then `reads`. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.balance = 10; uint x = alice.account.balance; ]⟩ φ }
    ~~> dl![m]{ { pv := 10 ‖ acc := alice.account ‖ storage := save(storage, alice.account.balance, 10) ‖
          acc2 := alice.account ‖ x := 10 } φ } :=
  (run ..).leads.via (reads ..)
#last_line chain
end BalanceWriteRead

/-! ## Example: Symbolic Execution of reading a storage root -/

namespace RootRead
/-- `uint v = total;` from a storage where `total` is 10: the paper's one `⇝*` (the declaration dropped, the
root read with `select`), the merge, and the read of the write resolved (`findOnSave`). -/
theorem chain :
    dl![m]{ { storage := save(storage, total, 10) } ⟨[ uint v = total; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, total, 10) } { v := find(storage, total) } φ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, total, 10) ‖ v := find(save(storage, total, 10), total) } φ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, total, 10) ‖ v := 10 } φ } := by
  sol_chain
#last_line chain
end RootRead

/-! ## Example: Symbolic Execution of whole-struct write `alice = pVal` -/

namespace RootWrite
/-- `total = pVal;` with `pVal` 7: a value written to a state variable, then the merge.  Stand-in: the printed
`alice = pVal;` has a struct-valued `pVal`, which has no spelling here (a memory struct fires
`memoryToStorageStoreRoot`); a `uint` root fires the same `storageRootWriteStore`. -/
theorem store :
    dl![m]{ { pVal := 7 } ⟨[ total = pVal; ]⟩ φ }
    ~*> dl![m]{ { pVal := 7 } { storage := save(storage, total, pVal) } φ }
    ~[sequentialToParallel]~> dl![m]{ { pVal := 7 ‖ storage := save(storage, total, 7) } φ } := by
  sol_chain

/-- `alice = bob;` from a storage where `bob.age` is 10: a storage path on the right is copied by reading the
value there (`find(storage, bob)`, as printed).  The merge reads `bob` in the starting storage; a
struct read has no literal, and no law reads `bob` through the write below it. -/
theorem copy :
    dl![m]{ { storage := save(storage, bob.age, 10) } ⟨[ alice = bob; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, bob.age, 10) } { storage := save(storage, alice, find(storage, bob)) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { storage := save(save(storage, bob.age, 10), alice, find(save(storage, bob.age, 10), bob)) } φ } := by
  sol_chain
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
alias.  The paper's one `⇝*` to the stack, then the merge, which writes at `bob.account.balance`; both
bindings of `acc` stay, the later one the one that counts. -/
theorem chain :
    dl![m]{ ⟨[ Account storage acc = alice.account; acc = bob.account; acc.balance = 10; ]⟩ φ }
    ~*> dl![m]{ { acc := alice.account } { acc := bob.account } { storage := save(storage, acc.balance, 10) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { acc := alice.account ‖ acc := bob.account ‖ storage := save(storage, bob.account.balance, 10) } φ } := by
  sol_chain
#last_line chain
end Rebind

namespace GlobalCopy
/-- `account = bob.account;` with `account` a state variable (`Roots`), from a storage where
`bob.account.balance` is 10: a global left-hand side copies.  The merge reads `bob.account` in the starting
storage; a struct read has no literal. -/
theorem chain :
    dl![m]{ { storage := save(storage, bob.account.balance, 10) } ⟨[ account = bob.account; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, bob.account.balance, 10) }
        { storage := save(storage, account, find(storage, bob.account)) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(save(storage, bob.account.balance, 10), account,
            find(save(storage, bob.account.balance, 10), bob.account)) } φ } := by
  sol_chain
#last_line chain
end GlobalCopy
end

/-! ## Example: Index Read and Write on a Storage Array -/

section
variable (m : Modality) (φ : Post StandardExample)

namespace IndexRead
/-- `v = values[i];` with `i` 1, from a storage where `values[1]` is 10, at the box.  One normal branch: the
bounds check is the path's own (`State.checkIndex`, the `@S` of `values[1]@S`), so the rule does not branch
and there is no `i < 0 ∨ i ≥ ℓ` sequent.  `findOnSave` reads the write back past the check under the box only,
where a check that fails makes the line true.  Under any modality `m` the chain stops at the check: no law
decides it, which needs the length in `S`, and a starting length has no spelling (the notation writes a length
by a push or a pop only). -/
theorem chain :
    dl![.box]{ { i := 1 ‖ storage := save(storage, values[1], 10) } ⟨[ v = values[i]; ]⟩ φ }
    ~*> dl![.box]{ { i := 1 ‖ storage := save(storage, values[1], 10) } { v := find(storage, values[i]) } φ }
    ~[sequentialToParallel]~> dl![.box]{
        { i := 1 ‖ storage := save(storage, values[1], 10) ‖
            v := find(save(storage, values[1], 10), values[1]@save(storage, values[1], 10)) } φ }
    ~[findOnSave]~> dl![.box]{ { i := 1 ‖ storage := save(storage, values[1], 10) ‖ v := 10 } φ } := by
  sol_chain
#last_line chain
end IndexRead

namespace IndexWrite
/-- `values[i] = 100;` with `i` 1.  One normal branch, as for the read. -/
theorem chain :
    dl![m]{ { i := 1 } ⟨[ values[i] = 100; ]⟩ φ }
    ~*> dl![m]{ { i := 1 } { storage := save(storage, values[i], 100) } φ }
    ~[sequentialToParallel]~> dl![m]{ { i := 1 ‖ storage := save(storage, values[1], 100) } φ } := by
  sol_chain
#last_line chain
end IndexWrite

namespace MappingRead
/-- `v = balances[a];` with `a` 3, from a storage where `balances[3]` is 10, at the box: a mapping key, no
length check.  The path records the key's check all the same (`balances[3]@S`), and `findOnSave` reads the
write back past it under the box only.  Under any modality `m` the chain stops there: no law yet drops the
check of a mapping key, which cannot fail. -/
theorem chain :
    dl![.box]{ { a := 3 ‖ storage := save(storage, balances[3], 10) } ⟨[ v = balances[a]; ]⟩ φ }
    ~*> dl![.box]{ { a := 3 ‖ storage := save(storage, balances[3], 10) } { v := find(storage, balances[a]) } φ }
    ~[sequentialToParallel]~> dl![.box]{
        { a := 3 ‖ storage := save(storage, balances[3], 10) ‖
            v := find(save(storage, balances[3], 10), balances[3]@save(storage, balances[3], 10)) } φ }
    ~[findOnSave]~> dl![.box]{ { a := 3 ‖ storage := save(storage, balances[3], 10) ‖ v := 10 } φ } := by
  sol_chain
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
/-- `Token storage tokRef = bob.account.token; tokens[i] = tokRef;` (`TestSuite`) with `i` 1, from a storage
where `bob.account.token.value` is 10: the element written is the value found at the alias path.  The paper's
one `⇝*`: the nested initialiser aliased one member at a time (`bobAcc`, then `tokRef` through it), then the
write; the merge binds `tokRef` to `bob.account.token`, as printed.  A struct read has no literal: no law
reads `bob.account.token` through the write below it. -/
theorem chain :
    dl![m]{ { i := 1 ‖ storage := save(storage, bob.account.token.value, 10) }
        ⟨[ Token storage tokRef = bob.account.token; tokens[i] = tokRef; ]⟩ φ }
    ~*> dl![m]{ { i := 1 ‖ storage := save(storage, bob.account.token.value, 10) }
        { bobAcc := bob.account } { tokRef := bobAcc.token } { storage := save(storage, tokens[i], find(storage, tokRef)) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 1 ‖ bobAcc := bob.account ‖ tokRef := bob.account.token ‖
            storage :=
              save(save(storage, bob.account.token.value, 10), tokens[1]@save(storage, bob.account.token.value, 10),
                find(save(storage, bob.account.token.value, 10), bob.account.token)) } φ } := by
  sol_chain
#last_line chain
end IndexWriteStruct

/-! ## Example: Push and Pop on a Storage Array -/

/- A concrete starting length has no spelling: the notation writes a length by a push or a pop only
(`Calculus/Notation.lean`, `rStor`), so the push and pop examples start from the storage as it is and keep
its length, `values.length`, symbolic. -/

namespace Push
/-- `values.push(42);` (`TestSuite`): the element at the old length and the length in one update;
`values.length` is the printed `n`.  The paper's one `⇝`, the rule and the empty program after it. -/
def chain :
    dl![m]{ ⟨[ values.push(42); ]⟩ φ }
    ~*> dl![m]{ { storage := save(save(storage, values[values.length], 42), values.length, values.length + 1) } φ } := by
  sol_chain
#last_line chain
end Push

namespace Pop
/-- `tokens.pop();`: the last slot cleared with `delAt` and the length decremented, `tokens.length` the printed
`ℓ`.  One branch: an empty array reverts by itself, so there is no `ℓ ≤ 0` sequent. -/
def chain :
    dl![m]{ ⟨[ tokens.pop(); ]⟩ φ }
    ~*> dl![m]{ { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) } φ } := by
  sol_chain
#last_line chain
end Pop

namespace PushAfterPop
/-- `tokens.push(); tokens[0].value = 7; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value;`: the
push, the write, the pop, then a bound push (`storageLocalRootPushBind`, which only bumps the length).
Stand-in: the printed `tokens.push().value` is a member of a call, which is refused; `sp` binds the slot.  The
seven updates merge into one; the explicit-check paths record the storage term in which each index was
checked.  The paper's `i == 0` is not reached: the indices are the symbolic length (`tokens[tokens.length]`),
and the read laws read literal indices only. -/
theorem chain :
    dl![m]{ ⟨[ tokens.push(); tokens[0].value = 7; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~[storagePushLengthSaveReferenceElement]~> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) }
          ⟨[ tokens[0].value = 7; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~[storageFieldWrite_unfold_leftFst]~> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) }
          ⟨[ uint se1 = 7; Token storage sp1 = tokens[0]; sp1.value = se1; tokens.pop(); Token storage sp = tokens.push();
            uint i = sp.value; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) } { se1 := 7 } { sp1 := tokens[0] }
          ⟨[ sp1.value = se1; tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~[storageFieldWriteSave]~> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) } { se1 := 7 } { sp1 := tokens[0] }
          { storage := save(storage, sp1.value, se1) }
          ⟨[ tokens.pop(); Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~[storagePopSave]~> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) } { se1 := 7 } { sp1 := tokens[0] }
          { storage := save(storage, sp1.value, se1) }
          { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) }
          ⟨[ Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~[storageLocalDeclInitDrop]~> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) } { se1 := 7 } { sp1 := tokens[0] }
          { storage := save(storage, sp1.value, se1) }
          { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) }
          ⟨[ sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~[storageLocalRootPushBind]~> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) } { se1 := 7 } { sp1 := tokens[0] }
          { storage := save(storage, sp1.value, se1) }
          { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) }
          { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          ⟨[ uint i = sp.value; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) } { se1 := 7 } { sp1 := tokens[0] }
          { storage := save(storage, sp1.value, se1) }
          { storage := save(delAt(storage, tokens[tokens.length - 1]), tokens.length, tokens.length - 1) }
          { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { i := find(storage, sp.value) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { se1 := 7 ‖ sp1 := tokens[0]@save(storage, tokens.length, tokens.length + 1) ‖
            storage :=
              save(save(delAt(save(save(storage, tokens.length, tokens.length + 1),
                      (tokens[0]@save(storage, tokens.length, tokens.length + 1)).value, 7),
                    tokens[tokens.length - 1]),
                  tokens.length, tokens.length - 1),
                tokens.length, tokens.length + 1) ‖
            sp :=
              tokens[tokens.length]@save(delAt(save(save(storage, tokens.length, tokens.length + 1),
                      (tokens[0]@save(storage, tokens.length, tokens.length + 1)).value, 7),
                    tokens[tokens.length - 1]),
                  tokens.length, tokens.length - 1) ‖
            i :=
              find(save(save(delAt(save(save(storage, tokens.length, tokens.length + 1),
                        (tokens[0]@save(storage, tokens.length, tokens.length + 1)).value, 7),
                      tokens[tokens.length - 1]),
                    tokens.length, tokens.length - 1),
                  tokens.length, tokens.length + 1),
                (tokens[tokens.length]@save(delAt(save(save(storage, tokens.length, tokens.length + 1),
                            (tokens[0]@save(storage, tokens.length, tokens.length + 1)).value, 7),
                          tokens[tokens.length - 1]),
                        tokens.length, tokens.length - 1)).value) } φ } := by
  sol_chain
#last_line chain
end PushAfterPop

/-! ## Example: Pop After Push -/

namespace PopAfterPush
/-- `values.push(); values.pop();`: the push clears the appended slot and bumps the length
(`storagePushLengthSave`, the paper's first `⇝`), then the pop (its second).  One branch (`n + 1 > 0`); there is
no `sizeNotNegative`.  The two storage writes merge into one.  The paper's read-over-write that turns the
popped index `ℓ − 1` into `n` is not drawn: no law reads a length through a push. -/
theorem chain :
    dl![m]{ ⟨[ values.push(); values.pop(); ]⟩ φ }
    ~[storagePushLengthSave]~> dl![m]{
        { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) } ⟨[ values.pop(); ]⟩ φ }
    ~*> dl![m]{
        { storage := save(delAt(storage, values[values.length]), values.length, values.length + 1) }
          { storage := save(delAt(storage, values[values.length - 1]), values.length, values.length - 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage :=
            save(delAt(save(delAt(storage, values[values.length]), values.length, values.length + 1),
                values[values.length - 1]),
              values.length, values.length - 1) } φ } := by
  sol_chain
#last_line chain
end PopAfterPush

/-! ## Example: Nonsimple Path Index Write `alice.accounts[0] = 100` -/

namespace AccountsWrite
def names : FreshTable := [("pv", "se1"), ("sp", "sp1"), ("idx", "ie1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `basketA.items[0] = 100;` (`TestSuite`), the `uint[]` member of a struct: stands for
`alice.accounts[0] = 100;`, which `StandardExample` has no member for.  The paper's `⇝` (the source, receiver
and index captured), `⇝*` (the declarations bound) and `⇝` (the write, its in-bounds branch), then the
merge. -/
theorem chain :
    dl![m]{ ⟨[ basketA.items[0] = 100; ]⟩ φ }
    ~[storageIndexWriteCaptureAllComplexRecv]~>
      dl![m]{ ⟨[ uint pv = 100; uint[] storage sp = basketA.items; uint idx = 0; sp[idx] = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 100 } { sp := basketA.items } { idx := 0 } ⟨[ sp[idx] = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 100 } { sp := basketA.items } { idx := 0 } { storage := save(storage, sp[idx], pv) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { pv := 100 ‖ sp := basketA.items ‖ idx := 0 ‖ storage := save(storage, basketA.items[0], 100) } φ } := by
  sol_chain
#last_line chain
end AccountsWrite

/-! ## Example: Nonsimple Path and Index Write -/

namespace AccountsWriteIncrement
def names : FreshTable := [("pv", "se1"), ("sp", "sp2"), ("idx", "se3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `basketA.items[++i] = valueVal;` (stands for `alice.accounts[++i] = valueVal;`) with `i` 2 and `valueVal`
42.  The paper's `⇝`, the value snapshotted, the receiver aliased and the index captured in that order, is
the elaborator's: the program is `uint pv = valueVal; uint[] storage sp = basketA.items; uint idx;
idx = ++i; sp[idx] = pv;`.  Then one `⇝*` binding the captures (`idx` declared, then assigned `++i`), the
write, the merge, which resolves the element to `basketA.items[2 + 1]`, and the index folded to `3`. -/
theorem chain :
    dl![m]{ { i := 2 ‖ valueVal := 42 } ⟨[ basketA.items[++i] = valueVal; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ valueVal := 42 } { pv := valueVal } { sp := basketA.items } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          ⟨[ sp[idx] = pv; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ valueVal := 42 } { pv := valueVal } { sp := basketA.items } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          { storage := save(storage, sp[idx], pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ valueVal := 42 ‖ pv := 42 ‖ sp := basketA.items ‖ idx := 0 ‖ i := 2 + 1 ‖ idx := 2 + 1 ‖
            storage := save(storage, basketA.items[2 + 1], 42) } φ }
    ~[add_literals]~> dl![m]{
        { i := 2 ‖ valueVal := 42 ‖ pv := 42 ‖ sp := basketA.items ‖ idx := 0 ‖ i := 3 ‖ idx := 3 ‖
            storage := save(storage, basketA.items[3], 42) } φ } := by
  sol_chain
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
/-- `matrix[i++][i++] = 77;` with `i` 0, at the box.  The paper's `⇝` and first `⇝*` are the elaborator's: it
captures both increments before the write (`uint idx1; idx1 = i++; uint[] storage sp = matrix[idx1];
uint idx2; idx2 = i++; sp[idx2] = 77;`; `77` is a value, so `pv` is not declared).  Then the paper's second
`⇝*`, to the stack of captures, the write, the merge, which resolves the captures, and the two additions
folded: the write lands at `matrix[0][1]` and `i` ends at `2`, as printed. -/
theorem chain :
    dl![.box]{ { i := 0 } ⟨[ matrix[i++][i++] = 77; ]⟩ φ }
    ~*> dl![.box]{
        { i := 0 } { idx1 := 0 } { i := i + 1 ‖ idx1 := i } { sp := matrix[idx1] } { idx2 := 0 } { i := i + 1 ‖ idx2 := i }
          ⟨[ sp[idx2] = 77; ]⟩ φ }
    ~*> dl![.box]{
        { i := 0 } { idx1 := 0 } { i := i + 1 ‖ idx1 := i } { sp := matrix[idx1] } { idx2 := 0 } { i := i + 1 ‖ idx2 := i }
          { storage := save(storage, sp[idx2], 77) } φ }
    ~[sequentialToParallel]~> dl![.box]{
        { i := 0 ‖ idx1 := 0 ‖ i := 0 + 1 ‖ idx1 := 0 ‖ sp := matrix[0] ‖ idx2 := 0 ‖ i := 0 + 1 + 1 ‖ idx2 := 0 + 1 ‖
            storage := save(storage, matrix[0][0 + 1], 77) } φ }
    ~[add_literals]~> dl![.box]{
        { i := 0 ‖ idx1 := 0 ‖ i := 1 ‖ idx1 := 0 ‖ sp := matrix[0] ‖ idx2 := 0 ‖ i := 1 + 1 ‖ idx2 := 1 ‖
            storage := save(storage, matrix[0][1], 77) } φ }
    ~[add_literals]~> dl![.box]{
        { i := 0 ‖ idx1 := 0 ‖ i := 1 ‖ idx1 := 0 ‖ sp := matrix[0] ‖ idx2 := 0 ‖ i := 2 ‖ idx2 := 1 ‖
            storage := save(storage, matrix[0][1], 77) } φ } := by
  sol_chain
#last_line chain
end MatrixRow
end

end Solidity.Examples.Chains.Storage
