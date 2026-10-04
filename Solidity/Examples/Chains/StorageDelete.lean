import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The storage `delete` examples as chains

The calculus's storage `delete` examples, each one chain term over any modality `m` and postcondition `φ`
(`Examples/Chains/Storage.lean` says how to read one), in `TestSuite`.  `bucket.tokens` stands for
`alice.account.tokens`.  The strategy's runs are grouped as the paper prints them (a printed `⇝` that Lean
takes in several rules, a write or a read through the aliases it binds, is one `~*>`); past the merge every
read is resolved one law a link, every capture kept.  `findOnDelAtBelow` reads `b` and `v` back to their
defaults under the chain's premise, that the deleted node is no mapping (a mapping keeps its members).  A
read at an index (`kept`, `gone`) checks its bound in the state it runs in (`p[i]@S`), and no law yet reads
through a deleted root (`select(delAt(S, ledger), ledger)`) or past such a check, so `MappingDelete` ends
short of the printed `10`, `0`, `0`.
-/

namespace Solidity.Examples.Chains.StorageDelete

/-! ## Example: Storage Delete Cases -/

local instance : InContract := ⟨TestSuite⟩
section
variable (m : Modality) (φ : Post TestSuite)

namespace SubtreeDelete
variable (hk : STerm.KindFreeAt st!{ save(save(select(storage, alice), account.balance, 100), account.token.value, 7) } pt!{ account })

/-- `alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
b = alice.account.balance; v = alice.account.token.value;` run: the paper's `⇝*` through the two nested
writes (`S₁`), the delete (`S₂`), the two reads, each through the aliases it binds, and the merge. -/
theorem run :
    dl![m]{ ⟨[ alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
        b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          ⟨[ delete alice.account; b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    ~[storageFieldDelete]~> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          { storage := delAt(storage, alice.account) }
          ⟨[ b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          { storage := delAt(storage, alice.account) } { sp4 := alice.account } { b := find(storage, sp4.balance) }
          ⟨[ v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          { storage := delAt(storage, alice.account) } { sp4 := alice.account } { b := find(storage, sp4.balance) }
          { sp6 := alice.account } { sp5 := sp6.token } { v := find(storage, sp5.value) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖
            b :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.balance) ‖
            sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.token.value) }
          φ } := by
  sol_chain

include hk in
/-- The reads of the merged line resolved as solkey reads a path, a member at a time: from its head
(`findMemberCons`), the delete and the writes seen from `alice` (`selectOnDelAtMember`,
`selectOnSaveMemberIn`, the writes under the delete), and the word below the deleted node read back to its
default (`findOnDelAtBelow`), under `hk`: the `account` node of `alice`, after the writes, is no mapping. -/
theorem reads :
    dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖
            b :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.balance) ‖
            sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.token.value) }
          φ }
    ~[findMemberCons]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖
            b :=
              find(select(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                  alice),
                account.balance) ‖
            sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.token.value) }
          φ }
    ~[selectOnDelAtMember]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖
            b :=
              find(delAt(select(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice),
                  account),
                account.balance) ‖
            sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.token.value) }
          φ }
    ~[selectOnSaveMemberIn]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖
            b :=
              find(delAt(save(select(save(storage, alice.account.balance, 100), alice), account.token.value, 7), account),
                account.balance) ‖
            sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.token.value) }
          φ }
    ~[selectOnSaveMemberIn]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖
            b :=
              find(delAt(save(save(select(storage, alice), account.balance, 100), account.token.value, 7), account),
                account.balance) ‖
            sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.token.value) }
          φ }
    ~[findOnDelAtBelow]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖ b := 0 ‖ sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                alice.account.token.value) }
          φ }
    ~[findMemberCons]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖ b := 0 ‖ sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(select(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account),
                  alice),
                account.token.value) }
          φ }
    ~[selectOnDelAtMember]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖ b := 0 ‖ sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(select(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice),
                  account),
                account.token.value) }
          φ }
    ~[selectOnSaveMemberIn]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖ b := 0 ‖ sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(select(save(storage, alice.account.balance, 100), alice), account.token.value, 7), account),
                account.token.value) }
          φ }
    ~[selectOnSaveMemberIn]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖ b := 0 ‖ sp6 := alice.account ‖ sp5 := alice.account.token ‖
            v :=
              find(delAt(save(save(select(storage, alice), account.balance, 100), account.token.value, 7), account),
                account.token.value) }
          φ }
    ~[findOnDelAtBelow]~> dl![m]{
        { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
            storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
            sp4 := alice.account ‖ b := 0 ‖ sp6 := alice.account ‖ sp5 := alice.account.token ‖ v := 0 }
          φ } := by
  sol_chain

include hk in
/-- `alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
b = alice.account.balance; v = alice.account.token.value;`: `run` then `reads`. -/
theorem chain :
    dl![m]{ ⟨[ alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
        b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    ~~> dl![m]{ { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
        storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
        sp4 := alice.account ‖ b := 0 ‖ sp6 := alice.account ‖ sp5 := alice.account.token ‖ v := 0 } φ } :=
  (run ..).leads.via (reads (hk := hk) ..)
#last_line chain
end SubtreeDelete

namespace IndexDelete
def names : FreshTable := [("toks", "sp1"), ("idx", "se2"), ("arr", "sp3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `delete bucket.tokens[++i]; len = bucket.tokens.length;` with `i` 2.  The elaborator captures the index
before the statement (`uint idx; idx = ++i; delete toks[idx];`, the paper's first `⇝*`); the run binding
`toks`, `idx` and `i`; `storageIndexArrayDelete` writing `delAt` at the element (the in-bounds branch
only); the length read through `arr`; the merge, which resolves the element to `bucket.tokens[2 + 1]`; the
delete does not touch the length (`lenOnDelAtFrame`), and the index folds to `3`. -/
theorem chain :
    dl![m]{ { i := 2 } ⟨[ delete bucket.tokens[++i]; len = bucket.tokens.length; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          ⟨[ delete toks[idx]; len = bucket.tokens.length; ]⟩ φ }
    ~[storageIndexArrayDelete]~> dl![m]{ { i := 2 } { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          { storage := delAt(storage, toks[idx]) } ⟨[ len = bucket.tokens.length; ]⟩ φ }
    ~*> dl![m]{ { i := 2 } { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          { storage := delAt(storage, toks[idx]) } { arr := bucket.tokens } { len := arr.length } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ toks := bucket.tokens ‖ idx := 0 ‖ i := 2 + 1 ‖ idx := 2 + 1 ‖
            storage := delAt(storage, bucket.tokens[2 + 1]) ‖ arr := bucket.tokens ‖
            len := find(delAt(storage, bucket.tokens[2 + 1]), bucket.tokens.length) }
          φ }
    ~[lenOnDelAtFrame]~> dl![m]{
        { i := 2 ‖ toks := bucket.tokens ‖ idx := 0 ‖ i := 2 + 1 ‖ idx := 2 + 1 ‖
            storage := delAt(storage, bucket.tokens[2 + 1]) ‖ arr := bucket.tokens ‖ len := bucket.tokens.length }
          φ }
    ~[add_literals]~> dl![m]{
        { i := 2 ‖ toks := bucket.tokens ‖ idx := 0 ‖ i := 3 ‖ idx := 3 ‖ storage := delAt(storage, bucket.tokens[3]) ‖
            arr := bucket.tokens ‖ len := bucket.tokens.length }
          φ } := by
  sol_chain
#last_line chain
end IndexDelete

namespace MappingDelete
/-- `ledger.nonce = 5; ledger.balances[1] = 10; delete ledger; kept = ledger.balances[1];
delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1];`: the two writes (`S₄`, the paper's
`⇝*`), `delete ledger;` (`storageRootDelete`, `S₅`), the read of `kept` with the keyed delete
(`storageIndexDelete`, no bounds branch, `S₆`), then `nonce` and `gone`; the merge, the value deleted at
`gone`'s key read as its default (`findOnDelAtValue`), the keyed delete framed out of `nonce`
(`findOnDelAtFrame`), and `nonce` read from its head (`findMemberCons`). -/
theorem chain :
    dl![m]{ ⟨[ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger; kept = ledger.balances[1];
        delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 }
            { sp1 := ledger.balances }
              { ie1 := 1 }
                { storage := save(storage, sp1[ie1], se1) }
                  ⟨[ delete ledger; kept = ledger.balances[1]; delete ledger.balances[1]; nonce = ledger.nonce;
                    gone = ledger.balances[1]; ]⟩ φ }
    ~[storageRootDelete]~> dl![m]{
        { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 }
            { sp1 := ledger.balances }
              { ie1 := 1 }
                { storage := save(storage, sp1[ie1], se1) }
                  { storage := delAt(storage, ledger) }
                    ⟨[ kept = ledger.balances[1]; delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1];
                      ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 }
            { sp1 := ledger.balances }
              { ie1 := 1 }
                { storage := save(storage, sp1[ie1], se1) }
                  { storage := delAt(storage, ledger) }
                    { sp2 := ledger.balances }
                      { kept := find(storage, sp2[1]) }
                        { sp3 := ledger.balances }
                          { storage := delAt(storage, sp3[1]) } ⟨[ nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 }
            { sp1 := ledger.balances }
              { ie1 := 1 }
                { storage := save(storage, sp1[ie1], se1) }
                  { storage := delAt(storage, ledger) }
                    { sp2 := ledger.balances }
                      { kept := find(storage, sp2[1]) }
                        { sp3 := ledger.balances }
                          { storage := delAt(storage, sp3[1]) }
                            { nonce := find(storage, ledger.nonce) }
                              { sp4 := ledger.balances } { gone := find(storage, sp4[1]) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ sp2 := ledger.balances ‖
            kept :=
              find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10), ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            sp3 := ledger.balances ‖
            storage :=
              delAt(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                  ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            nonce :=
              find(delAt(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger),
                  ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                        ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                      ledger)),
                ledger.nonce) ‖
            sp4 := ledger.balances ‖
            gone :=
              find(delAt(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger),
                  ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                        ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                      ledger)),
                ledger.balances[1]@delAt(delAt(save(save(storage, ledger.nonce, 5),
                        ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                      ledger),
                    ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                          ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                        ledger))) }
          φ }
    ~[findOnDelAtValue]~> dl![m]{
        { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ sp2 := ledger.balances ‖
            kept :=
              find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10), ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            sp3 := ledger.balances ‖
            storage :=
              delAt(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                  ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            nonce :=
              find(delAt(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger),
                  ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                        ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                      ledger)),
                ledger.nonce) ‖
            sp4 := ledger.balances ‖
            gone :=
              delValue(find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger),
                  ledger.balances[1]@delAt(delAt(save(save(storage, ledger.nonce, 5),
                          ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                        ledger),
                      ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                            ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                          ledger)))) }
          φ }
    ~[findOnDelAtFrame]~> dl![m]{
        { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ sp2 := ledger.balances ‖
            kept :=
              find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10), ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            sp3 := ledger.balances ‖
            storage :=
              delAt(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                  ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            nonce :=
              find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10), ledger),
                ledger.nonce) ‖
            sp4 := ledger.balances ‖
            gone :=
              delValue(find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger),
                  ledger.balances[1]@delAt(delAt(save(save(storage, ledger.nonce, 5),
                          ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                        ledger),
                      ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                            ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                          ledger)))) }
          φ }
    ~[findMemberCons]~> dl![m]{
        { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ sp2 := ledger.balances ‖
            kept :=
              find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10), ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            sp3 := ledger.balances ‖
            storage :=
              delAt(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                  ledger),
                ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                      ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger)) ‖
            nonce :=
              select(select(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger),
                  ledger),
                nonce) ‖
            sp4 := ledger.balances ‖
            gone :=
              delValue(find(delAt(save(save(storage, ledger.nonce, 5), ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                    ledger),
                  ledger.balances[1]@delAt(delAt(save(save(storage, ledger.nonce, 5),
                          ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                        ledger),
                      ledger.balances[1]@delAt(save(save(storage, ledger.nonce, 5),
                            ledger.balances[1]@save(storage, ledger.nonce, 5), 10),
                          ledger)))) }
          φ } := by
  sol_chain
#last_line chain
end MappingDelete

end
end Solidity.Examples.Chains.StorageDelete
