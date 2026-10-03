import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The storage `delete` examples as chains

The calculus's storage `delete` examples, each a chain over any modality `m` and postcondition `φ`
(`Examples/Chains/Storage.lean` says how to read one), in `TestSuite`.  `bucket.tokens` stands for
`alice.account.tokens`.  The strategy's lines alias one member at a time and index by captures, so they are
crossed unwritten; the merges give the printed lines (`S₁`, `S₂`, the reads through them), and
`findOnDelAtBelow` reads `b` and `v` back to their defaults under the chain's premise, that the deleted node
is no mapping (a mapping keeps its members).  A read at an index (`kept`, `gone`) checks its bound in the
state it runs in, so it does not merge under a storage write and stays as the rules leave it.
-/

namespace Solidity.Examples.Chains.StorageDelete

/-! ## Example: Storage Delete Cases -/

local instance : InContract := ⟨TestSuite⟩
section
variable (m : Modality) (φ : Post TestSuite)

namespace SubtreeDelete

set_option maxHeartbeats 4000000 in
/-- the two nested writes, `delete alice.account;`, then the leaves read back: the stack the strategy
leaves, merged (the printed `S₂`, the delete over the two writes `S₁`, read by `b` and `v`), its captures
dropped, and each read resolved as solkey reads it, a member at a time — the path from its head
(`findMemberCons`), the delete and the writes seen from `alice` (`selectOnDelAtMember`,
`selectOnSaveMemberIn`, the writes under the delete), and the word below the deleted node read back to its default
(`findOnDelAtBelow`), under the premise that the `account` node of `alice`, after the writes, is no
mapping (which keeps its members). -/
def chain (hk : STerm.KindFreeAt st!{ save(save(select(storage, alice), account.balance, 100), account.token.value, 7) } pt!{ account }) :
    dl![m]{ ⟨[ alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
        b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    ~~> dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖ b := 0 ‖ v := 0 } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
        b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { se1 := 100 ‖ sp1 := alice.account ‖ se2 := 7 ‖ sp3 := alice.account ‖ sp2 := alice.account.token ‖
          storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
          sp4 := alice.account ‖ b := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.balance) ‖
          sp6 := alice.account ‖ sp5 := alice.account.token ‖
          v := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.token.value) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
          b := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.balance) ‖
          v := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.token.value) } φ } := by sol_chain
    _ ~[findMemberCons]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
          b := find(select(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice), account.balance) ‖
          v := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.token.value) } φ } := by sol_chain
    _ ~[selectOnDelAtMember]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
          b := find(delAt(select(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice), account), account.balance) ‖
          v := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.token.value) } φ } := by sol_chain
    _ ~[selectOnSaveMemberIn]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
          b := find(delAt(save(select(save(storage, alice.account.balance, 100), alice), account.token.value, 7), account), account.balance) ‖
          v := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.token.value) } φ } := by sol_chain
    _ ~[selectOnSaveMemberIn]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖
          b := find(delAt(save(save(select(storage, alice), account.balance, 100), account.token.value, 7), account), account.balance) ‖
          v := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.token.value) } φ } := by sol_chain
    _ ~[findOnDelAtBelow]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖ b := 0 ‖
          v := find(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice.account.token.value) } φ } := by sol_chain
    _ ~[findMemberCons]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖ b := 0 ‖
          v := find(select(delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account), alice), account.token.value) } φ } := by sol_chain
    _ ~[selectOnDelAtMember]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖ b := 0 ‖
          v := find(delAt(select(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice), account), account.token.value) } φ } := by sol_chain
    _ ~[selectOnSaveMemberIn]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖ b := 0 ‖
          v := find(delAt(save(select(save(storage, alice.account.balance, 100), alice), account.token.value, 7), account), account.token.value) } φ } := by
      sol_chain
    _ ~[selectOnSaveMemberIn]~>
        dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖ b := 0 ‖
          v := find(delAt(save(save(select(storage, alice), account.balance, 100), account.token.value, 7), account), account.token.value) } φ } := by sol_chain
    _ ~[findOnDelAtBelow]~> dl![m]{ { storage := delAt(save(save(storage, alice.account.balance, 100), alice.account.token.value, 7), alice.account) ‖ b := 0 ‖ v := 0 } φ } := by sol_chain
#last_line chain
end SubtreeDelete

namespace IndexDelete
def names : FreshTable := [("toks", "sp1"), ("idx", "se2"), ("arr", "sp3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `delete bucket.tokens[++i]; len = bucket.tokens.length;`: the index captured by the elaborator (an equality), the captures merged and the dead `idx := 0` dropped, `storageIndexArrayDelete` writing `delAt` at the element (the in-bounds branch only; the line indexes by the capture, so it is crossed unwritten, and its merge resolves the element to `bucket.tokens[i + 1]`), then the length read through `arr`, left as the stack of its updates. -/
def stack :
    dl![m]{ ⟨[ delete bucket.tokens[++i]; len = bucket.tokens.length; ]⟩ φ }
    ~~> dl![m]{ { toks := bucket.tokens ‖ i := i + 1 ‖ idx := i + 1 ‖ storage := delAt(storage, bucket.tokens[i + 1]) }
          { arr := bucket.tokens } { len := arr.length } φ } :=
  calc dl![m]{ ⟨[ delete bucket.tokens[++i]; len = bucket.tokens.length; ]⟩ φ }
    _ = dl![m]{ ⟨[ Token[] storage toks = bucket.tokens; uint idx; idx = ++i; delete toks[idx];
          len = bucket.tokens.length; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          ⟨[ delete toks[idx]; len = bucket.tokens.length; ]⟩ φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { toks := bucket.tokens ‖ idx := 0 ‖ i := i + 1 ‖ idx := i + 1 }
          ⟨[ delete toks[idx]; len = bucket.tokens.length; ]⟩ φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { toks := bucket.tokens ‖ i := i + 1 ‖ idx := i + 1 }
          ⟨[ delete toks[idx]; len = bucket.tokens.length; ]⟩ φ } := by sol_chain
    _ ~[storageIndexArrayDelete]~> _ := by sol_chain
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { toks := bucket.tokens ‖ i := i + 1 ‖ idx := i + 1 ‖ storage := delAt(storage, bucket.tokens[i + 1]) }
          { arr := bucket.tokens } { len := arr.length } φ } := by sol_chain

/-- The alias `arr` merged with the length read through it. -/
def merged :
    dl![m]{ { toks := bucket.tokens ‖ i := i + 1 ‖ idx := i + 1 ‖ storage := delAt(storage, bucket.tokens[i + 1]) }
          { arr := bucket.tokens } { len := arr.length } φ }
    ~[sequentialToParallel]~>
        dl![m]{ { toks := bucket.tokens ‖ i := i + 1 ‖ idx := i + 1 ‖ storage := delAt(storage, bucket.tokens[i + 1]) }
          { arr := bucket.tokens ‖ len := bucket.tokens.length } φ } := by sol_chain

/-- The two segments (one chain is over the budget of a single
declaration).  The read under the delete merges too (`Upd.mergeStL`), to
`len := find(delAt(storage, bucket.tokens[i + 1]), bucket.tokens.length)`,
which `lenOnDelAtFrame` resolves to `bucket.tokens.length`: the lines after
this one. -/
def chain :
    dl![m]{ ⟨[ delete bucket.tokens[++i]; len = bucket.tokens.length; ]⟩ φ }
    ~~> dl![m]{ { toks := bucket.tokens ‖ i := i + 1 ‖ idx := i + 1 ‖ storage := delAt(storage, bucket.tokens[i + 1]) }
          { arr := bucket.tokens ‖ len := bucket.tokens.length } φ } :=
  calc dl![m]{ ⟨[ delete bucket.tokens[++i]; len = bucket.tokens.length; ]⟩ φ }
    _ ~~> _ := stack m φ
    _ ~[sequentialToParallel]~> _ := merged m φ
end IndexDelete

namespace MappingDelete
set_option maxHeartbeats 1000000 in
/-- the ledger program: two writes, `delete ledger;` (`storageRootDelete`), the read of `kept`, the keyed delete (`storageIndexDelete`, no bounds branch), then `nonce` and `gone`.  The indexed write is crossed unwritten (it indexes by the capture `ie1`) and merged with its captures; past it the reads and writes at an index check their bound in the state they run in, so no storage write merges over them: the chain ends at the stack, each alias merged with the read or write through it. -/
def chain :
    dl![m]{ ⟨[ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger; kept = ledger.balances[1];
        delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ storage := save(storage, ledger.balances[1], 10) }
          { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances ‖ kept := find(storage, ledger.balances[1]) }
          { sp3 := ledger.balances ‖ storage := delAt(storage, ledger.balances[1]) }
          { nonce := find(storage, ledger.nonce) ‖ sp4 := ledger.balances ‖ gone := find(storage, ledger.balances[1]) } φ } :=
  calc dl![m]{ ⟨[ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger; kept = ledger.balances[1];
        delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ }
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { storage := save(storage, ledger.nonce, 5) }
          ⟨[ ledger.balances[1] = 10; delete ledger; kept = ledger.balances[1]; delete ledger.balances[1];
            nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ } := rfl
    _ ~[storageIndexWriteCaptureAllComplexRecv]~>
        dl![m]{ { storage := save(storage, ledger.nonce, 5) }
          ⟨[ uint se1 = 10; mapping(uint => uint) storage sp1 = ledger.balances; uint ie1 = 1; sp1[ie1] = se1;
            delete ledger; kept = ledger.balances[1]; delete ledger.balances[1]; nonce = ledger.nonce;
            gone = ledger.balances[1]; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { storage := save(storage, ledger.nonce, 5) } { se1 := 10 } { sp1 := ledger.balances } { ie1 := 1 }
          ⟨[ sp1[ie1] = se1; delete ledger; kept = ledger.balances[1]; delete ledger.balances[1]; nonce = ledger.nonce;
            gone = ledger.balances[1]; ]⟩ φ } := by sol_chain
    _ ~[storageIndexWriteMappingSave]~> _ := by sol_chain
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ storage := save(storage, ledger.balances[1], 10) }
          { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances } { kept := find(storage, sp2[1]) }
          { sp3 := ledger.balances } { storage := delAt(storage, sp3[1]) }
          { nonce := find(storage, ledger.nonce) }
          { sp4 := ledger.balances } { gone := find(storage, sp4[1]) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ storage := save(storage, ledger.balances[1], 10) }
          { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances ‖ kept := find(storage, ledger.balances[1]) }
          { sp3 := ledger.balances } { storage := delAt(storage, sp3[1]) }
          { nonce := find(storage, ledger.nonce) }
          { sp4 := ledger.balances } { gone := find(storage, sp4[1]) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ storage := save(storage, ledger.balances[1], 10) }
          { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances ‖ kept := find(storage, ledger.balances[1]) }
          { sp3 := ledger.balances ‖ storage := delAt(storage, ledger.balances[1]) }
          { nonce := find(storage, ledger.nonce) }
          { sp4 := ledger.balances } { gone := find(storage, sp4[1]) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, ledger.nonce, 5) }
          { se1 := 10 ‖ sp1 := ledger.balances ‖ ie1 := 1 ‖ storage := save(storage, ledger.balances[1], 10) }
          { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances ‖ kept := find(storage, ledger.balances[1]) }
          { sp3 := ledger.balances ‖ storage := delAt(storage, ledger.balances[1]) }
          { nonce := find(storage, ledger.nonce) ‖ sp4 := ledger.balances ‖ gone := find(storage, ledger.balances[1]) } φ } := by
      sol_chain
end MappingDelete

end
end Solidity.Examples.Chains.StorageDelete
