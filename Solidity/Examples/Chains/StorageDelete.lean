import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The storage `delete` examples as chains

The calculus's storage `delete` examples, each a chain over any modality `m` and postcondition `φ`
(`Examples/Chains/Storage.lean` says how to read one), in `TestSuite`.  `bucket.tokens` stands for
`alice.account.tokens`.  Each chain keeps the updates as the rules leave them and stops there: the printed
lines merge them and read `b`, `v`, `kept`, `nonce`, `gone` through the `delAt` marker, which is the Theory's
(`deleteSubtreeBalance` in `Examples/Tactics/Theory.lean`), not a link, and two storage writes do not merge
(`{ storage := … ‖ storage := … }` is stuck) over a variable modality.  The anchors are the printed lines, as
updates.
-/

namespace Solidity.Examples.Chains.StorageDelete

/-! ## Example: Storage Delete Cases -/

local instance : InContract := ⟨TestSuite⟩
section
variable (m : Modality) (φ : Post TestSuite)

namespace SubtreeDelete

/-- the two nested writes, `delete alice.account;`, then the leaves read back.  The anchors: the two writes (printed `S₁`), the delete (`S₂`), the read of `b`, the read of `v`. -/
def chain :
    dl![m]{ ⟨[ alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
        b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    ~*> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          { storage := delAt(storage, alice.account) }
          { sp4 := alice.account } { b := find(storage, sp4.balance) }
          { sp6 := alice.account } { sp5 := sp6.token } { v := find(storage, sp5.value) } φ } :=
  calc dl![m]{ ⟨[ alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
        b = alice.account.balance; v = alice.account.token.value; ]⟩ φ }
    _ ~*> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          ⟨[ delete alice.account; b = alice.account.balance; v = alice.account.token.value; ]⟩ φ } := by sol_chain
    _ ~[storageFieldDelete]~>
        dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          { storage := delAt(storage, alice.account) }
          ⟨[ b = alice.account.balance; v = alice.account.token.value; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          { storage := delAt(storage, alice.account) }
          { sp4 := alice.account } { b := find(storage, sp4.balance) }
          ⟨[ v = alice.account.token.value; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { se1 := 100 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
          { se2 := 7 } { sp3 := alice.account } { sp2 := sp3.token } { storage := save(storage, sp2.value, se2) }
          { storage := delAt(storage, alice.account) }
          { sp4 := alice.account } { b := find(storage, sp4.balance) }
          { sp6 := alice.account } { sp5 := sp6.token } { v := find(storage, sp5.value) } φ } := by sol_chain
end SubtreeDelete

namespace IndexDelete
def names : FreshTable := [("toks", "sp1"), ("idx", "se2"), ("arr", "sp3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty
/-- `delete bucket.tokens[++i]; len = bucket.tokens.length;`: the index captured by the elaborator (an equality), `storageIndexArrayDelete` writing `delAt` at the element (the in-bounds branch only), then the length read. -/
def chain :
    dl![m]{ ⟨[ delete bucket.tokens[++i]; len = bucket.tokens.length; ]⟩ φ }
    ~*> dl![m]{ { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          { storage := delAt(storage, toks[idx]) } { arr := bucket.tokens } { len := arr.length } φ } :=
  calc dl![m]{ ⟨[ delete bucket.tokens[++i]; len = bucket.tokens.length; ]⟩ φ }
    _ = dl![m]{ ⟨[ Token[] storage toks = bucket.tokens; uint idx; idx = ++i; delete toks[idx];
          len = bucket.tokens.length; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          ⟨[ delete toks[idx]; len = bucket.tokens.length; ]⟩ φ } := by sol_chain
    _ ~[storageIndexArrayDelete]~>
        dl![m]{ { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          { storage := delAt(storage, toks[idx]) } ⟨[ len = bucket.tokens.length; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { toks := bucket.tokens } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
          { storage := delAt(storage, toks[idx]) } { arr := bucket.tokens } { len := arr.length } φ } := by sol_chain
end IndexDelete

namespace MappingDelete
/-- the ledger program: two writes, `delete ledger;` (`storageRootDelete`), the read of `kept`, the keyed delete (`storageIndexDelete`, no bounds branch), then `nonce` and `gone`. -/
def chain :
    dl![m]{ ⟨[ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger; kept = ledger.balances[1];
        delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, ledger.nonce, 5) } { se1 := 10 } { sp1 := ledger.balances } { ie1 := 1 }
          { storage := save(storage, sp1[ie1], se1) } { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances } { kept := find(storage, sp2[1]) }
          { sp3 := ledger.balances } { storage := delAt(storage, sp3[1]) }
          { nonce := find(storage, ledger.nonce) }
          { sp4 := ledger.balances } { gone := find(storage, sp4[1]) } φ } :=
  calc dl![m]{ ⟨[ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger; kept = ledger.balances[1];
        delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ }
    _ ~*> dl![m]{ { storage := save(storage, ledger.nonce, 5) } { se1 := 10 } { sp1 := ledger.balances } { ie1 := 1 }
          { storage := save(storage, sp1[ie1], se1) }
          ⟨[ delete ledger; kept = ledger.balances[1]; delete ledger.balances[1]; nonce = ledger.nonce;
            gone = ledger.balances[1]; ]⟩ φ } := by sol_chain
    _ ~[storageRootDelete]~>
        dl![m]{ { storage := save(storage, ledger.nonce, 5) } { se1 := 10 } { sp1 := ledger.balances } { ie1 := 1 }
          { storage := save(storage, sp1[ie1], se1) } { storage := delAt(storage, ledger) }
          ⟨[ kept = ledger.balances[1]; delete ledger.balances[1]; nonce = ledger.nonce;
            gone = ledger.balances[1]; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { storage := save(storage, ledger.nonce, 5) } { se1 := 10 } { sp1 := ledger.balances } { ie1 := 1 }
          { storage := save(storage, sp1[ie1], se1) } { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances } { kept := find(storage, sp2[1]) }
          ⟨[ delete ledger.balances[1]; nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { storage := save(storage, ledger.nonce, 5) } { se1 := 10 } { sp1 := ledger.balances } { ie1 := 1 }
          { storage := save(storage, sp1[ie1], se1) } { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances } { kept := find(storage, sp2[1]) }
          { sp3 := ledger.balances } { storage := delAt(storage, sp3[1]) }
          ⟨[ nonce = ledger.nonce; gone = ledger.balances[1]; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { storage := save(storage, ledger.nonce, 5) } { se1 := 10 } { sp1 := ledger.balances } { ie1 := 1 }
          { storage := save(storage, sp1[ie1], se1) } { storage := delAt(storage, ledger) }
          { sp2 := ledger.balances } { kept := find(storage, sp2[1]) }
          { sp3 := ledger.balances } { storage := delAt(storage, sp3[1]) }
          { nonce := find(storage, ledger.nonce) }
          { sp4 := ledger.balances } { gone := find(storage, sp4[1]) } φ } := by sol_chain
end MappingDelete

end
end Solidity.Examples.Chains.StorageDelete
