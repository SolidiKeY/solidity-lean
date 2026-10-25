import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

/-!
# An ERC20 token in Velvet

`mint` and `transferFrom` of an ERC20 token:

```solidity
function mint(address to, uint amount) public {
  totalSupply += amount;
  balanceOf[to] += amount;
}
function transferFrom(address from, address to, uint amount) public {
  allowance[from][msg.sender] -= amount;
  balanceOf[from] -= amount;
  balanceOf[to] += amount;
}
```

Accounts are indices into the ledger (`to` is a Lean keyword, so the
parameters are `src` and `dst`). `allowance` is the row of
`msg.sender`, the spender: `allowance[from]` is what it may still move from
`from`. A `mut` parameter is a storage variable the method writes, and
`totalSupplyOld` its value on entry. The requires are the calls that do not
revert, and amounts are unbounded `Nat`s (`Bank.lean` bounds one).
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section SolidityVelvetToken

-- `totalSupply += amount; balanceOf[to] += amount;`
method mint (mut balances : Array Nat) (mut totalSupply : Nat) (dst : Nat) (amount : Nat)
    return (u : Unit)
  require dst < balances.size
  ensures totalSupply = totalSupplyOld + amount
  ensures balances.size = balancesOld.size
  ensures balances[dst]! = balancesOld[dst]! + amount
  ensures ∀ j, j ≠ dst → balances[j]! = balancesOld[j]!
  do
    totalSupply := totalSupply + amount
    balances[dst] += amount
    return

prove_correct mint by
  loom_solve

/-- info: DivM.res ((), #[0, 5], 15) -/
#guard_msgs in
#eval (mint #[0, 0] 10 1 5).run

-- The spender's allowance and the owner's balance go down, the recipient's up.
method transferFrom (mut balances : Array Nat) (mut allowance : Array Nat)
    (src : Nat) (dst : Nat) (amount : Nat) return (u : Unit)
  require src < balances.size
  require dst < balances.size
  require src < allowance.size
  require src ≠ dst
  require amount ≤ allowance[src]!
  require amount ≤ balances[src]!
  ensures allowance[src]! + amount = allowanceOld[src]!
  ensures balances[src]! + amount = balancesOld[src]!
  ensures balances[dst]! = balancesOld[dst]! + amount
  ensures ∀ j, j ≠ src → j ≠ dst → balances[j]! = balancesOld[j]!
  ensures balances[src]! + balances[dst]! = balancesOld[src]! + balancesOld[dst]!
  do
    allowance[src] := allowance[src]! - amount
    balances[src] := balances[src]! - amount
    balances[dst] += amount
    return

prove_correct transferFrom by
  loom_solve

/-- info: DivM.res ((), #[6, 4, 0], #[1, 0, 0]) -/
#guard_msgs in
#eval (transferFrom #[10, 0, 0] #[5, 0, 0] 0 1 4).run

end SolidityVelvetToken
