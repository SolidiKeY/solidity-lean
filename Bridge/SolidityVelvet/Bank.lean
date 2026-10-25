import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

/-!
# A bank in Velvet

The deposit and withdraw of a bank contract, over a ledger of balances
indexed by account:

```solidity
function deposit(uint amount) public { balanceOf[msg.sender] += amount; }
function withdraw(uint amount) public {
  require(amount <= balanceOf[msg.sender]);
  balanceOf[msg.sender] -= amount;
}
```

A Solidity `uint` is bounded and `+=` reverts past `2^256 - 1`; a Velvet
`Nat` is not, so `deposit` requires the sum to fit, which is the call that
does not revert. Each method says what it changes and, with a `∀`, what it
leaves alone: the other accounts' balances.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section SolidityVelvetBank

-- `balanceOf[who] += amount`, for a call that does not overflow.
method deposit (mut balances : Array Nat) (who : Nat) (amount : Nat) return (u : Unit)
  require who < balances.size
  require balances[who]! + amount < 2 ^ 256
  ensures balances.size = balancesOld.size
  ensures balances[who]! = balancesOld[who]! + amount
  ensures balances[who]! < 2 ^ 256
  ensures ∀ j, j ≠ who → balances[j]! = balancesOld[j]!
  do
    balances[who] += amount
    return

prove_correct deposit by
  loom_solve

/-- info: DivM.res ((), #[5, 3]) -/
#guard_msgs in
#eval (deposit #[5, 1] 1 2).run

-- `require(amount <= balanceOf[who]); balanceOf[who] -= amount;`
method withdraw (mut balances : Array Nat) (who : Nat) (amount : Nat) return (u : Unit)
  require who < balances.size
  require amount ≤ balances[who]!
  ensures balances.size = balancesOld.size
  ensures balances[who]! + amount = balancesOld[who]!
  ensures ∀ j, j ≠ who → balances[j]! = balancesOld[j]!
  do
    balances[who] := balances[who]! - amount
    return

prove_correct withdraw by
  loom_solve

/-- info: DivM.res ((), #[2, 1]) -/
#guard_msgs in
#eval (withdraw #[5, 1] 0 3).run

end SolidityVelvetBank
