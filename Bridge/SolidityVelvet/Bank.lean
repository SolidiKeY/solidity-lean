import SolidityVelvet.Contract

/-!
# A bank in Velvet

A bank contract written as Solidity
(`Bridge/SolidityVelvet/Contract.lean`), each function with its
specification, then proved by Velvet one function at a time.

`balanceOf` is a mapping, so an account nobody paid reads zero.
`deposit`'s `+=` reverts past `2^256 - 1` and `withdraw`'s `require`
reverts an overdraft: the `ensures` are about the calls that do not revert.
Each function says what it changes and, with a `forall`, what it leaves
alone: the other accounts' balances.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

contract Bank {
  mapping(address => uint) balanceOf;

  function deposit(uint amount) public
    ensures balanceOf[msg.sender] == old(balanceOf[msg.sender]) + amount
    ensures balanceOf[msg.sender] < 2 ** 256
    ensures forall (address a) a != msg.sender ==> balanceOf[a] == old(balanceOf[a])
  {
    balanceOf[msg.sender] += amount;
  }

  function withdraw(uint amount) public
    ensures balanceOf[msg.sender] + amount == old(balanceOf[msg.sender])
    ensures forall (address a) a != msg.sender ==> balanceOf[a] == old(balanceOf[a])
  {
    require(amount <= balanceOf[msg.sender]);
    balanceOf[msg.sender] -= amount;
  }

  function balance() public view returns (uint b)
    ensures b == balanceOf[msg.sender]
  {
    return balanceOf[msg.sender];
  }
}

prove_correct Bank.deposit by
  loom_solve

prove_correct Bank.withdraw by
  loom_solve

prove_correct Bank.balance by
  loom_solve

/-! A run takes the storage, then `msg.sender`, then the arguments, and
returns the result beside the storage it wrote. -/

/-- info: DivM.res ((), Mapping.ofList [(1, 7)]) -/
#guard_msgs in
#eval (Bank.deposit (Mapping.ofList [(1, 5)]) 1 2).run

/-- info: DivM.res ((), Mapping.ofList [(0, 2), (1, 1)]) -/
#guard_msgs in
#eval (Bank.withdraw (Mapping.ofList [(0, 5), (1, 1)]) 0 3).run

/-- info: DivM.res 5 -/
#guard_msgs in
#eval (Bank.balance (Mapping.ofList [(0, 5)]) 0).run
