import SolidityVelvet.Contract

/-!
# An ERC20 token in Velvet

The token's storage and its `mint`, `transfer`, `approve` and
`transferFrom`, as Solidity
(`Bridge/SolidityVelvet/Contract.lean`).
`allowance[owner][spender]` is what `spender` may still move from `owner`.
A subtraction past zero reverts, and so does an addition past `2^256 - 1`:
the `ensures` are about the calls that do not revert, and none needs a
`require` to rule an underflow out.

`transfer` and `transferFrom` keep the sum of the two balances they touch,
also when an account pays itself; their other postconditions say what
moves when the two accounts differ.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

contract Token {
  uint totalSupply;
  mapping(address => uint) balanceOf;
  mapping(address => mapping(address => uint)) allowance;

  function mint(address dst, uint amount) public
    ensures totalSupply == old(totalSupply) + amount
    ensures balanceOf[dst] == old(balanceOf[dst]) + amount
    ensures forall (address a) a != dst ==> balanceOf[a] == old(balanceOf[a])
  {
    totalSupply += amount;
    balanceOf[dst] += amount;
  }

  function transfer(address dst, uint amount) public
    ensures balanceOf[msg.sender] + balanceOf[dst]
      == old(balanceOf[msg.sender]) + old(balanceOf[dst])
    ensures msg.sender != dst ==> balanceOf[msg.sender] + amount == old(balanceOf[msg.sender])
    ensures msg.sender != dst ==> balanceOf[dst] == old(balanceOf[dst]) + amount
  {
    balanceOf[msg.sender] -= amount;
    balanceOf[dst] += amount;
  }

  function approve(address spender, uint amount) public
    ensures allowance[msg.sender][spender] == amount
    ensures forall (address a) a != msg.sender ==> allowance[a] == old(allowance[a])
  {
    allowance[msg.sender][spender] = amount;
  }

  function transferFrom(address src, address dst, uint amount) public
    ensures allowance[src][msg.sender] + amount == old(allowance[src][msg.sender])
    ensures balanceOf[src] + balanceOf[dst] == old(balanceOf[src]) + old(balanceOf[dst])
    ensures src != dst ==> balanceOf[src] + amount == old(balanceOf[src])
    ensures src != dst ==> balanceOf[dst] == old(balanceOf[dst]) + amount
    ensures forall (address a) a != src && a != dst ==> balanceOf[a] == old(balanceOf[a])
  {
    allowance[src][msg.sender] -= amount;
    balanceOf[src] -= amount;
    balanceOf[dst] += amount;
  }
}

prove_correct Token.mint by
  loom_solve

prove_correct Token.transfer by
  loom_solve

prove_correct Token.approve by
  loom_solve

prove_correct Token.transferFrom by
  loom_solve

/-- info: DivM.res ((), 15, Mapping.ofList [(1, 5)]) -/
#guard_msgs in
#eval (Token.mint 10 default 1 5).run

/-- info: DivM.res ((), Mapping.ofList [(1, 4), (0, 6)]) -/
#guard_msgs in
#eval (Token.transfer (Mapping.ofList [(0, 10)]) 0 1 4).run
