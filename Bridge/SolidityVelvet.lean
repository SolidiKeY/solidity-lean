import SolidityVelvet.Contract

/-!
# Solidity patterns in Velvet

Velvet (`vendor/CaseStudies/VENDOR.md`) is the Dafny-style verifier built on
Loom: `prove_correct … by loom_solve` discharges a method's verification
conditions with Loom's VC generator and `grind`. Here the methods are
written as a Solidity contract (`SolidityVelvet/Contract.lean`), and each
function is stated as the Velvet method `Patterns.f`.

The functions are three Solidity programs the core verifies with its own
calculus: the counting loop of `SolidityBridge/LoomExamples.lean`, a scan
for the largest balance, and ERC20's `transfer` over a ledger of balances.
They are Lean programs, not `Stmt`s: nothing here runs them by `Stmt.run` or
relates them to the core's semantics. The Loom bridge proper is
`SolidityBridge/Loom.lean`; this library imports Velvet alone, so its
keywords stay out of `SolidityBridge`.

The semantics are Velvet's partial correctness with demonic choice: a
`require`, an overflow or an index out of range is an `assume`, a revert
with no outcome. A function also runs: each `#eval` pins one execution, the
storage it wrote returned beside the result.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

contract Patterns {
  uint[] balances;
  mapping(address => uint) balanceOf;

  function countTo(uint n) public pure returns (uint i)
    ensures i == n
  {
    while (i < n)
      invariant i <= n
    {
      i++;
    }
  }

  function maxBalance() public view returns (uint mx)
    ensures forall (uint j) j < balances.length ==> balances[j] <= mx
  {
    require(balances.length > 0);
    mx = balances[0];
    for (uint i = 1; i < balances.length; i++)
      invariant 1 <= i && i <= balances.length
      invariant forall (uint j) j < i ==> balances[j] <= mx
    {
      if (balances[i] > mx) mx = balances[i];
    }
  }

  function transfer(address recipient, uint amount) public
    ensures balanceOf[msg.sender] + amount == old(balanceOf[msg.sender])
    ensures balanceOf[recipient] == old(balanceOf[recipient]) + amount
  {
    require(msg.sender != recipient);
    balanceOf[msg.sender] -= amount;
    balanceOf[recipient] += amount;
  }
}

prove_correct Patterns.countTo by
  loom_solve

prove_correct Patterns.maxBalance by
  loom_solve

prove_correct Patterns.transfer by
  loom_solve

/-- info: DivM.res 3 -/
#guard_msgs in
#eval (Patterns.countTo 3).run

/-- info: DivM.res 7 -/
#guard_msgs in
#eval (Patterns.maxBalance #[3, 7, 5]).run

/-- info: DivM.res ((), Mapping.ofList [(1, 4), (0, 6)]) -/
#guard_msgs in
#eval (Patterns.transfer (Mapping.ofList [(0, 10)]) 0 1 4).run
