import SolidityVelvet.Contract

/-!
# Loops over storage arrays in Velvet

Three loops a contract runs over its storage arrays, as Solidity
(`Bridge/SolidityVelvet/Contract.lean`), each with the invariant that proves it.

`totalBalance` is specified by a recursive sum (`sumTo`, a Lean function the
specification calls), `indexOf` by what its result is when the holder is
found and when it is not, and `winningProposal` as the index of a largest
count, the first one on a tie. Their reads stay inside the arrays, so no
index reverts; `totalBalance`'s `+=` reverts past `2^256 - 1`.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-- The sum of the first `n` balances. -/
def sumTo (a : Array Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo a n + a[n]!

@[grind] theorem sumTo_succ (a : Array Nat) (n : Nat) :
    sumTo a (n + 1) = sumTo a n + a[n]! := rfl

@[grind] theorem sumTo_zero (a : Array Nat) : sumTo a 0 = 0 := rfl

contract Registry {
  uint[] balances;
  address[] holders;
  uint[] votes;

  function totalBalance() public view returns (uint s)
    ensures s == sumTo(balances, balances.length)
  {
    for (uint i = 0; i < balances.length; i++)
      invariant i <= balances.length
      invariant s == sumTo(balances, i)
    {
      s += balances[i];
    }
  }

  function indexOf(address who) public view returns (uint i)
    ensures i <= holders.length
    ensures i < holders.length ==> holders[i] == who
    ensures forall (uint j) j < i ==> holders[j] != who
  {
    while (i < holders.length && holders[i] != who)
      invariant i <= holders.length
      invariant forall (uint j) j < i ==> holders[j] != who
    {
      i++;
    }
  }

  function winningProposal() public view returns (uint w)
    ensures w < votes.length
    ensures forall (uint j) j < votes.length ==> votes[j] <= votes[w]
    ensures forall (uint j) j < w ==> votes[j] < votes[w]
  {
    require(votes.length > 0);
    for (uint p = 1; p < votes.length; p++)
      invariant 1 <= p && p <= votes.length
      invariant w < p
      invariant forall (uint j) j < p ==> votes[j] <= votes[w]
      invariant forall (uint j) j < w ==> votes[j] < votes[w]
    {
      if (votes[p] > votes[w]) w = p;
    }
  }
}

prove_correct Registry.totalBalance by
  loom_solve

prove_correct Registry.indexOf by
  loom_solve

prove_correct Registry.winningProposal by
  loom_solve

/-- info: DivM.res 12 -/
#guard_msgs in
#eval (Registry.totalBalance #[3, 4, 5]).run

/-- info: DivM.res 1 -/
#guard_msgs in
#eval (Registry.indexOf #[7, 9, 9] 9).run

/-- info: DivM.res 3 -/
#guard_msgs in
#eval (Registry.indexOf #[7, 9, 9] 4).run

/-- info: DivM.res 1 -/
#guard_msgs in
#eval (Registry.winningProposal #[2, 5, 5, 1]).run
