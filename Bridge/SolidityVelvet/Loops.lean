import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

/-!
# Loops over storage arrays in Velvet

Three loops a contract runs over a storage array, each with the invariant
that proves it:

```solidity
function totalBalance() view returns (uint s) {
  for (uint i = 0; i < balances.length; i++) s += balances[i];
}
function indexOf(address who) view returns (uint i) {
  while (i < holders.length && holders[i] != who) i++;
}
function winningProposal() view returns (uint w) {
  for (uint p = 1; p < votes.length; p++) if (votes[p] > votes[w]) w = p;
}
```

`totalBalance` is specified by a recursive sum (`sumTo`), `indexOf` by what
its result is when the holder is found and when it is not, and
`winningProposal` as the index of a largest count, the first one on a tie.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section SolidityVelvetLoops

/-- The sum of the first `n` balances. -/
def sumTo (a : Array Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo a n + a[n]!

@[grind] theorem sumTo_succ (a : Array Nat) (n : Nat) :
    sumTo a (n + 1) = sumTo a n + a[n]! := rfl

@[grind] theorem sumTo_zero (a : Array Nat) : sumTo a 0 = 0 := rfl

method totalBalance (balances : Array Nat) return (s : Nat)
  ensures s = sumTo balances balances.size
  do
    let mut s := 0
    let mut i := 0
    while i < balances.size
    invariant i ≤ balances.size
    invariant s = sumTo balances i
    done_with i = balances.size
    do
      s := s + balances[i]!
      i := i + 1
    return s

prove_correct totalBalance by
  loom_solve

/-- info: DivM.res 12 -/
#guard_msgs in
#eval (totalBalance #[3, 4, 5]).run

method indexOf (holders : Array Nat) (who : Nat) return (idx : Nat)
  ensures idx ≤ holders.size
  ensures idx < holders.size → holders[idx]! = who
  ensures ∀ j, j < idx → holders[j]! ≠ who
  do
    let mut i := 0
    while i < holders.size ∧ holders[i]! ≠ who
    invariant i ≤ holders.size
    invariant ∀ j, j < i → holders[j]! ≠ who
    done_with (i = holders.size ∨ holders[i]! = who)
    do
      i := i + 1
    return i

prove_correct indexOf by
  loom_solve

/-- info: DivM.res 1 -/
#guard_msgs in
#eval (indexOf #[7, 9, 9] 9).run

/-- info: DivM.res 3 -/
#guard_msgs in
#eval (indexOf #[7, 9, 9] 4).run

method winningProposal (votes : Array Nat) return (w : Nat)
  require votes.size > 0
  ensures w < votes.size
  ensures ∀ j, j < votes.size → votes[j]! ≤ votes[w]!
  ensures ∀ j, j < w → votes[j]! < votes[w]!
  do
    let mut w := 0
    let mut p := 1
    while p < votes.size
    invariant 1 ≤ p ∧ p ≤ votes.size
    invariant w < p
    invariant ∀ j, j < p → votes[j]! ≤ votes[w]!
    invariant ∀ j, j < w → votes[j]! < votes[w]!
    done_with p = votes.size
    do
      if votes[p]! > votes[w]! then
        w := p
      p := p + 1
    return w

prove_correct winningProposal by
  loom_solve

/-- info: DivM.res 1 -/
#guard_msgs in
#eval (winningProposal #[2, 5, 5, 1]).run

end SolidityVelvetLoops
