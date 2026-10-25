import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

/-!
# Solidity patterns in Velvet

Velvet (`vendor/CaseStudies/VENDOR.md`) is the Dafny-style verifier built on
Loom: a `method` is a Lean program with `require`/`ensures` and loop
invariants, and `prove_correct … by loom_solve` discharges its verification
conditions with Loom's VC generator and `grind`.

Each method below is the Velvet reading of a Solidity program the core
verifies with its own calculus: the counting loop of
`SolidityBridge/LoomExamples.lean`, a scan for the largest balance, and
ERC20's `transfer` over a ledger of balances. They are Lean programs, not
`Stmt`s: nothing here runs them by `Stmt.run` or relates them to the core's
semantics. The Loom bridge proper is `SolidityBridge/Loom.lean`; this module
imports Velvet alone, so its keywords stay out of `SolidityBridge`.

The semantics are Velvet's partial correctness with demonic choice, as in its
own examples: a `require` is a precondition, not a revert. A method also
runs: each `#eval` pins one execution, the updated ledger returned beside the
result.
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section SolidityVelvet

-- `uint i = 0; while (i < n) { i = i + 1; }`: the counting loop.
method countTo (n : Nat) return (res : Nat)
  ensures res = n
  do
    let mut i := 0
    while i < n
    invariant i ≤ n
    done_with i = n
    do
      i := i + 1
    return i

prove_correct countTo by
  loom_solve

/-- info: DivM.res 3 -/
#guard_msgs in
#eval (countTo 3).run

-- The largest balance of a non-empty ledger.
method maxBalance (balances : Array Nat) return (res : Nat)
  require balances.size > 0
  ensures ∀ j, j < balances.size → balances[j]! ≤ res
  do
    let mut i := 0
    let mut mx := balances[i]!
    i := i + 1
    while i < balances.size
    invariant 0 ≤ i ∧ i ≤ balances.size
    invariant ∀ j, j < i → balances[j]! ≤ mx
    done_with i = balances.size
    do
      let b := balances[i]!
      if b > mx then
        mx := b
      else
        mx := mx
      i := i + 1
    return mx

prove_correct maxBalance by
  loom_solve

/-- info: DivM.res 7 -/
#guard_msgs in
#eval (maxBalance #[3, 7, 5]).run

-- ERC20's `transfer`: `balanceOf[sender] -= amount; balanceOf[recipient] += amount;`,
-- under the precondition that rules its revert out. (`method` takes no doc comment.)
method transfer (mut balances : Array Nat) (sender : Nat) (recipient : Nat) (amount : Nat)
    return (u : Unit)
  require sender < balances.size
  require recipient < balances.size
  require sender ≠ recipient
  require amount ≤ balances[sender]!
  ensures balances.size = balancesOld.size
  ensures balances[sender]! = balancesOld[sender]! - amount
  ensures balances[recipient]! = balancesOld[recipient]! + amount
  do
    balances[sender] := balances[sender]! - amount
    balances[recipient] += amount
    return

prove_correct transfer by
  loom_solve

/-- info: DivM.res ((), #[6, 4]) -/
#guard_msgs in
#eval (transfer #[10, 0] 0 1 4).run

end SolidityVelvet
