import Solidity.Wp.Verifier

/-!
# `sol_wp` end-to-end examples

A representative slice of the dynamic-logic example suite
(`SemanticsExamples`, `Examples/Taclets/{StorageOps,ValueOps,MemoryOps}`),
re-proved through the wp verifier instead of `native_decide`: every proof
is kernel-checked symbolic execution, and the axiom audit at the bottom
shows the profile `[propext, Classical.choice, Quot.sound]` for each —
no `Lean.ofReduceBool`, no `Lean.trustCompiler`.
-/

namespace Solidity
namespace Wp
namespace ExamplesWP

open Semantics

set_option maxHeartbeats 8000000

/-! ## The two `SemanticsExamples` (`Semantics.lean`) -/

/-- The goal example: write a storage field, read it back. -/
theorem ex1 :
    (sol!{ < alice.account.balance = 10;
             result = alice.account.balance > (result == 10) }).Holds := by
  sol_wp

/-- Pure arithmetic into a stack variable. -/
theorem ex2 : (sol!{ < result = 1 + 2 > (result == 3) }).Holds := by
  sol_wp

/-! ## Storage operations (`Examples/Taclets/StorageOps.lean`) -/

/-- `storage-root-read-write.key` -/
theorem ex3 : (sol!{ < age = 34; result = age > (result == 34) }).Holds := by
  sol_wp

/-- `storage-root-multiple-writes.key` -/
theorem ex4 :
    (sol!{ < age = 1; age = 2; result = age > (result == 2) }).Holds := by
  sol_wp

/-- `storage-field-write-read.key` -/
theorem ex5 :
    (sol!{ < alice.age = 34; result = alice.age > (result == 34) }).Holds := by
  sol_wp

/-- `storage-root-add-assign.key` -/
theorem ex6 :
    (sol!{ < age = 10; age += 5; result = age > (result == 15) }).Holds := by
  sol_wp

/-! ## Value operators (`Examples/Taclets/ValueOps.lean`) -/

/-- `subtraction-simple.key` -/
theorem ex7 : (sol!{ < result = 7 - 2 > (result == 5) }).Holds := by
  sol_wp

/-- `less-than-simple.key` -/
theorem ex8 : (sol!{ < result = (3 < 5) > (result == true) }).Holds := by
  sol_wp

/-- `unary-minus-simple.key` (`x = 5 ->` becomes a declaration) -/
theorem ex9 : (sol!{ < uint x = 5; result = -x > (result == -5) }).Holds := by
  sol_wp

/-! ## Memory operations (`Examples/Taclets/MemoryOps.lean`) -/

/-- `memory-decl-default.key` -/
theorem ex10 :
    (sol!{ < Person memory carol; result = carol.age >
           (result == 0) }).Holds := by
  sol_wp

/-- `memory-deep-field.key` -/
theorem ex11 :
    (sol!{ < Person memory carol;
             carol.account.balance = 10;
             result = carol.account.balance > (result == 10) }).Holds := by
  sol_wp

/-! ## Box modality: reverting programs -/

/-- A reverting head statement validates the box judgment vacuously
(`Box.wpB_cons_revert` fires on the first statement; the rest of the
block and the unprovable postcondition are never reached). -/
theorem ex12 : (sol!{ [ revert(); result = 1 ] (false == true) }).Holds := by
  sol_wp

/-- A zero divisor in `/=` reverts (`StorageOps.lean`, KeY
`storageRootDivAssign` guard): one `wpB_cons_ok` step, then
`wpB_cons_revert`. -/
theorem ex13 : (sol!{ [ age = 10; age /= 0 ] (false == true) }).Holds := by
  sol_wp

/-- `require` violated (`StorageOps.lean`, `requireSimple` "Reverts"):
box `c → φ` holds vacuously. -/
theorem ex14 :
    (sol!{ [ require(false); result = 1 ] (false == true) }).Holds := by
  sol_wp

/-! ## Negative diamond: a halt refutes the judgment -/

/-- `require` violated under diamond (`StorageOps.lean`): the halting head
statement refutes the judgment — `not_holds_diamond_of_halt` with the
interpreter verdict computed by `sol_exec_eval`. -/
theorem ex15 :
    ¬ (sol!{ < require(false); result = 1 > (result == 1) }).Holds :=
  not_holds_diamond_of_halt (by sol_exec_eval)

/-! ## Axiom audit

Expected profile for every theorem above:
`[propext, Classical.choice, Quot.sound]` — in particular no
`Lean.ofReduceBool`/`Lean.trustCompiler` (nothing here evaluates through
the compiler) and no solver-trust axiom. -/

#print axioms ex1
#print axioms ex2
#print axioms ex3
#print axioms ex4
#print axioms ex5
#print axioms ex6
#print axioms ex7
#print axioms ex8
#print axioms ex9
#print axioms ex10
#print axioms ex11
#print axioms ex12
#print axioms ex13
#print axioms ex14
#print axioms ex15

end ExamplesWP
end Wp
end Solidity
