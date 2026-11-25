import Solidity.Goals.Panic
import Solidity.Correctness.Panic.Provenance

/-- The panic-carrying runner satisfies its outcome, provenance and source contracts. -/
theorem Solidity.Semantics.run_panic_codes : Solidity.Goals.runCarriesPanicCodes :=
  ⟨Solidity.Correctness.Panic.run_outcomes, Solidity.Correctness.Panic.code_provenance,
    Solidity.Correctness.Panic.source_association⟩

/--
info: 'Solidity.Semantics.run_panic_codes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Solidity.Semantics.run_panic_codes
