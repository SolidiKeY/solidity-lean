import Solidity.Frontend.Testing
import Solidity.Calculus.Close
import Solidity.Calculus.Closers

/-! The Solidity 0.8.38 aggregate fixture, including singleton literals. -/
solc_import "../../../tests/solc/Aggregates.ast.json" hash 0xacca6911aae737d1
  as Solkey.Migration.Aggregates testing

namespace Solidity.Examples.Tactics.AggregatesImport

/-- The imported literals program has the expected initialized-state outcome. -/
theorem literals_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.literals).isOk = true := by decide +kernel

/-- The imported copies program has the expected initialized-state outcome. -/
theorem copies_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.copies).isOk = true := by decide +kernel

/-- The imported storageElements program has the expected initialized-state outcome. -/
theorem storageElements_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.storageElements).isOk = true := by decide +kernel

/-- The imported memoryElements program has the expected initialized-state outcome. -/
theorem memoryElements_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.memoryElements).isOk = true := by decide +kernel

/-- The imported tuples program has the expected initialized-state outcome. -/
theorem tuples_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.tuples).isOk = true := by decide +kernel

/-- The imported nested program has the expected initialized-state outcome. -/
theorem nested_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.nested).isOk = true := by decide +kernel

/-- The imported abiLiteral program has the expected initialized-state outcome. -/
theorem abiLiteral_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.abiLiteral).isOk = true := by decide +kernel

/-- The imported falsePost program has the expected initialized-state outcome. -/
theorem falsePost_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.falsePost).isOk = false := by decide +kernel

/-- The imported narrowNested program has the expected initialized-state outcome. -/
theorem narrowNested_initial : (Prog.run (State.init Solkey.Migration.Aggregates)
    Solkey.Migration.Aggregates.narrowNested).isOk = true := by decide +kernel

open scoped Scoped
local instance : InContract := ⟨Solkey.Migration.Aggregates⟩

/-- The imported literal assertion is valid in every initial typed state. -/
theorem literals_valid : ⊨ᶠ spec!{literals} := by
  sol_symex; sol_decide

end Solidity.Examples.Tactics.AggregatesImport
