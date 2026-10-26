import Solidity.Frontend.Testing
import Solidity.Calculus.Close
import Solidity.Calculus.Closers

/-! Compiler-accepted names retain their declaration identity through import. -/
solc_import "../../../tests/solc/SourceIdentifiers.ast.json" hash 0x7074a63990674247
  as Imported.SourceIdentifiers testing


namespace Solidity.Examples.Tactics.SourceIdentifiersImport

theorem shadow_execution :
    (Prog.run (State.init Imported.SourceIdentifiers) Imported.SourceIdentifiers.noOpShadow).isOk = true ∧
    (Prog.run (State.init Imported.SourceIdentifiers) Imported.SourceIdentifiers.«$compute»).isOk = true ∧
    (Prog.run (State.init Imported.SourceIdentifiers) Imported.SourceIdentifiers.localMagic).isOk = true := by
  decide +kernel

open scoped Scoped
local instance : InContract := ⟨Imported.SourceIdentifiers⟩

theorem escaped_spec_valid : ⊨ᶠ spec!{escapedSpec} := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.SourceIdentifiersImport
