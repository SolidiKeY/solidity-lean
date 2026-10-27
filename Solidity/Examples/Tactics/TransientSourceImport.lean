import Solidity.Frontend.Import
import Solidity.Semantics.Run
import Solidity.Syntax.Splice

/-! The actual pinned-source lowering, executed at a concrete deployed address.
Safety formulas and successful execution are separate controls. -/
namespace Solidity.Examples.Tactics.TransientSourceImport
solc_import "../../../tests/solc/TransientSource.ast.json" hash 0xaddcbeb9d907ef4d as Imported.TransientSource testing
solc_import "../../../tests/solc/TransientSource.ast.json" hash 0xaddcbeb9d907ef4d as Imported.TransientDerived testing
private def entry : State Imported.TransientSource [] :=
  { State.init Imported.TransientSource with tx := { selfAddress := ⟨1, rfl⟩ } }

example : Imported.TransientSource.transientRoots = ["count"] := rfl
example : Imported.TransientDerived.transientRoots = ["inherited"] := rfl
/-- The source must actually return successfully; rejecting its self-call is insufficient. -/
theorem source_self_success : ((sol[Imported.TransientSource]{ selfSharing(); }).run entry).isOk = true := by decide +kernel
/-- The source's own caught failure restores both declared regions. -/
theorem source_rollback_success : ((sol[Imported.TransientSource]{ rollback(); }).run entry).isOk = true := by decide +kernel
/-- A false source assertion remains a panic, not an admitted failed observation. -/
example : (match (sol[Imported.TransientSource]{ falsePersistentAlias(); }).run entry with
  | .error .panic => true | _ => false) = true := by decide +kernel

#print axioms source_self_success
#print axioms source_rollback_success
end Solidity.Examples.Tactics.TransientSourceImport
