import Solidity.Lowering.V08.DeclarationRoles
import Solidity.Lowering.V08.LibraryControls

/-! Source role metadata and actual existing typed library deployment controls.
Catalogue/layout/link/body source preservation remains an explicit prerequisite. -/
namespace Solidity.Lowering.V08.RoleControls
open Solidity
open ContractWorld
open DeclarationRoles

def libraryDecl : Source.Decl :=
  { kind := .library, name := "L", scope := none, top := true, node := .library "L" .nil }
def interfaceDecl : Source.Decl :=
  { kind := .interface, name := "I", scope := none, top := true, node := .interface "I" .nil .nil }
def sourceUnit : Source.Syn .unit := .unit (.cons libraryDecl.node (.cons interfaceDecl.node .nil))

theorem library_member : libraryDecl ∈ sourceUnit.decls := List.mem_cons_self

theorem source_roles : roleOf? libraryDecl = some .libraryCode ∧ roleOf? interfaceDecl = none := ⟨rfl, rfl⟩

def before : World LibraryControls.linkedCatalog := World.empty LibraryControls.linkedCatalog
  (fun address => if address = Controls.sender then ⟨100, by decide +kernel⟩ else ⟨0, by decide +kernel⟩)
def attached : Option (World LibraryControls.linkedCatalog) := attach? libraryDecl before true

def deployed : Option (TRes Bool) := attached.map fun world => do
  let (next, _) ← world.deployLibrary true LibraryControls.link Controls.ctx
  pure ((next.storage? (⟨LibraryControls.link⟩ : Handle true)).isSome)

/-- This actual source role attaches to an empty typed library and installs code. -/
theorem library_deployed : deployed.map Except.toOption = some (some true) := by decide +kernel

def refused : Option (Option THalt) := attached.map fun world =>
  match world.create true LibraryControls.link .nil Controls.ctx with
  | .error halt => some halt
  | _ => none

/-- Actual intrinsic ordinary creation after attaching source library role
metadata is rejected exactly; no source-new execution is asserted. -/
theorem ordinary_creation_refused : refused = some (some .revert) := by decide +kernel

/-- The other catalogue key stays an ordinary contract with its actual funding. -/
theorem other_catalogue_preserved : attached.map (fun world =>
    (world.isLibrary false, (world.balance Controls.sender).1, world.accounts Controls.self |>.isSome)) =
      some (false, 100, false) := by decide +kernel

#print axioms library_member
#print axioms source_roles
#print axioms library_deployed
#print axioms ordinary_creation_refused
#print axioms other_catalogue_preserved
end Solidity.Lowering.V08.RoleControls
