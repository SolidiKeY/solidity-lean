import Solidity.Lowering.V08.RoleControls

/-! Regression: role metadata must not fabricate installed accounts or funding,
and other-role preservation must have genuinely distinct catalogue keys.
A general attachment frame law retains whole account/ledger functions and time;
the existing two-key model supplies actual metadata and exact guard refusals.
No Source deployment/body/link/layout preservation or admission is asserted. -/
namespace H62.AuditV08Adapters.RoleAttachmentJoint
open Solidity ContractWorld
open Solidity.Lowering.V08
open DeclarationRoles

/-- General framing law for the existing role attachment, with full functions. -/
theorem frames {K : Type} [DecidableEq K] {contracts : K → Contract}
    (world : World contracts) (key other : K) (role : Role)
    (declaration : Source.Decl) (selected : roleOf? declaration = some role)
    (different : other ≠ key) :
    ∃ next, attach? declaration world key = some next ∧
      next.accounts = world.accounts ∧ next.funds = world.funds ∧
      next.timestamp = world.timestamp ∧ next.roles other = world.roles other :=
  ⟨setRole world key role, attach_of_role declaration world key role selected,
    rfl, rfl, rfl, other_role world key other role different⟩

/-- Distinctness and metadata coexist in the existing nonempty source unit. -/
theorem joint : RoleControls.libraryDecl ∈ RoleControls.sourceUnit.decls ∧
    roleOf? RoleControls.libraryDecl = some .libraryCode ∧
    (false : Bool) ≠ true ∧ (RoleControls.before.funds Controls.sender).1 = 100 :=
  ⟨RoleControls.library_member, rfl, by decide +kernel, by decide +kernel⟩

/-- Instantiation retains whole account and ledger functions, not projections. -/
theorem actual_frames :
    ∃ next, attach? RoleControls.libraryDecl RoleControls.before true = some next ∧
      next.accounts = RoleControls.before.accounts ∧
      next.funds = RoleControls.before.funds ∧
      next.timestamp = RoleControls.before.timestamp ∧
      next.roles false = RoleControls.before.roles false :=
  frames RoleControls.before true false .libraryCode RoleControls.libraryDecl
    joint.2.1 joint.2.2.1

/-- Exact ordinary creation refusal for any supplied typed constructor/context. -/
theorem actual_create (constructor : Prog (LibraryControls.linkedCatalog true) [] [])
    (context : Context) :
    (attach? RoleControls.libraryDecl RoleControls.before true).map
      (fun next => next.create true LibraryControls.link constructor context) =
        some (.error .revert) :=
  source_library_create_refused RoleControls.libraryDecl RoleControls.before true
    LibraryControls.link constructor context joint.2.1

/-- Exact ordinary-call refusal; no favourable body or call result is assumed. -/
theorem actual_call {α : Type} (entry : Entry (LibraryControls.linkedCatalog true) α)
    (context : Context) :
    (attach? RoleControls.libraryDecl RoleControls.before true).map
      (fun next => next.callFrame (⟨LibraryControls.link⟩ : Handle true) entry context) =
        some (.error .revert) := by
  rw [attach_of_role RoleControls.libraryDecl RoleControls.before true .libraryCode joint.2.1]
  exact congrArg some (library_call_refused RoleControls.before true _ entry context)

#print axioms frames
#print axioms joint
#print axioms actual_frames
#print axioms actual_create
#print axioms actual_call
end H62.AuditV08Adapters.RoleAttachmentJoint
