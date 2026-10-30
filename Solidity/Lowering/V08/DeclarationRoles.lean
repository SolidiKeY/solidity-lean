import Solidity.Source.Decls
import Solidity.Semantics.ContractWorld

/-!
# Declaration-kind role observations

A catalogue key and its typed Contract are still supplied. This adapter only
reads source declaration kind and attaches the existing runtime role; it does
not install source code or certify layout/link identity, abstractness or source
admission. Interfaces and non-code declarations do not create deployable roles.
-/
namespace Solidity.Lowering.V08.DeclarationRoles
open Solidity
open ContractWorld

def roleOf? (declaration : Source.Decl) : Option Role :=
  match declaration.kind, declaration.top, declaration.node with
  | .contract, _, .contract _ _ _ _ _ => some .contractCode
  | .library, _, .library _ _ => some .libraryCode
  | _, _, _ => none

/-- Change one existing typed catalogue's role; leave every account/body intact. -/
def setRole {K : Type} [DecidableEq K] {contracts : K → Contract}
    (world : World contracts) (key : K) (role : Role) : World contracts :=
  { world with roles := fun other => if other = key then role else world.roles other }

def attach? {K : Type} [DecidableEq K] {contracts : K → Contract}
    (declaration : Source.Decl) (world : World contracts) (key : K) : Option (World contracts) :=
  (roleOf? declaration).map (setRole world key)

theorem attach_of_role {K : Type} [DecidableEq K] {contracts : K → Contract}
    (declaration : Source.Decl) (world : World contracts) (key : K) (role : Role)
    (selected : roleOf? declaration = some role) :
    attach? declaration world key = some (setRole world key role) := by
  simp only [attach?, selected, Option.map_some]

/-- Registering one role leaves all other catalogue keys unchanged. -/
theorem other_role {K : Type} [DecidableEq K] {contracts : K → Contract}
    (world : World contracts) (key other : K) (role : Role) (different : other ≠ key) :
    (setRole world key role).roles other = world.roles other := by
  simp only [setRole, different, if_false]

/-- No storage/code lookup is fabricated by attaching role metadata. -/
theorem storage_unchanged {K : Type} [DecidableEq K] {contracts : K → Contract}
    (world : World contracts) (key : K) (role : Role) {other : K} (handle : Handle other) :
    (setRole world key role).storage? handle = world.storage? handle := rfl

theorem library_role {K : Type} [DecidableEq K] {contracts : K → Contract}
    (world : World contracts) (key : K) :
    (setRole world key .libraryCode).isLibrary key = true := by
  simp only [setRole, World.isLibrary, if_true]

/-- The actual ordinary creation interface rejects the library role. -/
theorem library_create_refused {K : Type} [DecidableEq K] {contracts : K → Contract}
    (world : World contracts) (key : K) (self : Address)
    (constructor : Prog (contracts key) [] []) (context : Context) :
    (setRole world key .libraryCode).create key self constructor context = .error .revert := by
  unfold World.create
  rw [library_role]
  rfl

/-- The actual ordinary call interface also rejects a library regardless of body. -/
theorem library_call_refused {K : Type} [DecidableEq K] {contracts : K → Contract} {α : Type}
    (world : World contracts) (key : K) (self : Handle key)
    (entry : Entry (contracts key) α) (context : Context) :
    (setRole world key .libraryCode).callFrame self entry context = .error .revert := by
  unfold World.callFrame
  rw [library_role]
  rfl

/-- Source library metadata transports its real ordinary-creation refusal,
without pretending to certify the separate supplied typed library body. -/
theorem source_library_create_refused {K : Type} [DecidableEq K] {contracts : K → Contract}
    (declaration : Source.Decl) (world : World contracts) (key : K) (self : Address)
    (constructor : Prog (contracts key) [] []) (context : Context)
    (selected : roleOf? declaration = some .libraryCode) :
    (attach? declaration world key).map (fun next => next.create key self constructor context) =
      some (.error .revert) := by
  rw [attach_of_role declaration world key .libraryCode selected]
  exact congrArg some (library_create_refused world key self constructor context)

#print axioms attach_of_role
#print axioms other_role
#print axioms storage_unchanged
#print axioms library_role
#print axioms library_create_refused
#print axioms library_call_refused
#print axioms source_library_create_refused
end Solidity.Lowering.V08.DeclarationRoles
