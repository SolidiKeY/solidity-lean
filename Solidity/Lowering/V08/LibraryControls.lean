import Solidity.Lowering.V08.Controls
import Solidity.Lowering.V08.LibraryCreation

/-! Linked-context and constructor-combination witnesses over supplied typed
bodies; source linkage and source execution are not certified by these controls. -/
namespace Solidity.Lowering.V08.LibraryControls
open Solidity.ContractWorld
open Solidity.Lowering.V08.Controls

def Empty : Contract := { vars := [] }
def linkedCatalog : Bool → Contract | false => Cell | true => Empty
def roles : Bool → Role | false => .contractCode | true => .libraryCode
def link : Address := ⟨⟨4, by decide +kernel⟩, by decide +kernel⟩
def linkedInitial : World linkedCatalog := World.empty linkedCatalog
  (fun address => if address = sender then ⟨100, by decide +kernel⟩ else ⟨0, by decide +kernel⟩) roles

def cells (world : World linkedCatalog) (owner : Address) : Option (Int × Int) := do
  let store ← world.storage? (⟨owner⟩ : Handle false)
  let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
  let .prim scratch ← store.find (SRef.ofRoot "scratch" rfl)
  pure (saved.1, scratch.1)

def linkedBody : Library linkedCatalog false (List UInt8) :=
  ⟨true, link, { locals := [], body := sol[Cell]{ saved = 5; scratch = 17; }, result := fun _ => .ok [0xab, 0xcd] }⟩

def delegated : TRes ((Int × Int) × (Option (Int × Int) × Option (Int × Int)) × Nat) := do
  let (world, _) ← linkedInitial.create false self .nil Controls.ctx
  let (world, _) ← world.create false third .nil Controls.ctx
  let (world, _) ← world.deployLibrary true link Controls.ctx
  let (next, status) := world.transact (fun before => do
    let (paid, _) ← before.call (⟨self⟩ : Handle false) (Entry.unit .nil true) paidCtx
    paid.libraryCall (⟨self⟩ : Handle false) (observeLibrary linkedBody List.length) paidCtx)
  let length ← status
  pure (((next.balance sender).1, (next.balance self).1), (cells next self, cells next third), length)

/-- A paid outer caller delegates in its own storage; another instance stays
unchanged and the observation extension retains the exact returned length. -/
theorem delegated_owner : delegated.toOption = some ((93, 7), (some (5, 0), some (0, 0)), 2) := by decide +kernel

/-- Delegation neither charges value twice nor writes another instance. -/
theorem delegated_wrong_context : delegated.toOption ≠ some ((86, 14), (some (5, 0), some (5, 0)), 2) := by
  rw [delegated_owner]
  decide +kernel

def constructedCells (world : World catalog) : Option (Int × Int) := do
  let store ← world.storage? (⟨third⟩ : Handle ())
  let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
  let .prim scratch ← store.find (SRef.ofRoot "scratch" rfl)
  pure (saved.1, scratch.1)

def creationSuccess : TRes (Option (Int × Int × Int × Int) × Option (Int × Int) × Nat) := do
  let world ← setup
  let (next, status) := world.transact (fun before => do
    let (paid, _) ← before.call (⟨self⟩ : Handle ()) entry paidCtx
    paid.tryCreate (.ok ()) () (fun _ => third)
      (fun _ => sol[Cell]{ saved = 8; scratch = 12; }) (fun _ => Controls.ctx)
      (fun after _ => .ok (after, 42)) (fun snapshot _ => .ok (snapshot, 0)))
  let result ← status
  pure (observe next, constructedCells next, result)

/-- Nonempty constructor success installs its own persistent store; both
owners' transient regions reset at the same outer transaction boundary. -/
theorem constructor_installed : creationSuccess.toOption =
    some (some (93, 7, 3, 0), some (8, 0), 42) := by decide +kernel

/-- Successful construction cannot be replaced by a default installed store. -/
theorem constructor_wrong_store : creationSuccess.toOption ≠
    some (some (93, 7, 3, 0), some (0, 0), 42) := by decide +kernel

#print axioms delegated_owner
#print axioms delegated_wrong_context
#print axioms constructor_installed
#print axioms constructor_wrong_store
end Solidity.Lowering.V08.LibraryControls
