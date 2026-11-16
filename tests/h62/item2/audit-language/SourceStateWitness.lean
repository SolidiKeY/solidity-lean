import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.State

/-!
Guarded regression: copying must allocate fresh storage, preserve source contents
under writes to the copy, and keep writes invisible at distinct addresses/paths.
These full imported telescopes share one populated heap/layout and a populated
storage cell; individually inhabited but incompatible premises earn no credit.
Local state feasibility and clients do not prove compiler or EVM frame behavior.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceStateWitness
open Solidity.Source

def layout : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
def signedDecimal : FixTy := ⟨true, 8, 1, by decide⟩
def dataFalse : Data layout .bool := .val (.bool false)
def dataTrue : Data layout .bool := .val (.bool true)
def objectFalse : Σ τ, Data layout τ := ⟨.bool, dataFalse⟩
def objectTrue : Σ τ, Data layout τ := ⟨.bool, dataTrue⟩
def initial : Heap layout := ((Heap.empty : Heap layout).alloc objectFalse).1

def types : SPath → STy := fun _ => .bool
def path : SPath := ⟨⟨some "C", "value"⟩, []⟩
def otherPath : SPath := ⟨⟨some "C", "value"⟩, [.field 1]⟩
def storage : Storage layout types := Storage.empty.write path (.bool true)

theorem integer_zero_full : hypotheses_of% IntTy.zero_mem := by
  exact ⟨IntTy.u8, True.intro⟩
#verify_hypotheses integer_zero_full for Solidity.Source.IntTy.zero_mem
#print axioms integer_zero_full

theorem fixed_zero_full : hypotheses_of% FixTy.zero_mem := by
  exact ⟨signedDecimal, True.intro⟩
#verify_hypotheses fixed_zero_full for Solidity.Source.FixTy.zero_mem
#print axioms fixed_zero_full

theorem allocation_fresh_full : hypotheses_of% Heap.alloc_fresh := by
  exact ⟨layout, initial, objectTrue, True.intro⟩
#verify_hypotheses allocation_fresh_full for Solidity.Source.Heap.alloc_fresh
#print axioms allocation_fresh_full

theorem allocation_get_full : hypotheses_of% Heap.alloc_get := by
  exact ⟨layout, initial, objectTrue, True.intro⟩
#verify_hypotheses allocation_get_full for Solidity.Source.Heap.alloc_get
#print axioms allocation_get_full

theorem allocation_other_full : hypotheses_of% Heap.alloc_other := by
  exact ⟨layout, initial, objectTrue, 0, by decide, True.intro⟩
#verify_hypotheses allocation_other_full for Solidity.Source.Heap.alloc_other
#print axioms allocation_other_full

theorem write_get_full : hypotheses_of% Heap.write_get := by
  exact ⟨layout, initial, 0, .bool, dataTrue, rfl, True.intro⟩
#verify_hypotheses write_get_full for Solidity.Source.Heap.write_get
#print axioms write_get_full

theorem write_other_full : hypotheses_of% Heap.write_other := by
  exact ⟨layout, initial, 0, 1, by decide, .bool, dataTrue, rfl, True.intro⟩
#verify_hypotheses write_other_full for Solidity.Source.Heap.write_other
#print axioms write_other_full

theorem write_type_full : hypotheses_of% Heap.write_ty := by
  exact ⟨layout, initial, 0, 1, .bool, dataTrue, rfl, True.intro⟩
#verify_hypotheses write_type_full for Solidity.Source.Heap.write_ty
#print axioms write_type_full

theorem copy_get_full : hypotheses_of% Heap.copy_get := by
  exact ⟨layout, initial, 0, objectFalse, rfl, True.intro⟩
#verify_hypotheses copy_get_full for Solidity.Source.Heap.copy_get
#print axioms copy_get_full

theorem copy_independent_full : hypotheses_of% Heap.copy_independent := by
  exact ⟨layout, initial, 0, objectFalse, rfl, .bool, dataTrue, rfl, True.intro⟩
#verify_hypotheses copy_independent_full for Solidity.Source.Heap.copy_independent
#print axioms copy_independent_full

theorem storage_empty_full : hypotheses_of% Storage.read_empty := by
  exact ⟨layout, types, path, True.intro⟩
#verify_hypotheses storage_empty_full for Solidity.Source.Storage.read_empty
#print axioms storage_empty_full

theorem storage_write_full : hypotheses_of% Storage.write_read := by
  exact ⟨layout, types, storage, path, Val.bool false, True.intro⟩
#verify_hypotheses storage_write_full for Solidity.Source.Storage.write_read
#print axioms storage_write_full

theorem storage_other_full : hypotheses_of% Storage.write_other := by
  exact ⟨layout, types, storage, path, otherPath, by decide, Val.bool false, True.intro⟩
#verify_hypotheses storage_other_full for Solidity.Source.Storage.write_other
#print axioms storage_other_full

theorem storage_restore_full : hypotheses_of% Storage.set_restore := by
  exact ⟨layout, types, storage, path, none, True.intro⟩
#verify_hypotheses storage_restore_full for Solidity.Source.Storage.set_restore
#print axioms storage_restore_full

/-- A source with actual contents cannot be the newly allocated address. -/
theorem allocation_not_source {D : Layout} (h : Heap D) {src : Nat}
    {x : Σ τ, Data D τ} (present : h.get src = some x) :
    (h.alloc x).2 ≠ src := by
  intro same
  have fresh := Heap.alloc_fresh h x
  rw [same, present] at fresh
  cases fresh

/-- Writing the allocated copy changes its contents while preserving the source. -/
def changedCopy : Heap layout :=
  (initial.alloc objectFalse).1.write 1 dataTrue rfl

example : changedCopy.get 0 = some objectFalse ∧ changedCopy.get 1 = some objectTrue :=
  ⟨rfl, rfl⟩

example : (storage.write otherPath (.bool false)).read path = some (.bool true) := rfl
example : (storage.set path none).read path = some (.bool false) := rfl
example : (storage.set path none).set path (storage.cell path) = storage :=
  Storage.set_restore storage path none

#print axioms allocation_not_source
end Solidity.H62.AuditLanguage.SourceStateWitness
