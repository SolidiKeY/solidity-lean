import Solidity.Yul.Views.FixedNominalStruct
import Solidity.Yul.Views.FixedNominalInventoryLaws

/-! Mixed fixed/nominal struct snapshots feed existing typed inventory updates.
All other objects retain the previous dispatcher. Retained original capacity and
actual Source writes are unchanged; this is not whole-language admission. -/
namespace Solidity.Yul.Views.MixedNominalInventory

def decode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (m : ByteView) (base : Nat) :
    Option (InventoryObject p τ) :=
  match τ with
  | .struct l name => FixedNominalMember.snapshotStruct p es l name m base
  | σ => FixedNominalInventory.decode p es σ m base

def update {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p))
    (entry : MixedHeapEntry p) (m : ByteView) : Option (OwnedInventoryUpdate allocated p) := do
  let object ← decode p es entry.ty m (p.address entry.id)
  if fits : object.shape.size ≤ (allocated.shape entry.id).size then
    pure ⟨entry,object,fits⟩
  else none

def updates {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es : List (MixedHeapEntry p)) :
    List (MixedHeapEntry p) → ByteView → Option (List (OwnedInventoryUpdate allocated p))
  | [], _ => some []
  | entry::rest, m => do
    let first ← update allocated p es entry m
    let tail ← updates allocated p es rest m
    pure (first::tail)

def writeback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (_history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p)) (m : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  (updates allocated p es es m).map (fun us => (runInventoryUpdates us).run s)

end Solidity.Yul.Views.MixedNominalInventory
