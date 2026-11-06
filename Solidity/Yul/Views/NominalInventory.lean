import Solidity.Yul.Views.InventorySnapshot
import Solidity.Yul.Views.NominalMemory

/-! Nominal memory arrays in the typed whole-heap inventory. The declaration
check applies even to empty arrays. Existing canonical dispatch is unchanged;
this additive dispatcher only supplies the previously unsupported UDVT arrays.
Successful preparations use the existing retained extent check and real heap
write sequence, including its complete source success/error result. -/
namespace Solidity.Yul.Views.NominalInventory

def snapshot {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (name : Source.DeclName) (k : Option Nat) (m : ByteView) (base : Nat) :
    Option (InventoryObject p (.array .memory (.udvt name) k)) :=
  let n := arrayLengthChoice k m base
  if NominalMemory.declaredUDVT E name then
    if bound : n < 2^256 then
      (NominalMemory.decodeArray E.layout name n m (base+arrayPayloadOffset k)).pmap
        (fun values decoded =>
          ⟨.array n (snapshotLengthChoice k m base) (fun i => .val (values i)),
            .array k.isNone n, .array n (snapshotLengthChoice k m base) _,
            .words _ _ (.array n (snapshotLengthChoice k m base) bound values
              (fun i => mload m (base+arrayPayloadOffset k+i.val*32))
              (fun i => .scalar (values i) _
                (NominalMemory.array_word E.layout name n m _ values decoded i)))⟩)
        (fun _ member => member)
    else none
  else none

def decode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (m : ByteView) (base : Nat) :
    Option (InventoryObject p τ) :=
  match τ with
  | .array .memory (.udvt name) k => snapshot p name k m base
  | σ => decodeInventoryObject p es σ m base

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

end Solidity.Yul.Views.NominalInventory
