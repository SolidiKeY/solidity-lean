import Solidity.Yul.Views.InventorySnapshot
import Solidity.Yul.Views.FixedMemory
import Solidity.Yul.Views.NominalInventoryLaws

/-! Additive fixed-array inventory snapshots use actual scaled values, original
extent checks and existing typed InventoryObject/OwnedInventoryUpdate. Other
objects use the existing nominal dispatcher. No old predicate or decoder changes,
new state/AST, pointer policy or recursive depth bound are introduced. -/
namespace Solidity.Yul.Views.FixedInventory

def snapshot {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (f : Source.FixTy) (k : Option Nat) (m : ByteView) (base : Nat) :
    Option (InventoryObject p (.array .memory (.fixed f) k)) :=
  let n := arrayLengthChoice k m base
  if bound : n < 2^256 then
      (FixedMemory.decodeArray E.layout f n m (base+arrayPayloadOffset k)).pmap
        (fun values decoded =>
          ⟨.array n (snapshotLengthChoice k m base) (fun i => .val (values i)),
            .array k.isNone n, .array n (snapshotLengthChoice k m base) _,
            .words _ _ (.array n (snapshotLengthChoice k m base) bound values
              (fun i => mload m (base+arrayPayloadOffset k+i.val*32))
              (fun i => .scalar (values i) _
                (FixedMemory.array_word E.layout f n m _ values decoded i)))⟩)
        (fun _ member => member)
  else none

def decode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (m : ByteView) (base : Nat) :
    Option (InventoryObject p τ) :=
  match τ with
  | .array .memory (.fixed f) k => snapshot p f k m base
  | σ => NominalInventory.decode p es σ m base

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

end Solidity.Yul.Views.FixedInventory
