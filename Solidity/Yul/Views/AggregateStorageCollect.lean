import Solidity.Yul.Views.AggregateStorageExtent
import Solidity.Yul.Views.RecursiveSourceInventory

namespace Solidity.Yul.Views

/-- Same typed scalar registrations as the existing finite codec. The oracle
reads a header, not a proposed inventory or desired output-view law. -/
abbrev AggregateLengthOracle (E : Source.Env) (a : Roadmap.Address) := ScalarPath E.layout (E.lay a) → Option Roadmap.Word
abbrev AggregateCollectFn (E : Source.Env) := (path : Source.SPath) → (a : Roadmap.Address) →
  AggregateLengthOracle E a → Nat → Option (List (ScalarPath E.layout (E.lay a)) × Nat)

/-- Natural recursion is over the actual runtime count, not a new cap. Word
nonwrap and positive stride are checked preparation boundaries. A failed child
propagates; no subtree is skipped. Child end is NOT the enclosing header end. -/
def collectAggregateElements {E} (child : AggregateCollectFn E) (fixed : Roadmap.Evm.Fixed)
    (p : Source.SPath) (a : Roadmap.Address) (lengths : AggregateLengthOracle E a)
    (base stride index count : Nat) : Option (List (ScalarPath E.layout (E.lay a))) :=
  match count with
  | 0 => some []
  | n+1 => do
    if stride=0 ∨ base+(index+1)*stride>2^256 then none else do
      let here ← child (p.go (.index index)) a lengths ((base+index*stride)*32)
      let rest ← collectAggregateElements child fixed p a lengths base stride (index+1) n
      pure (here.1++rest)

def collectAggregateField {E} (head : AggregateCollectFn E) (tail : Nat → AggregateCollectFn E)
    (index : Nat) : AggregateCollectFn E := fun p a lengths cursor => do
  let here ← head (p.go (.field index)) a lengths cursor
  let rest ← tail (index+1) p a lengths here.2
  pure (here.1++rest.1,rest.2)

mutual
def AggregateStorageDeclaration.collect {E τ b} (d : AggregateStorageDeclaration E τ b)
    (fixed : Roadmap.Evm.Fixed) : AggregateCollectFn E :=
  AggregateStorageDeclaration.casesOn (motive_1 := fun _ _ _ => AggregateCollectFn E) d
    (fun {τ _} old => fun p a lengths cursor =>
      if typed : E.pathTy p = some τ then
        match packed : old.pack p a cursor with
        | .error _ => none
        | .ok (cs,stop) => do
          let live ← (old.headers p cursor).attach.mapM (fun (entry : {entry // entry ∈ old.headers p cursor}) => do
            let h : PathPrimitiveHeader E entry.val.1 entry.val.2.1 entry.val.2.2 := by
              obtain ⟨h,_⟩ := old.headers_sound p a cursor cs stop typed packed entry.val entry.property
              exact h
            let n ← lengths (h.registration a)
            pure (h.elements fixed a n))
          pure (cs++live.flatten,stop)
      else none)
    (fun name _ _ members => fun p a lengths cursor =>
      if E.pathTy p = some (.struct .storage name) then do
        let out ← members.collect fixed 0 p a lengths (roundSlot cursor)
        pure (out.1,roundSlot out.2)
      else none)
    (fun {τ _} child _ => fun p a lengths cursor =>
      if E.pathTy p = some (.array .storage τ none) then do
        let header ← ((StorageDeclaration.uintArray (E := E)).pack p a cursor).toOption
        match header.1 with
        | [c] => do
          let n ← lengths c
          let base := fixedLayoutHash fixed (.data c.slot.val)
          let live ← collectAggregateElements (child.collect fixed) fixed p a lengths base child.stride 0 n.val
          pure (header.1++live,header.2)
        | _ => none
      else none)
def AggregateStorageFields.collect {E τs b} (d : AggregateStorageFields E τs b)
    (fixed : Roadmap.Evm.Fixed) : Nat → AggregateCollectFn E :=
  AggregateStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → AggregateCollectFn E) d
    (fun _ _ _ _ cursor => some ([],cursor))
    (fun {τ _ _ _} head tail => collectAggregateField
      (fun p a lengths cursor => if E.pathTy p = some τ then head.collect fixed p a lengths cursor else none)
      (tail.collect fixed))
end

/-- Concrete source oracle, preserving real Source failure as failed
PREPARATION. This is not admission/refusal or execution semantics. -/
def aggregateSourceLengths {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) : AggregateLengthOracle E F.this :=
  fun c => do
    let n ← (Source.readLen F c.path).run s |>.1.toOption
    if bound : n<2^256 then some ⟨n,bound⟩ else none

def aggregateRawLengths {E a} (m : SlotView) : AggregateLengthOracle E a := fun c => some (m c.slot)

end Solidity.Yul.Views
