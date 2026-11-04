import Solidity.Backend.MemoryCopies.SourceRootCopies
import Solidity.Backend.MemoryCopies.SourceDefaultFrames

/-! Existing Source default traversal at arbitrary reference-element lengths. -/
namespace Solidity.Backend.MemoryCopies

/-- A proved leaf constructor at the existing Source operation. Instances are
supplied by proofs, not postulated; no Source admission rule is replaced. -/
structure SourceLeafDefault (E : Source.Env) (τ : Source.STy)
    (memory : τ.loc? = some .memory) where
  data : Source.Data E.layout τ
  execution : ∀ {Γ : Source.RCtx} (before : Source.EMState E Γ) (slack : Nat),
    (Source.zeroVal (E := E) (Γ := Γ) (slack + 2) τ).run before =
      (.ok (.memRef memory before.2.heap.next),allocatedState data before)

/-- Exact child addresses and reached state from the actual zeroElems run.
This is a successful Source fragment, not a compiler or size-failure theorem. -/
def SourceLeafElementsResult {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (memory : τ.loc? = some .memory) (before : Source.EMState E Γ) (count slack : Nat) : Prop :=
  ∃ (values : Fin count → Source.Data E.layout τ) (after : Source.EMState E Γ),
    (Source.zeroElems (E := E) (Γ := Γ) (count + 2 + slack) τ count).run before = (.ok values,after) ∧
    after.2.heap.next = before.2.heap.next + count ∧ AllocationExtension before after ∧
    (∀ i, values i = .val (.memRef memory (before.2.heap.next + i.val)))

end Solidity.Backend.MemoryCopies
