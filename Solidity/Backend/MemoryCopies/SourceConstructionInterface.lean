import Solidity.Backend.MemoryCopies.SourceLeafInterface

/-! Composable success certificates for the existing Source default operation.
Counters describe object identities and interpreter horizon, not physical size. -/
namespace Solidity.Backend.MemoryCopies

/-- An actual complete Source default run at every input, with exact allocation
count and the parent allocated last. Instances are proofs; this does not select
code, admit a Source type, or replace any allocation failure semantics. -/
structure SourceConstructionCertificate (E : Source.Env) (τ : Source.STy)
    (memory : τ.loc? = some .memory) where
  horizon : Nat
  objects : Nat
  horizon_positive : 0 < horizon
  objects_positive : 0 < objects
  execution : ∀ {Γ : Source.RCtx} (before : Source.EMState E Γ) (slack : Nat),
    ∃ (after : Source.EMState E Γ) (root : Nat) (data : Source.Data E.layout τ),
      SourceDefaultCertificate (horizon + slack) τ memory before after root data ∧
      after.2.heap.next = before.2.heap.next + objects ∧ root + 1 = after.2.heap.next

/-- Child traversal at the existing operation, with the exact total number of
objects allocated by the supplied proved child constructor. -/
def SourceConstructionElements {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {memory : τ.loc? = some .memory} (child : SourceConstructionCertificate E τ memory)
    (count slack : Nat) (before : Source.EMState E Γ) : Prop :=
  ∃ (values : Fin count → Source.Data E.layout τ) (after : Source.EMState E Γ),
    (Source.zeroElems (E := E) (Γ := Γ) (count + child.horizon + slack) τ count).run before =
      (.ok values,after) ∧
    after.2.heap.next = before.2.heap.next + count * child.objects ∧ AllocationExtension before after

end Solidity.Backend.MemoryCopies
