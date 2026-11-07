import Solidity.Backend.MemoryCopies.SourceStoredElementsInterface

/-! Fresh parent and repeated-copy obligations for the existing stored-value family.
All equations describe actual Source loadElem runs, not a new evaluator. -/
namespace Solidity.Backend.MemoryCopies

structure SourceStoredReferenceCertificate {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {type : Source.STy}
    (stored : SourceStoredValue frame path before type) (memory : type.loc? = some .memory) : Prop where
  positive : 0 < stored.objects
  copy : ∀ (input : Source.EMState E Γ), AllocationExtension before input → ∀ slack : Nat,
    ∃ (data : Source.Data E.layout type) (loaded after : Source.EMState E Γ) (root : Nat),
      SourceStorageCopyCertificate frame (stored.horizon + slack - 1) type memory path input loaded after root data ∧
      after.2.heap.next = input.2.heap.next + stored.objects ∧ root + 1 = after.2.heap.next

def SourceStoredDoubleCopy {E : Source.Env} {Γ : Source.RCtx} {frame : Source.Fr}
    {path : Source.SPath} {before : Source.EMState E Γ} {type : Source.STy}
    (stored : SourceStoredValue frame path before type) (memory : type.loc? = some .memory)
    (input : Source.EMState E Γ) (slack : Nat) : Prop :=
  ∃ (firstData secondData : Source.Data E.layout type)
    (firstLoaded firstAfter secondLoaded secondAfter : Source.EMState E Γ) (firstRoot secondRoot : Nat),
    SourceStorageCopyCertificate frame (stored.horizon + slack - 1) type memory path
      input firstLoaded firstAfter firstRoot firstData ∧
    SourceStorageCopyCertificate frame (stored.horizon + slack - 1) type memory path
      firstAfter secondLoaded secondAfter secondRoot secondData ∧
    (do
      let first ← Source.loadElem (E := E) (Γ := Γ) frame (stored.horizon + slack) type path
      let second ← Source.loadElem frame (stored.horizon + slack) type path
      pure (first,second)).run input = (.ok (.memRef memory firstRoot,.memRef memory secondRoot),secondAfter) ∧
    firstAfter.2.heap.next = input.2.heap.next + stored.objects ∧
    secondAfter.2.heap.next = input.2.heap.next + 2 * stored.objects ∧
    firstRoot + 1 = firstAfter.2.heap.next ∧ secondRoot + 1 = secondAfter.2.heap.next ∧
    firstRoot < secondRoot ∧ secondAfter.2.heap.get firstRoot = some ⟨type,firstData⟩
end Solidity.Backend.MemoryCopies
