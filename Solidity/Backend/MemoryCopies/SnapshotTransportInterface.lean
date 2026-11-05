import Solidity.Theory.Typed.Mem

/-! Generic observation transport through an existing kept heap extension.
The original rank-bounded copy operation and typed array lookup are unchanged.
No Source admission, compiled traversal or physical adequacy is asserted. -/
namespace Solidity.Backend.MemoryCopies

structure SnapshotTransportCertificate : Prop where
  snapshot : ∀ {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H'),
    Heap.Keeps extension before after → ∀ (T : Ty) (value : MVal H T),
    MVal.copyMToSt after (MVal.wk extension T value) = MVal.copyMToSt before value
  index : ∀ {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H'),
    Heap.Keeps extension before after → ∀ {A : RefTy} {E : Ty} (source : HRef H A)
      (shape : ArrTy A E) (index : PrimTy.uint.Denote),
    after.index (source.wk extension) shape index = (before.index source shape index).map (MVal.wk extension E)

end Solidity.Backend.MemoryCopies
