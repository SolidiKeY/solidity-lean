import Solidity.Yul.Views.AggregateStorageCollect

namespace Solidity.Yul.Views

/-- Concrete complete raw-snapshot preparation for the generated live inventory.
This does NOT establish alias closure after shrink or source/Yul adequacy. -/
def aggregateSnapshotWriteback {E τ b} (d : AggregateStorageDeclaration E τ b)
    (fixed : Roadmap.Evm.Fixed) (p : Source.SPath) (a : Roadmap.Address) (cursor : Nat)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) := do
  let computed ← d.collect fixed p a (aggregateRawLengths m) cursor
  if packedSeparationCheck computed.1 then packedStoreWriteback computed.1 m s else none

theorem aggregateSnapshot_reencode {E τ b} (d : AggregateStorageDeclaration E τ b)
    (fixed p a cursor m) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : aggregateSnapshotWriteback d fixed p a cursor m s = some (out,residual)) :
    ∃ cs stop, d.collect fixed p a (aggregateRawLengths m) cursor = some (cs,stop) ∧
      finiteEncode cs out residual = some m := by
  unfold aggregateSnapshotWriteback at step
  cases computed : d.collect fixed p a (aggregateRawLengths m) cursor with
  | none => simp only [computed,Bind.bind,Option.bind] at step; cases step
  | some result =>
    rcases result with ⟨cs,stop⟩
    simp only [computed,Bind.bind,Option.bind] at step
    split at step
    · exact ⟨cs,stop,rfl,packedStoreWriteback_reencode _ _ _ _ _
        ((packedSeparationCheck_iff _).mp (by assumption)) step⟩
    · cases step

theorem aggregateSnapshot_unchanged {E τ b} (d : AggregateStorageDeclaration E τ b)
    (fixed p a cursor m) (s : Source.Storage E.layout (E.lay a)) (cs stop)
    (computed : d.collect fixed p a (aggregateRawLengths m) cursor = some (cs,stop))
    (checked : packedSeparationCheck cs = true) (view : finiteView cs s m) :
    aggregateSnapshotWriteback d fixed p a cursor m s = some (s,packedMask cs m) := by
  unfold aggregateSnapshotWriteback
  rw [computed]
  dsimp only [Bind.bind,Option.bind]
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem aggregateSnapshot_unselected {E τ b} (d : AggregateStorageDeclaration E τ b)
    (fixed p a cursor m) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView) (cs stop)
    (computed : d.collect fixed p a (aggregateRawLengths m) cursor = some (cs,stop))
    (step : aggregateSnapshotWriteback d fixed p a cursor m s = some (out,residual))
    (q : Source.SPath) (unselected : ∀ c ∈ cs, q ≠ c.path) : out.cell q = s.cell q := by
  unfold aggregateSnapshotWriteback at step
  rw [computed] at step
  dsimp only [Bind.bind,Option.bind] at step
  split at step
  · exact packedStoreWriteback_other _ _ _ _ _ step q unselected
  · cases step

end Solidity.Yul.Views
