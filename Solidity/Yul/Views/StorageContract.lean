import Solidity.Yul.Views.Widths
import Solidity.Source.World

/-! Source/G27 physical agreement obligations. These structures are inputs to
V10, not replacements for its compiler or its existing full-word layout.
The original typed store is retained as writeback input, so unchanged writes
can preserve its unwritten/explicit-default distinction. -/
namespace Solidity.Yul.Views

abbrev SlotView := Roadmap.Word → Roadmap.Word

def saveSlot (m : SlotView) (a : Roadmap.Word) (v : Roadmap.Word) : SlotView :=
  fun b => if b = a then v else m b

theorem find_saveSlot (m : SlotView) (a : Roadmap.Word) (v : Roadmap.Word) : saveSlot m a v a = v := by
  simp only [saveSlot, ↓reduceIte]

theorem find_saveSlot_other (m : SlotView) (a b : Roadmap.Word) (v : Roadmap.Word) (h : b ≠ a) :
    saveSlot m a v b = m b := by simp only [saveSlot, if_neg h]

theorem saveSlot_unchanged (m : SlotView) (a : Roadmap.Word) : saveSlot m a (m a) = m := by
  funext b
  by_cases h : b = a
  · subst b; exact find_saveSlot m a (m a)
  · exact find_saveSlot_other m a b (m a) h

/-- Includes the actual source/layout codec agreement needed by G27/V10.
`view` leaves every slot outside the declared regions unconstrained; a concrete
instance must realize those bytes using `Regions.Residual`, not erase them. -/
structure ScalarStorageObligations (D : Source.Layout) (L : Source.SPath → Source.STy) (P : Type) where
  path : P → Source.SPath
  hash : Storage.Pre → Nat
  location : P → Storage.Loc
  field : P → Field
  width_agrees : ∀ p, StorageWidth D (L (path p)) (field p).width
  codec : (p : P) → ScalarCodec D (L (path p)) (field p)
  view : Source.Storage D L → SlotView → Prop
  realize : ∀ s, ∃ m, view s m
  read_agrees : ∀ s m p v, view s m → s.read (path p) = some v →
    (field p).find (m (physicalSlot hash (location p))).val = ((codec p).encode v).val
  writeback : SlotView → Source.Storage D L → Option (Source.Storage D L)
  unchanged : ∀ s m, view s m → writeback m s = some s
  result_view : ∀ s m s', writeback m s = some s' → view s' m

/-- Every physical observation of the existing typed persistent/transient
state is restored by the *actual* source frame rollback theorem. Residual
journaling remains a separate integration obligation. -/
theorem source_view_rollback {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy}
    (s : Source.ExecState D L T) (os : List (Source.Op D L T))
    (this caller : Roadmap.Address) (value : Roadmap.Word) (input : Roadmap.Bytes) (static : Bool)
    (view : Source.ExecState D L T → SlotView) :
    view ((s.enter this caller value input static).rollback (s.run os)) = view s := by
  rw [Source.rollback_run]

/-- Source transaction reset keeps persistent storage. -/
theorem persistent_reset {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy}
    (s : Source.ExecState D L T) (view : Source.World D L → SlotView) :
    view s.endTx.world = view s.world := rfl

/-- Actual source transient reads after reset are typed defaults. -/
theorem transient_reset {D : Source.Layout}
    {L T : Roadmap.Address → Source.SPath → Source.STy}
    (s : Source.ExecState D L T) (a : Roadmap.Address) (p : Source.SPath) :
    (s.endTx.transient.cells a).read p = Source.Val.default D (T a p) :=
  Source.endTx_transient s a p

end Solidity.Yul.Views
