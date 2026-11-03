import Solidity.Yul.Views.PackedResidualPlan

namespace Solidity.Yul.Views

/-- Representation invariant ONLY: carrier words/journal entries store zero in
owned bytes. The remaining bytes are arbitrary, including high bits. This is
not a supplied read/view/inverse/safety/adequacy law. -/
def PackedComplementValid {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy} (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (r : ResidualJournal complementCarrierOwnership) : Prop :=
  (∀ k i, packedCarrierOwns ps ts k i = true → lowByte (r.cells k) i = 0) ∧
  (∀ w ∈ r.journal, ∀ i, packedCarrierOwns ps ts w.1 i = true → lowByte w.2 i = 0)

def initialPackedComplement {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy} (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (raw : ResidualKey complementCarrierOwnership → Roadmap.Word) : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => complementWord (packedCarrierOwns ps ts k) (raw k),[]⟩

theorem initialPackedComplement_valid {D L T ps ts} (raw : ResidualKey complementCarrierOwnership → Roadmap.Word) :
    @PackedComplementValid D L T ps ts (initialPackedComplement ps ts raw) := by
  constructor
  · intro k i owned
    rw [show (initialPackedComplement ps ts raw).cells k = complementWord (packedCarrierOwns ps ts k) (raw k) from rfl,
      complementWord_byte,owned]
    rfl
  · intro w member; cases member

theorem packedComplement_write {D L T ps ts} (r : ResidualJournal complementCarrierOwnership)
    (valid : @PackedComplementValid D L T ps ts r) (k : ResidualKey complementCarrierOwnership) (v : Roadmap.Word)
    (masked : ∀ i, packedCarrierOwns ps ts k i = true → lowByte v i = 0) : PackedComplementValid ps ts (residualWrite r (k,v)) := by
  constructor
  · intro q i owned
    by_cases same : q = k
    · subst q; rw [show (residualWrite r (k,v)).cells k = v from residualSave_get _ _ _]; exact masked i owned
    · rw [show (residualWrite r (k,v)).cells q = r.cells q from residualSave_other _ _ _ _ same]
      exact valid.1 q i owned
  · intro w member i owned
    rcases List.mem_cons.mp member with same | old
    · subst w; exact valid.1 k i owned
    · exact valid.2 w old i owned

theorem packedComplement_plan {D L T ps ts} (r : ResidualJournal complementCarrierOwnership)
    (valid : @PackedComplementValid D L T ps ts r) (p : PackedSlotPlan ps ts) :
    PackedComplementValid ps ts (residualWrite r p.residualUpdate) := by
  apply packedComplement_write r valid
  intro i owned
  rw [complementWord_byte,owned]
  rfl

theorem packedComplement_run {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (valid : @PackedComplementValid D L T ps ts s.residual) (plans : List (PackedSlotPlan ps ts)) :
    PackedComplementValid ps ts (runPackedSlots s plans).residual := by
  induction plans generalizing s with
  | nil => exact valid
  | cons p plans ih => exact ih (applyPackedSlot s p) (packedComplement_plan _ valid p)

theorem packedComplement_undo {D L T ps ts} (r : ResidualJournal complementCarrierOwnership)
    (valid : @PackedComplementValid D L T ps ts r) : PackedComplementValid ps ts (residualUndo r) := by
  cases journal : r.journal with
  | nil => simpa only [residualUndo,journal] using valid
  | cons w ws =>
    have saved : ∀ i, packedCarrierOwns ps ts w.1 i = true → lowByte w.2 i = 0 := by
      intro i owned
      exact valid.2 w (by rw [journal]; exact List.mem_cons_self) i owned
    constructor
    · intro k i owned
      change lowByte ((residualUndo r).cells k) i = 0
      simp only [residualUndo,journal]
      by_cases same : k = w.1
      · subst k; rw [residualSave_get]; exact saved i owned
      · rw [residualSave_other _ _ _ _ same]; exact valid.1 k i owned
    · intro x member i owned
      have tail : x ∈ ws := by simpa only [residualUndo,journal] using member
      exact valid.2 x (by rw [journal]; exact List.mem_cons_of_mem _ tail) i owned

theorem packedComplement_undoN {D L T ps ts} (n : Nat) (r : ResidualJournal complementCarrierOwnership)
    (valid : @PackedComplementValid D L T ps ts r) : PackedComplementValid ps ts (residualUndoN n r) := by
  induction n generalizing r with
  | zero => exact valid
  | succ n ih => exact ih _ (packedComplement_undo r valid)

theorem packedComplement_rollback {D L T ps ts} (f : ResidualFrame) (s : ResidualCompanion D L T complementCarrierOwnership)
    (valid : @PackedComplementValid D L T ps ts s.residual) : PackedComplementValid ps ts (companionRollback f s).residual :=
  packedComplement_undoN _ _ valid

theorem packedComplement_endTx {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (valid : @PackedComplementValid D L T ps ts s.residual) : PackedComplementValid ps ts (companionEndTx s).residual := by
  constructor
  · intro k i owned
    change lowByte (if k.transient then (0 : Roadmap.Word) else s.residual.cells k) i = 0
    cases tr : k.transient
    · exact valid.1 k i owned
    · simp only [if_true]
      simp only [lowByte,wordByte,Fin.val_zero,Nat.zero_div]
      rfl
  · intro w member; cases member

end Solidity.Yul.Views
