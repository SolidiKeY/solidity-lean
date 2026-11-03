import Solidity.Yul.Views.ScalarWriteback

/-! Canonical preparation requests become actual typed Source.Op updates. The
update computes from the account's current storage, not a stale snapshot.
None is unsupported preparation input, never a Yul execution verdict.
Successful assembly integration still owes non-static/resource premises. -/
namespace Solidity.Yul.Views

def canonicalAccountWrite? {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    {f : Field} (a : Roadmap.Address) (p : Source.SPath) (c : ScalarCodec D (L a p) f)
    (slot : Roadmap.Word) (m : SlotView) : Option (Source.Op D L T) :=
  (canonicalScalarDecode c (f.findWord (m slot))).map
    (fun v => .account a (fun ac => {ac with storage := preserveScalarWrite p c v ac.storage}))

def canonicalTransientWrite? {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    {f : Field} (a : Roadmap.Address) (p : Source.SPath) (c : ScalarCodec D (T a p) f)
    (slot : Roadmap.Word) (m : SlotView) : Option (Source.Op D L T) :=
  (canonicalScalarDecode c (f.findWord (m slot))).map
    (fun v => .transient a (preserveScalarWrite p c v))

/-- Only the test/preparation boundary skips an unsupported request. -/
def applyPreparedWrite {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (s : Source.ExecState D L T) (request : Option (Source.Op D L T)) : Source.ExecState D L T :=
  (request.map s.apply).getD s

theorem accountWrite_actual_storage {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    {f : Field} (a : Roadmap.Address) (p : Source.SPath) (c : ScalarCodec D (L a p) f)
    (slot : Roadmap.Word) (m : SlotView) (s : Source.ExecState D L T) (op : Source.Op D L T)
    (e : canonicalAccountWrite? a p c slot m = some op) :
    ∃ storage, canonicalPathWriteback p c slot m (s.world.accounts a).storage = some storage ∧
      ((s.apply op).world.accounts a).storage = storage ∧ (s.apply op).transient = s.transient ∧
      (s.apply op).journal.length = s.journal.length + 1 := by
  obtain ⟨v, hd, hop⟩ := Option.map_eq_some_iff.mp e
  subst op
  refine ⟨preserveScalarWrite p c v (s.world.accounts a).storage, ?_, ?_, rfl, ?_⟩
  · simp only [canonicalPathWriteback, hd, Option.map_some]
  · simp only [Source.ExecState.apply, Source.World.set_get]
  · exact Source.ExecState.journal_apply _ _

theorem transientWrite_actual_storage {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    {f : Field} (a : Roadmap.Address) (p : Source.SPath) (c : ScalarCodec D (T a p) f)
    (slot : Roadmap.Word) (m : SlotView) (s : Source.ExecState D L T) (op : Source.Op D L T)
    (e : canonicalTransientWrite? a p c slot m = some op) :
    ∃ storage, canonicalPathWriteback p c slot m (s.transient.cells a) = some storage ∧
      (s.apply op).transient.cells a = storage ∧ (s.apply op).world = s.world ∧
      (s.apply op).journal.length = s.journal.length + 1 := by
  obtain ⟨v, hd, hop⟩ := Option.map_eq_some_iff.mp e
  subst op
  refine ⟨preserveScalarWrite p c v (s.transient.cells a), ?_, ?_, rfl, ?_⟩
  · simp only [canonicalPathWriteback, hd, Option.map_some]
  · simp only [Source.ExecState.apply, Source.Transient.set, dif_pos]
  · exact Source.ExecState.journal_apply _ _

theorem accountWrite_source_frame_other {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    {f : Field} (a : Roadmap.Address) (p q : Source.SPath) (c : ScalarCodec D (L a p) f)
    (slot : Roadmap.Word) (m : SlotView) (s : Source.ExecState D L T) (op : Source.Op D L T)
    (e : canonicalAccountWrite? a p c slot m = some op) (h : q ≠ p) :
    ((s.apply op).world.accounts a).storage.cell q = (s.world.accounts a).storage.cell q := by
  obtain ⟨v, hd, hop⟩ := Option.map_eq_some_iff.mp e
  subst op
  simp only [Source.ExecState.apply, Source.World.set_get]
  exact preserveScalarWrite_cell_other p q c v _ h

theorem transientWrite_source_frame_other {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    {f : Field} (a : Roadmap.Address) (p q : Source.SPath) (c : ScalarCodec D (T a p) f)
    (slot : Roadmap.Word) (m : SlotView) (s : Source.ExecState D L T) (op : Source.Op D L T)
    (e : canonicalTransientWrite? a p c slot m = some op) (h : q ≠ p) :
    ((s.apply op).transient.cells a).cell q = (s.transient.cells a).cell q := by
  obtain ⟨v, hd, hop⟩ := Option.map_eq_some_iff.mp e
  subst op
  simp only [Source.ExecState.apply, Source.Transient.set, dif_pos]
  exact preserveScalarWrite_cell_other p q c v _ h

theorem invalidAccountRequest_unchanged {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    {f : Field} (a : Roadmap.Address) (p : Source.SPath) (c : ScalarCodec D (L a p) f)
    (slot : Roadmap.Word) (m : SlotView) (s : Source.ExecState D L T)
    (e : canonicalScalarDecode c (f.findWord (m slot)) = none) :
    applyPreparedWrite s (canonicalAccountWrite? (T := T) a p c slot m) = s := by
  simp only [canonicalAccountWrite?, e, Option.map_none, applyPreparedWrite, Option.getD_none]

end Solidity.Yul.Views
