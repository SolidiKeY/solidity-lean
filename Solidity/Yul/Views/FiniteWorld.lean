import Solidity.Yul.Views.FinitePaths

/-! Validated finite batches become actual source operations over CURRENT storage.
Preparation validates all fields before producing an operation. None is unsupported
canonical input, not a Yul verdict. Static-mode/source integration remains open. -/
namespace Solidity.Yul.Views

def finiteAccountWrite? {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (L a))) (m : SlotView) : Option (Source.Op D L T) :=
  (finitePrepare cs m).map (fun update => .account a (fun ac => {ac with storage := update ac.storage}))

def finiteTransientWrite? {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (T a))) (m : SlotView) : Option (Source.Op D L T) :=
  (finitePrepare cs m).map (fun update => .transient a update)

theorem finiteAccountWrite_actual {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (L a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (e : finiteAccountWrite? a cs m = some op) :
    ∃ out, finiteWriteback cs m (s.world.accounts a).storage = some out ∧
      ((s.apply op).world.accounts a).storage = out ∧ (s.apply op).transient = s.transient ∧
      (s.apply op).journal.length = s.journal.length + 1 := by
  obtain ⟨update, hp, ho⟩ := Option.map_eq_some_iff.mp e
  subst op
  refine ⟨update (s.world.accounts a).storage, ?_, ?_, rfl, Source.ExecState.journal_apply _ _⟩
  · rw [finiteWriteback_prepare, hp]; rfl
  · simp only [Source.ExecState.apply, Source.World.set_get]

theorem finiteTransientWrite_actual {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (T a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (e : finiteTransientWrite? a cs m = some op) :
    ∃ out, finiteWriteback cs m (s.transient.cells a) = some out ∧
      (s.apply op).transient.cells a = out ∧ (s.apply op).world = s.world ∧
      (s.apply op).journal.length = s.journal.length + 1 := by
  obtain ⟨update, hp, ho⟩ := Option.map_eq_some_iff.mp e
  subst op
  refine ⟨update (s.transient.cells a), ?_, ?_, rfl, Source.ExecState.journal_apply _ _⟩
  · rw [finiteWriteback_prepare, hp]; rfl
  · simp only [Source.ExecState.apply, Source.Transient.set, dif_pos]

theorem finiteAccountWrite_view {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (L a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (sep : finiteSeparated cs)
    (e : finiteAccountWrite? a cs m = some op) : finiteView cs ((s.apply op).world.accounts a).storage m := by
  obtain ⟨out, hw, hs, _, _⟩ := finiteAccountWrite_actual a cs m s op e
  rw [hs]
  exact finiteWriteback_result_view cs m _ out sep hw

theorem finiteAccountWrite_other {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (L a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (e : finiteAccountWrite? a cs m = some op)
    (q : Source.SPath) (unrelated : ∀ c ∈ cs, q ≠ c.path) :
    ((s.apply op).world.accounts a).storage.cell q = (s.world.accounts a).storage.cell q := by
  obtain ⟨out, hw, hs, _, _⟩ := finiteAccountWrite_actual a cs m s op e
  rw [hs]
  exact finiteWriteback_other cs m _ out hw q unrelated

theorem finiteAccountWrite_unchanged {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (L a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (e : finiteAccountWrite? a cs m = some op)
    (h : finiteView cs (s.world.accounts a).storage m) :
    ((s.apply op).world.accounts a).storage = (s.world.accounts a).storage := by
  obtain ⟨out, hw, hs, _, _⟩ := finiteAccountWrite_actual a cs m s op e
  rw [finiteWriteback_unchanged cs m _ h] at hw
  exact hs.trans (Option.some.inj hw).symm

theorem finiteTransientWrite_view {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (T a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (sep : finiteSeparated cs)
    (e : finiteTransientWrite? a cs m = some op) : finiteView cs ((s.apply op).transient.cells a) m := by
  obtain ⟨out, hw, hs, _, _⟩ := finiteTransientWrite_actual a cs m s op e
  rw [hs]
  exact finiteWriteback_result_view cs m _ out sep hw

theorem finiteTransientWrite_other {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (T a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (e : finiteTransientWrite? a cs m = some op)
    (q : Source.SPath) (unrelated : ∀ c ∈ cs, q ≠ c.path) :
    ((s.apply op).transient.cells a).cell q = (s.transient.cells a).cell q := by
  obtain ⟨out, hw, hs, _, _⟩ := finiteTransientWrite_actual a cs m s op e
  rw [hs]
  exact finiteWriteback_other cs m _ out hw q unrelated

theorem finiteTransientWrite_unchanged {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (a : Roadmap.Address) (cs : List (ScalarPath D (T a))) (m : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T) (e : finiteTransientWrite? a cs m = some op)
    (h : finiteView cs (s.transient.cells a) m) :
    (s.apply op).transient.cells a = s.transient.cells a := by
  obtain ⟨out, hw, hs, _, _⟩ := finiteTransientWrite_actual a cs m s op e
  rw [finiteWriteback_unchanged cs m _ h] at hw
  exact hs.trans (Option.some.inj hw).symm

end Solidity.Yul.Views
