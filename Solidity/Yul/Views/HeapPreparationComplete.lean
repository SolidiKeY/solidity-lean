import Solidity.Yul.Views.HeapEnumeration

namespace Solidity.Yul.Views

theorem prepareFin_isSome (n : Nat) (A : Fin n → Type) (f : (i : Fin n) → Option (A i))
    (complete : ∀ i, (f i).isSome) : (prepareFin n A f).isSome := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨head,one⟩ := Option.isSome_iff_exists.mp (complete 0)
    obtain ⟨tail,rest⟩ := Option.isSome_iff_exists.mp (ih (fun i => A i.succ) (fun i => f i.succ) (fun i => complete i.succ))
    rw [prepareFin,one]
    change ((prepareFin n (fun i => A i.succ) (fun i => f i.succ)).bind _).isSome
    rw [rest]
    rfl

theorem prepareElement_complete {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {τ : Source.STy} (v : Source.Val D τ) (w : Roadmap.Word) (encoded : MemoryElement p v w) :
    (prepareElement p v).isSome := by
  unfold prepareElement
  split
  · rfl
  · rename_i absent
    cases encoded with
    | scalar _ _ read => rw [read] at absent; cases absent
    | pointer loc a σ owned shape =>
      change ((h.ty a).pbind (fun σ owned => if shape : σ.memShape = τ.memShape then some _ else none)).isSome
      rw [Option.pbind_some' owned,dif_pos shape]
      rfl

theorem prepareMember_complete {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {τ : Source.STy} (v : Source.Val D τ) (w : Roadmap.Word) (encoded : MemoryElement p v w) :
    (prepareMember p (.val v)).isSome := by
  change ((prepareElement p v).map _).isSome
  rw [Option.isSome_map]
  exact prepareElement_complete p v w encoded

theorem prepareFields_complete {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word} (fields : MemoryFields p fs ws) :
    (prepareFields p τs fs).isSome := by
  induction fields with
  | nil => rfl
  | cons v w encoded fs ws fields ih =>
    obtain ⟨head,one⟩ := Option.isSome_iff_exists.mp (prepareMember_complete p v w encoded)
    obtain ⟨tail,rest⟩ := Option.isSome_iff_exists.mp ih
    change ((prepareMember p (.val v)).bind _).isSome
    rw [one]
    simp only [Option.bind_some,rest,Option.map_some,Option.isSome_some]

/-- Constructive completeness for the EXISTING intrinsic serialization relation.
This is proved by its actual constructors, never an assumed inverse/read law. -/
theorem prepareHeapImage_complete {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) (τ : Source.STy) (d : Source.Data D τ) (found : h.get a = some ⟨τ,d⟩) (image : MemoryImage p d) :
    (prepareHeapImage p a τ d found).isSome := by
  cases image with
  | bytes bs bound => rfl
  | string bs bound => rfl
  | words d ws encoded =>
    cases encoded with
    | value v w elem => exact False.elim (no_value_memory_shape v _ (p.typed a _ _ found))
    | @array l σ k n hl bound values words elements =>
      change ((prepareFin n _ (fun i => prepareMember p (.val (values i)))).map _).isSome
      rw [Option.isSome_map]
      exact prepareFin_isSome n _ _ (fun i => prepareMember_complete p (values i) (words i) (elements i))
    | strct fs ws fields =>
      change ((prepareFields p _ fs).map _).isSome
      rw [Option.isSome_map]
      exact prepareFields_complete p fields

/-- Precise faithful ordinary representation: existing MemoryImage constructors
on each actual lookup. No inventory/coverage/final-view theorem is an input. -/
def HeapImageRepresentable {D : Source.Layout} {h : Source.Heap D} (p : Placement h) : Prop :=
  ∀ a τ d (_found : h.get a = some ⟨τ,d⟩), Nonempty (MemoryImage p d)

theorem heapEntryAt_complete {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) (τ : Source.STy) (d : Source.Data D τ) (found : h.get a = some ⟨τ,d⟩)
    (image : MemoryImage p d) : (heapEntryAt p a).isSome := by
  unfold heapEntryAt
  rw [Option.pbind_some' found,Option.isSome_map]
  exact prepareHeapImage_complete p a τ d found image

theorem representable_no_unsupported {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (represented : HeapImageRepresentable p) : unsupportedHeapCells p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a member
  obtain ⟨_,present,no⟩ := (unsupportedHeapCells_mem p a).mp member
  obtain ⟨x,found⟩ := Option.isSome_iff_exists.mp present
  obtain ⟨image⟩ := represented a x.1 x.2 found
  have yes := heapEntryAt_complete p a x.1 x.2 found image
  rw [no] at yes
  cases yes

theorem no_unsupported_representable {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (noneUnsupported : unsupportedHeapCells p = []) : HeapImageRepresentable p := by
  intro a τ d found
  have bound : a < h.next := by
    apply Nat.lt_of_not_le
    intro no
    have impossible := h.bounded a no
    change h.cells a = some ⟨τ,d⟩ at found
    rw [impossible] at found
    cases found
  cases yes : heapEntryAt p a with
  | none =>
    have bad := (unsupportedHeapCells_mem p a).mpr ⟨bound,by rw [found]; rfl,yes⟩
    rw [noneUnsupported] at bad
    cases bad
  | some e =>
    have eq := heapEntryAt_id p a e yes
    have lookup : (⟨τ,d⟩ : Sigma (Source.Data D)) = ⟨e.ty,e.data⟩ := Option.some.inj (found.symm.trans (eq ▸ e.found))
    cases lookup
    exact ⟨e.image⟩

end Solidity.Yul.Views
