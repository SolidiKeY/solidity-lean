import Solidity.Yul.Views.MixedHeapView

namespace Solidity.Yul.Views

theorem MemoryElement.refOK {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h}
    {τ : Source.STy} {v : Source.Val E.layout τ} {w : Roadmap.Word} (e : MemoryElement p v w) :
    Source.Val.RefOK E h.ty v := by
  cases e with
  | scalar v w encoded => cases v <;> first | trivial | cases encoded
  | pointer loc a σ owned shape => exact ⟨σ, owned, shape⟩

theorem MemoryFields.dataOK {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h}
    {τs : List Source.STy} {fs : Source.DataList E.layout τs} {ws : List Roadmap.Word} (e : MemoryFields p fs ws) :
    Source.DataListOK E h.ty fs := by
  induction e with
  | nil => exact .nil
  | cons v w encoded fs ws rest ih => exact .cons (.val encoded.refOK) ih

theorem MemoryFields.allVal {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h}
    {τs : List Source.STy} {fs : Source.DataList E.layout τs} {ws : List Roadmap.Word} (e : MemoryFields p fs ws) :
    fs.AllVal := by
  induction e with
  | nil => trivial
  | cons v w encoded fs ws rest ih => exact ⟨⟨v, rfl⟩, ih⟩

theorem MemoryObjectWords.dataOK {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h}
    {τ : Source.STy} {d : Source.Data E.layout τ} {ws : List Roadmap.Word} (e : MemoryObjectWords p d ws) :
    Source.DataOK E h.ty d := by
  cases e with
  | value v w encoded => exact .val encoded.refOK
  | array len hl bound values words encoded => exact .array (fun i => .val (encoded i).refOK)
  | strct fs ws fields => exact .struct fields.dataOK

theorem MemoryObjectWords.inner {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h}
    {τ : Source.STy} {d : Source.Data E.layout τ} {ws : List Roadmap.Word} (e : MemoryObjectWords p d ws) :
    Source.Data.Inner (E := E) d := by
  cases e with
  | value _ _ _ => trivial
  | array len hl bound values words encoded => exact fun i => ⟨values i, rfl⟩
  | strct fs ws fields => exact fields.allVal

theorem MemoryImage.dataOK {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h}
    {τ : Source.STy} {d : Source.Data E.layout τ} (image : MemoryImage p d) : Source.DataOK E h.ty d := by
  cases image with
  | bytes bs _ => exact .bytes bs
  | string bs _ => exact .string bs
  | words d ws e => exact e.dataOK

theorem MemoryImage.inner {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h}
    {τ : Source.STy} {d : Source.Data E.layout τ} (image : MemoryImage p d) : Source.Data.Inner (E := E) d := by
  cases image with
  | bytes _ _ => trivial
  | string _ _ => trivial
  | words d ws e => exact e.inner

theorem MemoryImage.top {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (a : Nat) {τ : Source.STy} {d : Source.Data E.layout τ} (image : MemoryImage p d)
    (found : h.get a = some ⟨τ, d⟩) : Source.Data.Top (E := E) d := by
  cases image with
  | bytes _ _ => trivial
  | string _ _ => trivial
  | words d ws e =>
    cases e with
    | value v w encoded => exact False.elim (no_value_memory_shape v (p.shape a) (p.typed a _ _ found))
    | array _ _ _ _ _ _ => trivial
    | strct _ _ _ => trivial

theorem mixedHeap_owner_invariants {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) :
    Source.HeapOK (E := E) h ∧ Source.HeapShaped (E := E) h ∧ Source.HeapInner (E := E) h := by
  have every (a : Nat) (x : Σ τ, Source.Data E.layout τ) (found : h.get a = some x) :
      Source.DataOK E h.ty x.2 ∧ Source.Data.Top (E := E) x.2 ∧ Source.Data.Inner (E := E) x.2 := by
    have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
    obtain ⟨e, member, eq⟩ := coverage a present
    subst a
    have same := Option.some.inj (found.symm.trans e.found)
    cases same
    exact ⟨e.image.dataOK, e.image.top p e.id e.found, e.image.inner⟩
  exact ⟨fun a x found => (every a x found).1, fun a x found => (every a x found).2.1,
    fun a x found => (every a x found).2.2⟩

end Solidity.Yul.Views
