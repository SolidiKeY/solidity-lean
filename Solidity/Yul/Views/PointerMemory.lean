import Solidity.Yul.Views.MixedMemoryMemOK

/-! Decode pointer WORDS against a finite collection of actual typed owned
heap entries. Coverage makes the candidate set complete for that supported heap;
there is no artificial address/length cap, guessed gap or hash injectivity.
None means unsupported preparation, not Yul refusal/no-op/shared-zero semantics. -/
namespace Solidity.Yul.Views

def pointerCandidate {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (τ : Source.STy) (word : Roadmap.Word) (e : MixedHeapEntry p) : Bool :=
  decide (e.ty.memShape = τ.memShape ∧ p.address e.id = word.val)

def decodeMemoryPointer {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (loc : τ.loc? = some .memory)
    (word : Roadmap.Word) : Option (Source.Val D τ) :=
  (es.find? (pointerCandidate τ word)).map (fun e => .memRef loc e.id)

theorem decodeMemoryPointer_sound {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (loc : τ.loc? = some .memory)
    (word : Roadmap.Word) (v : Source.Val E.layout τ) (decoded : decodeMemoryPointer p es τ loc word = some v) :
    Source.Val.RefOK E h.ty v ∧ ∃ e ∈ es, p.address e.id = word.val ∧ v = .memRef loc e.id := by
  obtain ⟨e, found, same⟩ := Option.map_eq_some_iff.mp decoded
  have flag := List.find?_some found
  change decide (e.ty.memShape = τ.memShape ∧ p.address e.id = word.val) = true at flag
  have pred : e.ty.memShape = τ.memShape ∧ p.address e.id = word.val := of_decide_eq_true flag
  subst v
  exact ⟨⟨e.ty, heap_ty_of_get h e.id e.ty e.data e.found, pred.1⟩,
    e, List.mem_of_find?_eq_some found, pred.2, rfl⟩

theorem decodeMemoryPointer_encode {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (τ : Source.STy)
    (loc : τ.loc? = some .memory) (a : Nat) (σ : Source.STy) (owned : h.ty a = some σ)
    (shape : σ.memShape = τ.memShape) :
    decodeMemoryPointer p es τ loc (ownedPointerWord p a σ owned) = some (.memRef loc a) := by
  have present : (h.cells a).isSome := by
    cases hc : h.cells a with
    | none => simp only [Source.Heap.ty, hc, Option.map_none] at owned; cases owned
    | some _ => rfl
  obtain ⟨e, member, id⟩ := coverage a present
  have ty : e.ty = σ := Option.some.inj ((heap_ty_of_get h e.id _ _ e.found).symm.trans (id ▸ owned))
  have yes : pointerCandidate τ (ownedPointerWord p a σ owned) e = true := by
    unfold pointerCandidate
    simp only [decide_eq_true_eq]
    exact ⟨ty ▸ shape, congrArg p.address id⟩
  unfold decodeMemoryPointer
  cases found : es.find? (pointerCandidate τ (ownedPointerWord p a σ owned)) with
  | none => exact False.elim ((List.find?_eq_none.mp found) e member yes)
  | some f =>
    have flag := List.find?_some found
    change decide (f.ty.memShape = τ.memShape ∧ p.address f.id = p.address a) = true at flag
    have pred : f.ty.memShape = τ.memShape ∧ p.address f.id = p.address a := of_decide_eq_true flag
    have occupied : (h.cells f.id).isSome := by change (h.get f.id).isSome = true; rw [f.found]; rfl
    have same := p.distinct f.id a occupied present pred.2
    simp only [Option.map_some]
    rw [same]

def pointerStateWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (F : Source.Fr) (horizon root index : Nat)
    (τ : Source.STy) (loc : τ.loc? = some .memory) (word : Roadmap.Word) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  (decodeMemoryPointer p es τ loc word).map (fun v => (Source.writeLoc F horizon (.mem root index) v).run s)

theorem pointerStateWriteback_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (F : Source.Fr)
    (horizon root index : Nat) (τ : Source.STy) (loc : τ.loc? = some .memory) (word : Roadmap.Word)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : pointerStateWriteback s p es F horizon root index τ loc word = some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  obtain ⟨v, decoded, same⟩ := Option.map_eq_some_iff.mp step
  subst result
  have keep := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := H) F horizon (.mem root index) v s
    ⟨ok, (decodeMemoryPointer_sound p es τ loc word v decoded).1⟩
  cases run : (Source.writeLoc F horizon (.mem root index) v).run s with
  | mk outcome out => cases outcome <;> simpa only [run] using keep

/-- Selected physical struct-field writeback. Real declaration/index/lookup
premises identify the word offset; this does not decode other changed fields. -/
def structPointerWriteback {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (F : Source.Fr) (horizon root : Nat)
    (name : Source.DeclName) (fs : Source.DataList E.layout (E.layout.fields name))
    (_found : s.2.heap.get root = some ⟨.struct .memory name, .struct fs⟩)
    (index : Fin (E.layout.fields name).length) (τ : Source.STy) (loc : τ.loc? = some .memory)
    (_field : (E.layout.fields name)[index.val]? = some τ) (m : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  pointerStateWriteback s p es F horizon root index.val τ loc (mload m (p.address root + index.val * 32))

theorem structPointerWriteback_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (F : Source.Fr)
    (horizon root : Nat) (name : Source.DeclName) (fs : Source.DataList E.layout (E.layout.fields name))
    (found : s.2.heap.get root = some ⟨.struct .memory name, .struct fs⟩)
    (index : Fin (E.layout.fields name).length) (τ : Source.STy) (loc : τ.loc? = some .memory)
    (field : (E.layout.fields name)[index.val]? = some τ) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : structPointerWriteback s p es F horizon root name fs found index τ loc field m = some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 :=
  pointerStateWriteback_MemOK E H s p es F horizon root index.val τ loc _ result step ok

theorem structPointer_word_fits {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (root : Nat)
    (name : Source.DeclName) (fs : Source.DataList D (D.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct fs⟩) (index : Fin (D.fields name).length) :
    p.address root + index.val * 32 + 32 ≤ p.address root + (p.shape root).size ∧
    p.address root + index.val * 32 + 32 ≤ p.free.val := by
  have present : (h.cells root).isSome := by change (h.get root).isSome = true; rw [found]; rfl
  have ends := p.ends root present
  have shape := p.typed root _ _ found
  generalize he : p.shape root = sh at shape
  cases shape
  rw [he] at ends
  have bound := index.isLt
  simp only [MemoryShape.size] at ends ⊢
  omega

theorem decodeMemoryPointer_read {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (loc : τ.loc? = some .memory)
    (word : Roadmap.Word) (v : Source.Val D τ) (decoded : decodeMemoryPointer p es τ loc word = some v) :
    ElementWord p.address v word := by
  obtain ⟨e, found, same⟩ := Option.map_eq_some_iff.mp decoded
  have flag := List.find?_some found
  change decide (e.ty.memShape = τ.memShape ∧ p.address e.id = word.val) = true at flag
  have pred : e.ty.memShape = τ.memShape ∧ p.address e.id = word.val := of_decide_eq_true flag
  subst v
  have owned := heap_ty_of_get h e.id e.ty e.data e.found
  have raw : ownedPointerWord p e.id e.ty owned = word := Fin.ext pred.2
  rw [← raw]
  exact MemoryElement.read (.pointer loc e.id e.ty owned pred.1)

end Solidity.Yul.Views
