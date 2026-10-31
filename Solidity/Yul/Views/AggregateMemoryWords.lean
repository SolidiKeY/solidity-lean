import Solidity.Yul.Views.ByteHeapRealization

/-! Concrete word-cell serialization and intrinsic aggregate witnesses. Scalar
members use the existing Source.Val.word; references use actual child typing
and real Placement bounds, never inline child contents or guessed ownership. -/
namespace Solidity.Yul.Views

def wordListView : List Roadmap.Word → ByteView → Nat → ByteView
  | [], m, _ => m
  | w :: ws, m, base => mstore (wordListView ws m (base + 32)) base w

theorem wordList_residual (ws : List Roadmap.Word) (m : ByteView) (base a : Nat)
    (outside : a < base ∨ base + ws.length * 32 ≤ a) : wordListView ws m base a = m a := by
  induction ws generalizing base with
  | nil => rfl
  | cons w ws ih =>
    rw [wordListView, mstore_outside _ _ _ _ (by simp only [List.length_cons] at outside; omega)]
    exact ih (base + 32) (by simp only [List.length_cons] at outside; omega)

theorem wordList_read (ws : List Roadmap.Word) (m : ByteView) (base i : Nat) (w : Roadmap.Word)
    (found : ws[i]? = some w) : mload (wordListView ws m base) (base + i * 32) = w := by
  induction ws generalizing base i with
  | nil => cases found
  | cons head tail ih =>
    cases i with
    | zero =>
      have eq := Option.some.inj found
      subst w
      simpa only [wordListView, Nat.zero_mul, Nat.add_zero] using mload_mstore (wordListView tail m (base + 32)) base head
    | succ i =>
      have keep : mload (wordListView (head :: tail) m base) (base + (i + 1) * 32) =
          mload (wordListView tail m (base + 32)) (base + (i + 1) * 32) := by
        apply mload_congr
        intro j
        exact mstore_outside _ _ _ _ (by have hj := j.isLt; omega)
      rw [keep]
      have eq : base + (i + 1) * 32 = (base + 32) + i * 32 := by omega
      rw [eq]
      exact ih _ _ found

theorem wordList_unchanged (ws : List Roadmap.Word) (m : ByteView) (base : Nat)
    (reads : ∀ i w, ws[i]? = some w → mload m (base + i * 32) = w) : wordListView ws m base = m := by
  induction ws generalizing base with
  | nil => rfl
  | cons w ws ih =>
    rw [wordListView, ih (base + 32) (by
      intro i v hv
      have h := reads (i + 1) v hv
      have eq : base + (i + 1) * 32 = (base + 32) + i * 32 := by omega
      rwa [eq] at h)]
    have h := reads 0 w rfl
    simp only [Nat.zero_mul, Nat.add_zero] at h
    rw [← h, mstore_mload]

theorem placement_owned_address {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) (σ : Source.STy) (owned : h.ty a = some σ) : p.address a < 2 ^ 256 := by
  have present : (h.cells a).isSome := by
    cases hc : h.cells a with
    | none => simp only [Source.Heap.ty, hc, Option.map_none] at owned; cases owned
    | some x => rfl
  have bound := p.ends a present
  have free := p.free.isLt
  omega

def ownedPointerWord {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) (σ : Source.STy) (owned : h.ty a = some σ) : Roadmap.Word :=
  ⟨p.address a, placement_owned_address p a σ owned⟩

inductive MemoryElement {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    {τ : Source.STy} → Source.Val D τ → Roadmap.Word → Prop where
  | scalar {τ} (v : Source.Val D τ) (w : Roadmap.Word) (encoded : v.word = some w) : MemoryElement p v w
  | pointer {τ : Source.STy} (loc : τ.loc? = some .memory) (a : Nat) (σ : Source.STy)
      (owned : h.ty a = some σ) (shape : σ.memShape = τ.memShape) :
      MemoryElement p (.memRef loc a) (ownedPointerWord p a σ owned)

theorem MemoryElement.read {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {v : Source.Val D τ} {w : Roadmap.Word} (e : MemoryElement p v w) :
    ElementWord p.address v w := by
  cases e with
  | scalar v w read => exact .scalar v w read
  | pointer loc a σ owned shape => exact .reference loc a (placement_owned_address p a σ owned)

theorem elementWord_unique {D : Source.Layout} {address : Nat → Nat} {τ : Source.STy}
    {v : Source.Val D τ} {w w' : Roadmap.Word}
    (a : ElementWord address v w) (b : ElementWord address v w') : w = w' := by
  cases a with
  | scalar v w encoded =>
    cases b with
    | scalar _ _ encoded' => exact Option.some.inj (encoded.symm.trans encoded')
    | reference loc id bound => cases encoded
  | reference loc id bound =>
    cases b with
    | scalar _ _ encoded => cases encoded
    | reference _ _ _ => rfl

inductive MemoryFields {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    {τs : List Source.STy} → Source.DataList D τs → List Roadmap.Word → Prop where
  | nil : MemoryFields p .nil []
  | cons {τ : Source.STy} {τs : List Source.STy} (v : Source.Val D τ) (w : Roadmap.Word) (encoded : MemoryElement p v w)
      (fs : Source.DataList D τs) (ws : List Roadmap.Word) (rest : MemoryFields p fs ws) :
      MemoryFields p (.cons (.val v) fs) (w :: ws)

theorem MemoryFields.length {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word} (e : MemoryFields p fs ws) :
    ws.length = τs.length := by
  induction e with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

theorem MemoryFields.nth {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word} (e : MemoryFields p fs ws)
    (i : Nat) (τ : Source.STy) (v : Source.Val D τ) (w : Roadmap.Word)
    (found : fs.nth i τ = .ok (.val v)) (read : ElementWord p.address v w) : ws[i]? = some w := by
  induction e generalizing i τ with
  | nil => simp only [Source.DataList.nth, Source.stuck] at found; cases found
  | @cons σ τs value word encoded fs ws rest ih =>
    cases i with
    | zero =>
      by_cases eq : σ = τ
      · subst τ
        simp only [Source.DataList.nth, dite_true] at found
        cases found
        exact congrArg some (elementWord_unique encoded.read read)
      · simp only [Source.DataList.nth, eq, dite_false, Source.stuck] at found; cases found
    | succ i => exact ih i τ v found read

end Solidity.Yul.Views
