import Solidity.Theory.Typed.Mem

/-!
# A copy into memory, below its root

What `SVal.copyStToM` leaves, member by member: the copy's root, and every
object the copy made for a member or an element, holds what the storage
value held there (`SVal.Mirrors`), each at an identity past the heap the
copy started from.  This is solkey's `readFromCopyToStorage` and
`readFromCopyToStorageIdentity` at any depth (`idC(idp, fxs)` with `fxs`
not empty), read on the typed heap: `Calculus/MemRead.lean`'s
`copyObjN` and `copyPathRd?` take their soundness from it.

The mirror is a property of the heap the copy leaves, so it is read at the
copy's node only; past a later write the memory walk reads down to the
node first.  It survives allocations (`SVal.Mirrors.wk`, `Heap.Keeps`),
which is what lets a struct's later members be copied after its earlier
ones.
-/

namespace Solidity

open Semantics (structDef lookupBy)

mutual
/-- **`w` holds, in `hp`, a copy of the storage value `v`**, every object
of it at an identity at least `n`: a word is the word, a struct's members
and an array's live elements are held member by member. -/
def SVal.Mirrors {H : HTy} (hp : Heap H) (n : Nat) : {T : Ty} → SVal T → MVal H T → Prop
  | _, .prim x, w => w = x
  | _, .struct fs, r => n ≤ (r : HRef H _).id ∧ SFields.Mirrors hp n fs (hp.get r)
  | _, .array e _ _, r =>
    n ≤ (r : HRef H _).id ∧ SVec.Mirrors hp n e (MObj.elems .dyn (hp.get r))
  | _, .fixed e, r =>
    n ≤ (r : HRef H _).id ∧ SVec.Mirrors hp n e (MObj.elems .fixed (hp.get r))
  | _, .map _ _, _ => False

/-- `SVal.Mirrors`, member by member. -/
def SFields.Mirrors {H : HTy} (hp : Heap H) (n : Nat) :
    {fs : List (Name × Ty)} → SFields fs → MFields H fs → Prop
  | _, .nil, _ => True
  | _, .cons v rest, x => v.Mirrors hp n x.1 ∧ SFields.Mirrors hp n rest x.2

/-- `SVal.Mirrors`, element by element. -/
def SVec.Mirrors {H : HTy} (hp : Heap H) (n : Nat) :
    {E : Ty} → {k : Nat} → SVec E k → List (MVal H E) → Prop
  | _, _, .nil, l => l = []
  | _, _, .cons v rest, l => ∃ w ws, l = w :: ws ∧ v.Mirrors hp n w ∧ SVec.Mirrors hp n rest ws
end


mutual
/-- A mirror past `n` is one past any `n' ≤ n`. -/
theorem SVal.Mirrors.mono {H : HTy} {hp : Heap H} {n n' : Nat} (hn : n' ≤ n) :
    {T : Ty} → (v : SVal T) → (w : MVal H T) → v.Mirrors hp n w → v.Mirrors hp n' w
  | _, .prim _, _, h => h
  | _, .struct fs, _, h => by
    simp only [SVal.Mirrors] at h ⊢
    exact ⟨Nat.le_trans hn h.1, SFields.Mirrors.mono hn fs _ h.2⟩
  | _, .array e _ _, _, h => by
    simp only [SVal.Mirrors] at h ⊢
    exact ⟨Nat.le_trans hn h.1, SVec.Mirrors.mono hn e _ h.2⟩
  | _, .fixed e, _, h => by
    simp only [SVal.Mirrors] at h ⊢
    exact ⟨Nat.le_trans hn h.1, SVec.Mirrors.mono hn e _ h.2⟩
  | _, .map _ _, _, h => by simp only [SVal.Mirrors] at h

theorem SFields.Mirrors.mono {H : HTy} {hp : Heap H} {n n' : Nat} (hn : n' ≤ n) :
    {fs : List (Name × Ty)} → (x : SFields fs) → (o : MFields H fs) →
    x.Mirrors hp n o → x.Mirrors hp n' o
  | _, .nil, _, _ => by simp only [SFields.Mirrors]
  | _, .cons v rest, o, h => by
    simp only [SFields.Mirrors] at h ⊢
    exact ⟨SVal.Mirrors.mono hn v _ h.1, SFields.Mirrors.mono hn rest _ h.2⟩

theorem SVec.Mirrors.mono {H : HTy} {hp : Heap H} {n n' : Nat} (hn : n' ≤ n) :
    {E : Ty} → {k : Nat} → (x : SVec E k) → (l : List (MVal H E)) →
    x.Mirrors hp n l → x.Mirrors hp n' l
  | _, _, .nil, _, h => h
  | _, _, .cons v rest, _, h => by
    simp only [SVec.Mirrors] at h ⊢
    obtain ⟨w, ws, rfl, h1, h2⟩ := h
    exact ⟨w, ws, rfl, SVal.Mirrors.mono hn v _ h1, SVec.Mirrors.mono hn rest _ h2⟩
end

mutual
/-- **A mirror survives a heap that keeps its objects** (`Heap.Keeps`): an
allocation after the copy. -/
theorem SVal.Mirrors.wk {H H' : HTy} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') {n : Nat} :
    {T : Ty} → (v : SVal T) → (w : MVal H T) → v.Mirrors hp n w → v.Mirrors hp' n (MVal.wk e T w)
  | _, .prim _, _, h => h
  | _, .struct fs, r, h => by
    simp only [SVal.Mirrors] at h ⊢
    refine ⟨h.1, ?_⟩
    show SFields.Mirrors hp' n fs (hp'.get (HRef.wk e r))
    rw [hk]
    exact SFields.Mirrors.wk hk fs _ h.2
  | _, .array a _ _, r, h => by
    simp only [SVal.Mirrors] at h ⊢
    refine ⟨h.1, ?_⟩
    show SVec.Mirrors hp' n a (MObj.elems .dyn (hp'.get (HRef.wk e r)))
    rw [hk, MObj.elems_wk]
    exact SVec.Mirrors.wk hk a _ h.2
  | _, .fixed a, r, h => by
    simp only [SVal.Mirrors] at h ⊢
    refine ⟨h.1, ?_⟩
    show SVec.Mirrors hp' n a (MObj.elems .fixed (hp'.get (HRef.wk e r)))
    rw [hk, MObj.elems_wk]
    exact SVec.Mirrors.wk hk a _ h.2
  | _, .map _ _, _, h => by simp only [SVal.Mirrors] at h

theorem SFields.Mirrors.wk {H H' : HTy} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') {n : Nat} :
    {fs : List (Name × Ty)} → (x : SFields fs) → (o : MFields H fs) →
    x.Mirrors hp n o → x.Mirrors hp' n (MFields.wk e fs o)
  | _, .nil, _, _ => by simp only [SFields.Mirrors]
  | _, .cons v rest, o, h => by
    simp only [SFields.Mirrors] at h ⊢
    exact ⟨SVal.Mirrors.wk hk v _ h.1, SFields.Mirrors.wk hk rest _ h.2⟩

theorem SVec.Mirrors.wk {H H' : HTy} {e : H <+: H'} {hp : Heap H} {hp' : Heap H'}
    (hk : Heap.Keeps e hp hp') {n : Nat} :
    {E : Ty} → {k : Nat} → (x : SVec E k) → (l : List (MVal H E)) →
    x.Mirrors hp n l → x.Mirrors hp' n (l.map (MVal.wk e E))
  | _, _, .nil, _, h => by simp only [SVec.Mirrors] at h ⊢; rw [h, List.map_nil]
  | _, _, .cons v rest, _, h => by
    simp only [SVec.Mirrors] at h ⊢
    obtain ⟨w, ws, rfl, h1, h2⟩ := h
    exact ⟨_, _, List.map_cons, SVal.Mirrors.wk hk v _ h1, SVec.Mirrors.wk hk rest _ h2⟩
end

mutual
/-- **A copy into memory mirrors what it copies**, every object it makes
past the heap it starts from. -/
theorem SVal.mirrors_copyStToM {H : HTy} (hp : Heap H) :
    {T : Ty} → (v : SVal T) → (h : T.mapFree = true) →
    v.Mirrors (v.copyStToM hp h).heap H.length (v.copyStToM hp h).val
  | _, .prim _, _ => by rw [SVal.copyStToM_prim]; rfl
  | _, .struct fs, h => by
    rw [SVal.copyStToM_struct]
    simp only [SVal.Mirrors]
    refine ⟨Grown.alloc_id_ge _, ?_⟩
    rw [Grown.alloc_get]
    exact SFields.Mirrors.wk (Heap.keeps_alloc _ _) fs _ (SFields.mirrors_copyStToM hp fs _)
  | _, .array a _ _, h => by
    rw [SVal.copyStToM_array]
    simp only [SVal.Mirrors]
    refine ⟨Grown.alloc_id_ge _, ?_⟩
    rw [Grown.alloc_get, MObj.elems_wk, MObj.elems_dyn]
    exact SVec.Mirrors.wk (Heap.keeps_alloc _ _) a _ (SVec.mirrors_copyStToM hp a _)
  | _, .fixed a, h => by
    rw [SVal.copyStToM_fixed]
    simp only [SVal.Mirrors]
    refine ⟨Grown.alloc_id_ge _, ?_⟩
    rw [Grown.alloc_get, MObj.elems_wk, MObj.elems_fixed]
    exact SVec.Mirrors.wk (Heap.keeps_alloc _ _) a _ (SVec.mirrors_copyStToM hp a _)
  | _, .map _ _, h => by simp only [Ty.mapFree, Bool.false_eq_true] at h

theorem SFields.mirrors_copyStToM {H : HTy} (hp : Heap H) :
    {fs : List (Name × Ty)} → (x : SFields fs) → (h : ∀ fT ∈ fs, fT.2.mapFree = true) →
    x.Mirrors (x.copyStToM hp h).heap H.length (x.copyStToM hp h).val
  | _, .nil, _ => by simp only [SFields.Mirrors]
  | _, .cons v rest, h => by
    rw [SFields.copyStToM_cons]
    simp only [SFields.Mirrors]
    exact ⟨SVal.Mirrors.wk (SFields.keeps_copyStToM rest _ _) v _ (SVal.mirrors_copyStToM hp v _),
      SFields.Mirrors.mono (v.copyStToM hp _).ext.length_le rest _
        (SFields.mirrors_copyStToM _ rest _)⟩

theorem SVec.mirrors_copyStToM {H : HTy} (hp : Heap H) :
    {E : Ty} → {k : Nat} → (x : SVec E k) → (h : E.mapFree = true) →
    x.Mirrors (x.copyStToM hp h).heap H.length (x.copyStToM hp h).val.1
  | _, _, .nil, _ => by rw [SVec.copyStToM_nil]; simp only [SVec.Mirrors]
  | _, _, .cons v rest, h => by
    rw [SVec.copyStToM_cons]
    simp only [SVec.Mirrors]
    exact ⟨_, _, rfl, SVal.Mirrors.wk (SVec.keeps_copyStToM rest _ _) v _ (SVal.mirrors_copyStToM hp v _),
      SVec.Mirrors.mono (v.copyStToM hp _).ext.length_le rest _
        (SVec.mirrors_copyStToM _ rest _)⟩
end

/-! ### Reading a mirror -/

/-- A mirrored word is the word. -/
theorem SVal.Mirrors.prim {H : HTy} {hp : Heap H} {n : Nat} {p : PrimTy} :
    (v : SVal (.prim p)) → (w : MVal H (.prim p)) → v.Mirrors hp n w → (w : p.Denote) = v.view
  | .prim _, _, h => h

/-- A mirrored object is past the heap the mirror is past. -/
theorem SVal.Mirrors.id_ge {H : HTy} {hp : Heap H} {n : Nat} {R : RefTy} :
    (v : SVal (.ref R)) → (r : MVal H (.ref R)) → v.Mirrors hp n r → n ≤ (r : HRef H R).id
  | .struct _, _, h => by simp only [SVal.Mirrors] at h; exact h.1
  | .array _ _ _, _, h => by simp only [SVal.Mirrors] at h; exact h.1
  | .fixed _, _, h => by simp only [SVal.Mirrors] at h; exact h.1
  | .map _ _, _, h => by simp only [SVal.Mirrors] at h

/-- A member of a mirrored struct mirrors the member. -/
theorem SFields.Mirrors.get {H : HTy} {hp : Heap H} {n : Nat} {f : Name} :
    {fs : List (Name × Ty)} → (x : SFields fs) → (o : MFields H fs) → x.Mirrors hp n o →
    {T : Ty} → (hf : lookupBy f fs = some T) → (x.get hf).Mirrors hp n (MFields.get fs o hf)
  | _, .nil, _, _, _, hf => absurd hf (by simp only [lookupBy, reduceCtorEq, not_false_eq_true])
  | _, @SFields.cons f' T' _ v rest, o, h, T, hf => by
    simp only [SFields.Mirrors] at h
    rw [SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e hf
      subst hT
      simp only [MFields.get, e, dite_true]
      exact h.1
    · simp only [MFields.get, e, dite_false]
      exact SFields.Mirrors.get rest o.2 h.2 _

/-- A mirrored vector: the elements, as many, each mirrored. -/
theorem SVec.Mirrors.getElem {H : HTy} {hp : Heap H} {n : Nat} :
    {E : Ty} → {k : Nat} → (x : SVec E k) → (l : List (MVal H E)) → x.Mirrors hp n l →
    ∀ i : Nat, (x.toList[i]? = none ∧ l[i]? = none) ∨
      ∃ v w, x.toList[i]? = some v ∧ l[i]? = some w ∧ v.Mirrors hp n w
  | _, _, .nil, l, h, i => by
    simp only [SVec.Mirrors] at h
    subst h
    exact .inl ⟨by rw [SVec.toList_nil]; rfl, rfl⟩
  | _, _, .cons v rest, l, h, i => by
    simp only [SVec.Mirrors] at h
    obtain ⟨w, ws, rfl, h1, h2⟩ := h
    rw [SVec.toList_cons]
    cases i with
    | zero => exact .inr ⟨v, w, rfl, rfl, h1⟩
    | succ i =>
      simp only [List.getElem?_cons_succ]
      exact SVec.Mirrors.getElem rest ws h2 i

end Solidity
