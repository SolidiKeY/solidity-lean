import Solidity.Source.Hoare

/-!
# Well-typed run-time states (lane V04b, preservation)

Most of a run-time state is typed by construction: a value of type `τ` is a
`Val D τ` (ranges, enum bounds, byte lengths inside), locals are
`Locals D Γ`, storage and transient storage are `Storage D L` over the
logical layout (`Env.cellTy`), and every memory object carries its type
(`Σ τ, Data D τ`). What is not intrinsic is **where references point**:

- a `memory` reference of type `τ` must name an object of type `τ`
  (`HeapTy`, the heap's typing);
- a `storage` reference of type `τ` must name a path of declared type `τ`
  (`Env.pathTy`);
- no value is a `calldata` reference (the semantics creates none: calldata
  references are a gap, `docs/feature-work/source-soundness.md`).

`Val.RefOK`, `DataOK`, `RValOK`, `LocalsOK` state this for values, memory
contents, run-time values and locals against a heap typing `H`; all are
monotone in `H` (`HeapTy.Le`). `HeapOK` asks it of every object in a heap,
against the heap's own typing.

The machine's memory operations keep it (`alloc_ok`, `heapPut_ok`) and
return values that satisfy it (`allocRef_ok`, `heapAt_ok`), and the typed
reads succeed on it (`heapObj_ok`, `heapAt_ok`; `heapAt` has no caller in
the interpreter): a read at the type the reference was made for is never
`stuck`.
-/

namespace Solidity.Source

open EM

variable {E : Env}

/-! ## Heap typings -/

/-- A heap typing: the type of the object at each address. -/
abbrev HeapTy := Nat → Option STy

/-- `H'` extends `H`: every typed address keeps its type. -/
def HeapTy.Le (H H' : HeapTy) : Prop := ∀ a τ, H a = some τ → H' a = some τ

theorem HeapTy.Le.refl (H : HeapTy) : H.Le H := fun _ _ h => h

theorem HeapTy.Le.trans {H₁ H₂ H₃ : HeapTy} (h₁ : H₁.Le H₂) (h₂ : H₂.Le H₃) : H₁.Le H₃ :=
  fun a τ h => h₂ a τ (h₁ a τ h)

/-! ## References that agree with the state -/

/-- **A value's reference agrees with the heap typing and the layout.** -/
def Val.RefOK (E : Env) (H : HeapTy) : {τ : STy} → Val E.layout τ → Prop
  | τ, .memRef _ a => H a = some τ
  | τ, .storRef _ p => E.pathTy p = some τ
  | _, .cdRef _ _ => False
  | _, _ => True

/-- A value of a type without a location is no reference. -/
theorem Val.refOK_of_loc {H : HeapTy} {τ : STy} (hτ : τ.loc? = none) (v : Val E.layout τ) :
    v.RefOK E H := by
  cases v with
  | memRef h _ => rw [hτ] at h; cases h
  | storRef h _ => rw [hτ] at h; cases h
  | cdRef h _ => rw [hτ] at h; cases h
  | _ => trivial

theorem Val.RefOK.mono {H H' : HeapTy} (hle : H.Le H') {τ : STy} {v : Val E.layout τ}
    (h : v.RefOK E H) : v.RefOK E H' := by
  cases v <;> first | trivial | exact h | exact hle _ _ h

mutual

/-- **Memory contents whose references agree**. -/
inductive DataOK (E : Env) (H : HeapTy) : {τ : STy} → Data E.layout τ → Prop where
  | val {τ : STy} {v : Val E.layout τ} : v.RefOK E H → DataOK E H (.val v)
  | bytes {l : DataLoc} (bs : List UInt8) : DataOK E H (Data.bytes (l := l) bs)
  | string {l : DataLoc} (bs : List UInt8) : DataOK E H (Data.string (l := l) bs)
  | array {l : DataLoc} {τ : STy} {n : Option Nat} {len : Nat} {hl : ∀ m, n = some m → m = len}
      {xs : Fin len → Data E.layout τ} : (∀ i, DataOK E H (xs i)) →
      DataOK E H (Data.array (l := l) len hl xs)
  | struct {l : DataLoc} {d : DeclName} {fs : DataList E.layout (E.layout.fields d)} :
      DataListOK E H fs → DataOK E H (Data.struct (l := l) fs)
  | mapping {k v : STy} {m : KeyOf E.layout k → Data E.layout v} : (∀ key, DataOK E H (m key)) →
      DataOK E H (Data.mapping m)

/-- Fields whose references agree. -/
inductive DataListOK (E : Env) (H : HeapTy) : {τs : List STy} → DataList E.layout τs → Prop where
  | nil : DataListOK E H .nil
  | cons {τ : STy} {τs : List STy} {x : Data E.layout τ} {xs : DataList E.layout τs} :
      DataOK E H x → DataListOK E H xs → DataListOK E H (.cons x xs)

end

mutual

theorem DataOK.mono {H H' : HeapTy} (hle : H.Le H') {τ : STy} {x : Data E.layout τ} :
    DataOK E H x → DataOK E H' x
  | .val h => .val (h.mono hle)
  | .bytes bs => .bytes bs
  | .string bs => .string bs
  | .array h => .array fun i => (h i).mono hle
  | .struct h => .struct (h.mono hle)
  | .mapping h => .mapping fun k => (h k).mono hle

theorem DataListOK.mono {H H' : HeapTy} (hle : H.Le H') {τs : List STy} {xs : DataList E.layout τs} :
    DataListOK E H xs → DataListOK E H' xs
  | .nil => .nil
  | .cons h hs => .cons (h.mono hle) (hs.mono hle)

end

mutual

/-- **Run-time values whose references agree**. -/
def RValOK (E : Env) (H : HeapTy) : {τ : STy} → RVal E.layout τ → Prop
  | _, .val v => v.RefOK E H
  | _, .tuple vs => RValsOK E H vs
  | _, _ => True

def RValsOK (E : Env) (H : HeapTy) : {τs : List STy} → RVals E.layout τs → Prop
  | _, .nil => True
  | _, .cons v vs => RValOK E H v ∧ RValsOK E H vs

end

mutual

theorem RValOK.mono {H H' : HeapTy} (hle : H.Le H') : {τ : STy} → (v : RVal E.layout τ) →
    RValOK E H v → RValOK E H' v
  | _, .val _, h => Val.RefOK.mono hle h
  | _, .tuple vs, h => RValsOK.mono hle vs h
  | _, .const _, _ => trivial
  | _, .strLit _, _ => trivial
  | _, .hex _ _, _ => trivial

theorem RValsOK.mono {H H' : HeapTy} (hle : H.Le H') : {τs : List STy} → (vs : RVals E.layout τs) →
    RValsOK E H vs → RValsOK E H' vs
  | _, .nil, _ => trivial
  | _, .cons v vs, h => And.intro (RValOK.mono hle v h.1) (RValsOK.mono hle vs h.2)

end

/-- **Locals whose references agree**. -/
def LocalsOK (E : Env) (H : HeapTy) : {Γ : RCtx} → Locals E.layout Γ → Prop
  | _, .nil => True
  | _, .cons v l => v.RefOK E H ∧ LocalsOK E H l

theorem LocalsOK.mono {H H' : HeapTy} (hle : H.Le H') : {Γ : RCtx} → (l : Locals E.layout Γ) →
    LocalsOK E H l → LocalsOK E H' l
  | _, .nil, _ => trivial
  | _, .cons _ l, h => And.intro (Val.RefOK.mono hle h.1) (LocalsOK.mono hle l h.2)

/-- Every local read from agreeing locals agrees. -/
theorem LocalsOK.get {H : HeapTy} : {Γ : RCtx} → {τ : STy} → (l : Locals E.layout Γ) → (i : Idx Γ τ) →
    LocalsOK E H l → (l.get i).RefOK E H
  | _, _, .cons _ _, .here, h => h.1
  | _, _, .cons _ r, .there i, h => LocalsOK.get r i h.2

/-- Writing an agreeing value keeps the locals agreeing. -/
theorem LocalsOK.set {H : HeapTy} : {Γ : RCtx} → {τ : STy} → (l : Locals E.layout Γ) → (i : Idx Γ τ) →
    {v : Val E.layout τ} → LocalsOK E H l → v.RefOK E H → LocalsOK E H (l.set i v)
  | _, _, .cons _ _, .here, _, h, hv => And.intro hv h.2
  | _, _, .cons _ r, .there i, _, h, hv => And.intro h.1 (LocalsOK.set r i h.2 hv)

/-! ## Heaps -/

/-- **A well-typed heap**: every object's references agree with the heap's
own typing. -/
def HeapOK (h : Heap E.layout) : Prop := ∀ a x, h.get a = some x → DataOK E h.ty x.2

/-- The empty heap is well typed. -/
theorem HeapOK.empty : HeapOK (Heap.empty : Heap E.layout) := fun _ _ h => by cases h

/-- Allocation extends the heap typing. -/
theorem Heap.alloc_le (h : Heap E.layout) (x : Σ τ, Data E.layout τ) : HeapTy.Le h.ty (h.alloc x).1.ty := by
  intro a τ ha
  have hne : a ≠ h.next := by
    intro e
    subst e
    simp only [Heap.ty, h.bounded _ (Nat.le_refl _), Option.map_none, reduceCtorEq] at ha
  simp only [Heap.ty, Heap.alloc, hne, if_false] at ha ⊢
  exact ha

/-- The allocated address has the object's type. -/
theorem Heap.alloc_ty (h : Heap E.layout) (x : Σ τ, Data E.layout τ) :
    (h.alloc x).1.ty (h.alloc x).2 = some x.1 := by
  simp only [Heap.ty, Heap.alloc, if_true, Option.map_some]

/-- **Allocation keeps a heap well typed**, given agreeing contents. -/
theorem HeapOK.alloc {h : Heap E.layout} (hh : HeapOK h) {x : Σ τ, Data E.layout τ}
    (hx : DataOK E h.ty x.2) : HeapOK (h.alloc x).1 := by
  intro a y hy
  by_cases e : a = h.next
  · subst e
    simp only [Heap.get, Heap.alloc, if_true, Option.some.injEq] at hy
    subst hy
    exact hx.mono (Heap.alloc_le h _)
  · have hy' : h.get a = some y := by simp only [Heap.get, Heap.alloc, e, if_false] at hy; exact hy
    exact (hh a y hy').mono (Heap.alloc_le h _)

/-- **A write at the object's type keeps a heap well typed**, given
agreeing contents. -/
theorem HeapOK.write {h : Heap E.layout} (hh : HeapOK h) {a : Nat} {τ : STy} {x : Data E.layout τ}
    (hty : h.ty a = some τ) (hx : DataOK E h.ty x) : HeapOK (h.write a x hty) := by
  have hteq : (h.write a x hty).ty = h.ty := funext fun b => Heap.write_ty h a b x hty
  intro b y hy
  rw [hteq]
  by_cases e : b = a
  · subst e
    rw [Heap.write_get] at hy
    cases hy
    exact hx
  · rw [Heap.write_other h e] at hy
    exact hh b y hy

/-! ## The state invariant -/

/-- **A well-typed machine state**, at least as typed as `H`: its heap is
well typed and extends `H`. -/
structure StOK (E : Env) (H : HeapTy) (s : St E) : Prop where
  heap : HeapOK s.heap
  le : H.Le s.heap.ty

theorem StOK.weaken {H H' : HeapTy} {s : St E} (h : StOK E H' s) (hle : H.Le H') : StOK E H s :=
  ⟨h.heap, hle.trans h.le⟩

/-- A well-typed interpreter state: the machine state and the locals. -/
def EMOK (E : Env) {Γ : RCtx} (H : HeapTy) (x : EMState E Γ) : Prop :=
  StOK E H x.2 ∧ LocalsOK E x.2.heap.ty x.1

/-! ## Memory operations keep it (preservation) -/

section
variable {Γ : RCtx}

/-- **`alloc`**: a well-typed state stays well typed, extended by the new
object's address. -/
theorem alloc_ok {H : HeapTy} {τ : STy} (x : Data E.layout τ) {X : Halt → EMState E Γ → Prop} :
    Hoare (fun y => EMOK E H y ∧ DataOK E y.2.heap.ty x) (alloc x : EM E Γ Nat)
      (fun a y => EMOK E H y ∧ y.2.heap.ty a = some τ) X := by
  intro ⟨l, s⟩ ⟨⟨⟨hh, hle⟩, hl⟩, hx⟩
  exact ⟨⟨⟨hh.alloc hx, hle.trans (Heap.alloc_le s.heap _)⟩, LocalsOK.mono (Heap.alloc_le s.heap _) l hl⟩,
    Heap.alloc_ty s.heap ⟨τ, x⟩⟩

/-- **`allocRef`**: the new reference agrees with the new heap (a
reference type in `memory`; otherwise the result is `stuck`, which a
well-typed caller never asks for). -/
theorem allocRef_ok {H : HeapTy} {τ : STy} (x : Data E.layout τ) (hm : τ.loc? = some .memory)
    {X : Halt → EMState E Γ → Prop} :
    Hoare (fun y => EMOK E H y ∧ DataOK E y.2.heap.ty x) (allocRef x : EM E Γ (Val E.layout τ))
      (fun v y => EMOK E H y ∧ v.RefOK E y.2.heap.ty) X := by
  refine Hoare.bind (alloc_ok x) fun a => ?_
  refine Hoare.dite' (fun h => Hoare.pure' fun y hy => ⟨hy.1, hy.2⟩) (fun h => absurd hm h)

/-- **`heapPut`**: a write of agreeing contents keeps the state well
typed; it is `stuck` only at an address whose object has another type. -/
theorem heapPut_ok {H : HeapTy} (a : Nat) (x : Σ τ, Data E.layout τ) :
    Hoare (fun y => EMOK E H y ∧ DataOK E y.2.heap.ty x.2) (heapPut a x : EM E Γ Unit)
      (fun _ y => EMOK E H y) (fun e y => EMOK E H y ∧ (NotStuck e ∨ y.2.heap.ty a ≠ some x.1)) := by
  unfold heapPut
  refine Hoare.bind (Hoare.st' (Q := fun s y => y.2 = s ∧ EMOK E H y ∧ DataOK E y.2.heap.ty x.2)
    fun y hy => ⟨rfl, hy⟩) fun s => ?_
  refine Hoare.dite' (fun h => Hoare.setSt' ?_) (fun h => Hoare.halt' ?_)
  · intro ⟨l, s'⟩ ⟨hs, ⟨⟨hh, hle⟩, hl⟩, hx⟩
    subst hs
    have hteq : (s'.heap.write a x.2 h).ty = s'.heap.ty := funext fun b => Heap.write_ty s'.heap a b x.2 h
    refine ⟨⟨hh.write h hx, ?_⟩, ?_⟩
    · show H.Le (s'.heap.write a x.2 h).ty
      rw [hteq]; exact hle
    · show LocalsOK E (s'.heap.write a x.2 h).ty l
      rw [hteq]; exact hl
  · intro y ⟨hs, hok, _⟩
    subst hs
    exact ⟨hok, .inr h⟩

/-- **`heapObj`**: the object at an address the typing knows, agreeing. -/
theorem heapObj_ok {H : HeapTy} (a : Nat) {τ : STy} :
    Hoare (fun y => EMOK E H y ∧ y.2.heap.ty a = some τ) (heapObj a : EM E Γ (Σ σ, Data E.layout σ))
      (fun x y => EMOK E H y ∧ x.1 = τ ∧ DataOK E y.2.heap.ty x.2) (fun _ _ => False) := by
  unfold heapObj
  refine Hoare.bind (Hoare.st' (Q := fun s y => y.2 = s ∧ EMOK E H y ∧ y.2.heap.ty a = some τ)
    fun y hy => ⟨rfl, hy⟩) fun s => ?_
  split
  · rename_i x hg
    refine Hoare.pure' fun y ⟨hs, hok, hty⟩ => ?_
    subst hs
    have hx1 : x.1 = τ := by
      simp only [Heap.ty, Heap.get] at hty hg
      rw [hg] at hty
      exact Option.some.inj hty
    exact ⟨hok, hx1, hok.1.heap a x hg⟩
  · rename_i hg
    refine Hoare.of_false fun y ⟨hs, _, hty⟩ => ?_
    subst hs
    simp only [Heap.ty, Heap.get] at hty hg
    rw [hg] at hty
    cases hty

/-- **`heapAt`, progress and preservation**: a read at the type the heap
typing gives is never `stuck` and returns agreeing contents. -/
theorem heapAt_ok {H : HeapTy} (a : Nat) (τ : STy) :
    Hoare (fun y => EMOK E H y ∧ y.2.heap.ty a = some τ) (heapAt a τ : EM E Γ (Data E.layout τ))
      (fun x y => EMOK E H y ∧ DataOK E y.2.heap.ty x) (fun _ _ => False) := by
  unfold heapAt
  refine Hoare.bind (heapObj_ok a) fun ⟨σ, x⟩ => ?_
  refine Hoare.dite' (fun h => ?_) (fun h => Hoare.of_false fun y hy => h hy.2.1)
  subst h
  exact Hoare.pure' fun y hy => ⟨hy.1, hy.2.2⟩

/-- **`storRef`**: a storage reference to a path of its type agrees. -/
theorem storRef_ok {P : EMState E Γ → Prop} {τ : STy} (p : SPath) (hs : τ.loc? = some .storage)
    (hp : E.pathTy p = some τ) {X : Halt → EMState E Γ → Prop} :
    Hoare P (storRef τ p : EM E Γ (Val E.layout τ)) (fun v y => P y ∧ ∀ H, v.RefOK E H) X := by
  unfold storRef
  rw [dif_pos hs]
  exact Hoare.pure' fun y hy => ⟨hy, fun _ => hp⟩

end

end Solidity.Source
