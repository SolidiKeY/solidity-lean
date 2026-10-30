import Solidity.Source.Eval
import Solidity.Source.Hoare

/-!
# Well-typed run-time states (lane V04b, preservation)

Most of a run-time state is typed by construction: a value of type `τ` is a
`Val D τ` (ranges, enum bounds, byte lengths inside), locals are
`Locals D Γ`, storage and transient storage are `Storage D L` over the
logical layout (`Env.cellTy`), and every memory object carries its type
(`Σ τ, Data D τ`). What is not intrinsic is **where references point**:

- a `memory` reference of type `τ` must name an object of type `τ`
  (`HeapTy`, the heap's typing), up to `bytes`/`string` (`STy.memShape`:
  `bytes(s)` keeps the pointer of a `string memory s`);
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

Reads and writes of locals and memory locations keep it too, halts
included (`writeLoc_local_pres`, `writeLoc_mem_pres`, `writeLoc_memByte_pres`,
`memSet_pres`, `readLoc_*_pres`, `memElem_pres`); a written value must agree,
and a value read agrees. These are preservation only: `HeapOK` says where
references point, not that a top-level object of a memory reference type is
an aggregate rather than a `Data.val`, so progress for memory accesses needs
that shape invariant as well (`SoundnessExamples.ptrHeap_byte_stuck`).
`HeapShaped` states it (`Data.Top`: a top-level object is a bare value only
at a type without a location); allocation and writes keep it, and with it a
byte write at a `bytes`/`string` address is never `stuck`
(`writeLoc_memByte_ok`), nor is an element or member write of the
element's or member's type (`memSet_ok`, `writeLoc_mem_ok`), nor a byte
read (`heapBytes_ok`, `readLoc_memByte_ok`).
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

/-- A memory object's shape: `string` and `bytes` objects of one location
are interchangeable (`bytes(s)` and `string(b)` keep the pointer). -/
def STy.memShape : STy → STy
  | .string l => .bytes l
  | τ => τ

/-- **A value's reference agrees with the heap typing and the layout.** -/
def Val.RefOK (E : Env) (H : HeapTy) : {τ : STy} → Val E.layout τ → Prop
  | τ, .memRef _ a => ∃ σ, H a = some σ ∧ σ.memShape = τ.memShape
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
  cases v with
  | memRef _ a => obtain ⟨σ, h1, h2⟩ := h; exact ⟨σ, hle _ _ h1, h2⟩
  | _ => first | trivial | exact h

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
  refine Hoare.dite' (fun h => Hoare.pure' fun y hy => ⟨hy.1, τ, hy.2, rfl⟩) (fun h => absurd hm h)

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


/-! ## Writes and reads of locations keep it -/

/-- **`heapObj`, preservation**, with any halt condition that holds at a
dangling address: the object read has the address's type and agrees; the
state is unchanged, so any `P` stronger than `EMOK` is kept. -/
theorem heapObj_gen {H : HeapTy} {P : EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    (hP : ∀ y, P y → EMOK E H y)
    (hX : ∀ y, P y → y.2.heap.get a = none → X (.stuck "dangling memory reference") y) :
    Hoare P (heapObj a : EM E Γ (Σ σ, Data E.layout σ))
      (fun x y => P y ∧ y.2.heap.ty a = some x.1 ∧ DataOK E y.2.heap.ty x.2) X := by
  unfold heapObj
  refine Hoare.bind (Hoare.st' (Q := fun s y => y.2 = s ∧ P y) fun y hy => ⟨rfl, hy⟩) fun s => ?_
  split
  · rename_i x hg
    refine Hoare.pure' fun y ⟨hs, hp⟩ => ?_
    subst hs
    refine ⟨hp, ?_, (hP y hp).1.heap a x hg⟩
    simp only [Heap.ty, Heap.get] at hg ⊢
    rw [hg]
    rfl
  · rename_i hg
    exact Hoare.halt' fun y ⟨hs, hp⟩ => by subst hs; exact hX y hp hg

/-- **`heapObj`, preservation**: `heapObj_gen` with `EMOK` on halts. -/
theorem heapObj_pres {H : HeapTy} {P : EMState E Γ → Prop} (hP : ∀ y, P y → EMOK E H y) (a : Nat) :
    Hoare P (heapObj a : EM E Γ (Σ σ, Data E.layout σ))
      (fun x y => P y ∧ y.2.heap.ty a = some x.1 ∧ DataOK E y.2.heap.ty x.2) (fun _ y => EMOK E H y) :=
  heapObj_gen hP fun y hy _ => hP y hy

/-- **`heapPut`, preservation**: halts included. -/
theorem heapPut_pres {H : HeapTy} (a : Nat) (x : Σ τ, Data E.layout τ) :
    Hoare (fun y => EMOK E H y ∧ DataOK E y.2.heap.ty x.2) (heapPut a x : EM E Γ Unit)
      (fun _ y => EMOK E H y) (fun _ y => EMOK E H y) :=
  Hoare.conseq (heapPut_ok a x) (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.1)

/-- Replacing a field by agreeing contents keeps the fields agreeing. -/
theorem DataListOK.setNth {H : HeapTy} : {τs : List STy} → (fs : DataList E.layout τs) → (i : Nat) →
    {τ : STy} → (y : Data E.layout τ) → {fs' : DataList E.layout τs} → DataListOK E H fs →
    DataOK E H y → fs.setNth i y = .ok fs' → DataListOK E H fs'
  | _, .nil, _, _, _, _, _, _, h => by simp only [DataList.setNth, stuck] at h; cases h
  | _, .cons (τ := σ) x r, 0, τ, y, _, hf, hy, h => by
    cases hf with
    | cons hx hr =>
      by_cases e : τ = σ
      · subst e
        simp only [DataList.setNth, dite_true] at h
        cases h
        exact .cons hy hr
      · simp only [DataList.setNth, e, dite_false, stuck] at h
        cases h
  | _, .cons x r, i + 1, _, y, _, hf, hy, h => by
    cases hf with
    | cons hx hr =>
      simp only [DataList.setNth] at h
      cases hr' : r.setNth i y with
      | error e => rw [hr'] at h; cases h
      | ok r' =>
        rw [hr'] at h
        cases h
        exact .cons hx (DataListOK.setNth r i y hr hy hr')

/-- **`memSet`, preservation**: storing an agreeing value as an element or
member keeps the state well typed (whether or not the write succeeds). -/
theorem memSet_pres {H : HeapTy} (a i : Nat) {τ : STy} (v : Val E.layout τ) :
    Hoare (fun y => EMOK E H y ∧ v.RefOK E y.2.heap.ty) (memSet a i v : EM E Γ Unit)
      (fun _ y => EMOK E H y) (fun _ y => EMOK E H y) := by
  unfold memSet
  refine Hoare.bind (heapObj_pres (fun _ h => h.1) a) fun ⟨σ, d⟩ => ?_
  cases d with
  | array len hl xs =>
    refine Hoare.dite' (fun h => Hoare.dite' (fun e => ?_) (fun _ => Hoare.halt' fun y hy => hy.1.1))
      (fun _ => Hoare.lift' fun y hy => hy.1.1)
    subst e
    refine Hoare.conseq (heapPut_pres a _) (fun y ⟨⟨hok, hv⟩, _, hd⟩ => ⟨hok, ?_⟩)
      (fun _ _ h => h) (fun _ _ h => h)
    cases hd with
    | array hxs =>
      refine .array fun j => ?_
      by_cases hj : j.val = i
      · simp only [hj, if_true]; exact .val hv
      · simp only [hj, if_false]; exact hxs j
  | @struct l d fs =>
    refine Hoare.bind (Hoare.lift' (Q := fun fs' y =>
      EMOK E H y ∧ DataOK E y.2.heap.ty (Data.struct (l := l) (d := d) fs'))
      fun y ⟨⟨hok, hv⟩, _, hd⟩ => ?_) fun fs' => heapPut_pres a ⟨.struct l d, .struct fs'⟩
    cases hd with
    | struct hfs =>
      cases hr : fs.setNth i (Data.val v) with
      | error e => exact hok
      | ok fs' => exact ⟨hok, .struct (hfs.setNth fs i _ (.val hv) hr)⟩
  | _ => exact Hoare.halt' fun y hy => hy.1.1

/-- **`writeLoc` to memory, preservation**: an element or member write of
an agreeing value keeps the state well typed. -/
theorem writeLoc_mem_pres {H : HeapTy} (F : Fr) (n a i : Nat) {τ : STy} (v : Val E.layout τ) :
    Hoare (fun y => EMOK E H y ∧ v.RefOK E y.2.heap.ty) (writeLoc F n (.mem a i) v : EM E Γ Unit)
      (fun _ y => EMOK E H y) (fun _ y => EMOK E H y) :=
  memSet_pres a i v

/-- **`writeLoc` to a memory byte, preservation**: a byte write into a
`bytes` or `string` keeps the state well typed. -/
theorem writeLoc_memByte_pres {H : HeapTy} (F : Fr) (n a i : Nat) (v : Val E.layout (.fixedBytes 1 (by decide))) :
    Hoare (EMOK E H) (writeLoc F n (.memByte a i) v : EM E Γ Unit)
      (fun _ y => EMOK E H y) (fun _ y => EMOK E H y) := by
  simp only [writeLoc]
  refine Hoare.bind (heapObj_pres (fun _ h => h) a) fun ⟨σ, d⟩ => ?_
  cases d with
  | bytes bs =>
    exact Hoare.ite' (fun _ => Hoare.conseq (heapPut_pres a _) (fun y hy => ⟨hy.1, .bytes _⟩)
      (fun _ _ h => h) (fun _ _ h => h)) (fun _ => Hoare.lift' fun y hy => hy.1)
  | string bs =>
    exact Hoare.ite' (fun _ => Hoare.conseq (heapPut_pres a _) (fun y hy => ⟨hy.1, .string _⟩)
      (fun _ _ h => h) (fun _ _ h => h)) (fun _ => Hoare.lift' fun y hy => hy.1)
  | _ => exact Hoare.halt' fun y hy => hy.1

/-- **`writeLoc` to a local, preservation.** -/
theorem writeLoc_local_pres {H : HeapTy} (F : Fr) (n : Nat) {τ : STy} (i : Idx Γ τ) (v : Val E.layout τ) :
    Hoare (fun y => EMOK E H y ∧ v.RefOK E y.2.heap.ty) (writeLoc F n (.local i) v : EM E Γ Unit)
      (fun _ y => EMOK E H y) (fun _ y => EMOK E H y) := by
  simp only [writeLoc]
  refine Hoare.bind (Hoare.locals' (Q := fun l y => y.1 = l ∧ EMOK E H y ∧ v.RefOK E y.2.heap.ty)
    fun y hy => ⟨rfl, hy⟩) fun l => Hoare.setLocals' ?_
  intro ⟨l', s⟩ ⟨hl, ⟨hs, hlo⟩, hv⟩
  subst hl
  exact ⟨hs, LocalsOK.set _ i hlo hv⟩

/-- A field read from agreeing fields agrees. -/
theorem DataListOK.nth {H : HeapTy} : {τs : List STy} → (fs : DataList E.layout τs) → DataListOK E H fs →
    (i : Nat) → (τ : STy) → {x : Data E.layout τ} → fs.nth i τ = .ok x → DataOK E H x
  | _, .nil, _, _, _, _, h => by simp only [DataList.nth, stuck] at h; cases h
  | _, .cons (τ := σ) y r, hf, 0, τ, _, h => by
    cases hf with
    | cons hy _ =>
      by_cases e : σ = τ
      · subst e
        simp only [DataList.nth, dite_true] at h
        cases h
        exact hy
      · simp only [DataList.nth, e, dite_false, stuck] at h
        cases h
  | _, .cons y r, hf, i + 1, τ, _, h => by
    cases hf with
    | cons _ hr => exact DataListOK.nth r hr i τ (by simpa only [DataList.nth] using h)

/-- An element read as a value agrees. -/
theorem asVal_ok {H : HeapTy} {τ : STy} {x : Data E.layout τ} (hx : DataOK E H x) {v : Val E.layout τ}
    (h : x.asVal = .ok v) : v.RefOK E H := by
  cases hx with
  | val hv => simp only [Data.asVal, pure, Except.pure, Except.ok.injEq] at h; subst h; exact hv
  | _ => simp only [Data.asVal, stuck] at h; cases h

/-- **`memElem`, preservation**: the element or member read agrees. -/
theorem memElem_pres {H : HeapTy} (a i : Nat) (τ : STy) :
    Hoare (EMOK E H) (memElem a i τ : EM E Γ (Val E.layout τ))
      (fun v y => EMOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => EMOK E H y) := by
  unfold memElem
  refine Hoare.bind (heapObj_pres (fun _ h => h) a) fun ⟨σ, d⟩ => ?_
  cases d with
  | array len hl xs =>
    refine Hoare.dite' (fun h => ?_) (fun _ => Hoare.lift' fun y hy => hy.1)
    refine Hoare.dite' (fun e => Hoare.lift' fun y ⟨hok, _, hd⟩ => ?_) (fun _ => Hoare.halt' fun y hy => hy.1)
    subst e
    cases hd with
    | array hxs =>
      split
      · rename_i v hv; exact ⟨hok, asVal_ok (hxs ⟨i, h⟩) hv⟩
      · exact hok
  | struct fs =>
    refine Hoare.bind (Hoare.lift' (Q := fun x y => EMOK E H y ∧ DataOK E y.2.heap.ty x)
      fun y ⟨hok, _, hd⟩ => ?_) fun x => Hoare.lift' fun y ⟨hok, hx⟩ => ?_
    · cases hd with
      | struct hfs =>
        cases hr : fs.nth i τ with
        | error e => exact hok
        | ok x => exact ⟨hok, hfs.nth fs i τ hr⟩
    · split
      · rename_i v hv; exact ⟨hok, asVal_ok hx hv⟩
      · exact hok
  | _ => exact Hoare.halt' fun y hy => hy.1


/-- **`readLoc` of a local, preservation**: the value read agrees. -/
theorem readLoc_local_pres {H : HeapTy} (F : Fr) {τ : STy} (i : Idx Γ τ) :
    Hoare (EMOK E H) (readLoc F (.local i) : EM E Γ (Val E.layout τ))
      (fun v y => EMOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => EMOK E H y) := by
  simp only [readLoc]
  refine Hoare.bind (Hoare.locals' (Q := fun l y => y.1 = l ∧ EMOK E H y) fun y hy => ⟨rfl, hy⟩)
    fun l => Hoare.pure' fun y ⟨hl, hok⟩ => ⟨hok, ?_⟩
  subst hl
  exact LocalsOK.get _ i hok.2

/-- **`readLoc` of memory, preservation**: an element or member read agrees. -/
theorem readLoc_mem_pres {H : HeapTy} (F : Fr) (a i : Nat) {τ : STy} :
    Hoare (EMOK E H) (readLoc F (.mem a i) : EM E Γ (Val E.layout τ))
      (fun v y => EMOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => EMOK E H y) :=
  memElem_pres a i τ

/-- **`readLoc` of a memory byte, preservation**: the state is unchanged. -/
theorem readLoc_memByte_pres {H : HeapTy} (F : Fr) (a i : Nat) :
    Hoare (EMOK E H) (readLoc F (.memByte a i) : EM E Γ (Val E.layout (.fixedBytes 1 (by decide))))
      (fun _ y => EMOK E H y) (fun _ y => EMOK E H y) := by
  simp only [readLoc]
  refine Hoare.bind (Q := fun _ y => EMOK E H y) (R := fun _ y => EMOK E H y) ?_ fun bs => ?_
  · unfold heapBytes
    refine Hoare.bind (heapObj_pres (fun _ h => h) a) fun ⟨σ, d⟩ => ?_
    cases d with
    | bytes bs => exact Hoare.pure' fun y hy => hy.1
    | string bs => exact Hoare.pure' fun y hy => hy.1
    | _ => exact Hoare.halt' fun y hy => hy.1
  · split
    · exact Hoare.pure' fun y hy => hy
    · exact Hoare.lift' fun y hy => hy


/-! ## Object shapes (for progress of memory accesses) -/

/-- **A top-level memory object has its aggregate shape**: it is a
`Data.val` only at a type without a location (never a bare pointer). (`HeapOK` does not
say this; `SoundnessExamples.ptrHeap_byte_stuck`.) -/
def Data.Top {τ : STy} : Data E.layout τ → Prop
  | .val _ => τ.loc? = none
  | _ => True

/-- Every object of the heap has its shape. -/
def HeapShaped (h : Heap E.layout) : Prop := ∀ a x, h.get a = some x → Data.Top x.2

/-- The empty heap is shaped. -/
theorem HeapShaped.empty : HeapShaped (Heap.empty : Heap E.layout) := fun _ _ h => by cases h

/-- **Allocation keeps a heap shaped**, given a shaped object. -/
theorem HeapShaped.alloc {h : Heap E.layout} (hh : HeapShaped h) {x : Σ τ, Data E.layout τ}
    (hx : Data.Top x.2) : HeapShaped (h.alloc x).1 := by
  intro a y hy
  by_cases e : a = h.next
  · subst e
    simp only [Heap.get, Heap.alloc, if_true, Option.some.injEq] at hy
    subst hy
    exact hx
  · have hy' : h.get a = some y := by simp only [Heap.get, Heap.alloc, e, if_false] at hy; exact hy
    exact hh a y hy'

/-- **A write keeps a heap shaped**, given a shaped object. -/
theorem HeapShaped.write {h : Heap E.layout} (hh : HeapShaped h) {a : Nat} {τ : STy} {x : Data E.layout τ}
    (hty : h.ty a = some τ) (hx : Data.Top x) : HeapShaped (h.write a x hty) := by
  intro b y hy
  by_cases e : b = a
  · subst e
    rw [Heap.write_get] at hy
    cases hy
    exact hx
  · rw [Heap.write_other h e] at hy
    exact hh b y hy

/-- **`heapPut`, progress and preservation of shapes**: a write at the
address's own type, of agreeing and shaped contents, succeeds and keeps the
state well typed and shaped. -/
theorem heapPut_shaped {H : HeapTy} (a : Nat) (x : Σ τ, Data E.layout τ) :
    Hoare (fun y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧ y.2.heap.ty a = some x.1 ∧
        DataOK E y.2.heap.ty x.2 ∧ Data.Top x.2)
      (heapPut a x : EM E Γ Unit) (fun _ y => EMOK E H y ∧ HeapShaped y.2.heap)
      (fun _ _ => False) := by
  unfold heapPut
  refine Hoare.bind (Hoare.st' (Q := fun s y => y.2 = s ∧ (EMOK E H y ∧ HeapShaped y.2.heap) ∧
    y.2.heap.ty a = some x.1 ∧ DataOK E y.2.heap.ty x.2 ∧ Data.Top x.2)
    fun y hy => ⟨rfl, hy⟩) fun s => ?_
  refine Hoare.dite' (fun h => Hoare.setSt' ?_) (fun h => Hoare.of_false ?_)
  · intro ⟨l, s'⟩ ⟨hs, ⟨⟨⟨hh, hle⟩, hl⟩, hsh⟩, _, hx, ht⟩
    subst hs
    have hteq : (s'.heap.write a x.2 h).ty = s'.heap.ty := funext fun b => Heap.write_ty s'.heap a b x.2 h
    refine ⟨⟨⟨hh.write h hx, ?_⟩, ?_⟩, hsh.write h ht⟩
    · show H.Le (s'.heap.write a x.2 h).ty
      rw [hteq]; exact hle
    · show LocalsOK E (s'.heap.write a x.2 h).ty l
      rw [hteq]; exact hl
  · intro y ⟨hs, _, hty, _⟩
    subst hs
    exact h hty

/-- **`heapObj` in a shaped heap**: as `heapObj_gen`, and the object read
has its shape. -/
theorem heapObj_top {H : HeapTy} {P : EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    (hP : ∀ y, P y → EMOK E H y ∧ HeapShaped y.2.heap)
    (hX : ∀ y, P y → y.2.heap.get a = none → X (.stuck "dangling memory reference") y) :
    Hoare P (heapObj a : EM E Γ (Σ σ, Data E.layout σ))
      (fun x y => P y ∧ y.2.heap.ty a = some x.1 ∧ DataOK E y.2.heap.ty x.2 ∧ Data.Top x.2) X := by
  unfold heapObj
  refine Hoare.bind (Hoare.st' (Q := fun s y => y.2 = s ∧ P y) fun y hy => ⟨rfl, hy⟩) fun s => ?_
  split
  · rename_i x hg
    refine Hoare.pure' fun y ⟨hs, hp⟩ => ?_
    subst hs
    refine ⟨hp, ?_, (hP y hp).1.1.heap a x hg, (hP y hp).2 a x hg⟩
    simp only [Heap.ty, Heap.get] at hg ⊢
    rw [hg]
    rfl
  · rename_i hg
    exact Hoare.halt' fun y ⟨hs, hp⟩ => by subst hs; exact hX y hp hg

/-- The memory shape of `bytes`: a `bytes` or a `string`. -/
theorem STy.memShape_bytes {σ : STy} {l : DataLoc} (h : σ.memShape = .bytes l) :
    σ = .bytes l ∨ σ = .string l := by
  cases σ <;> simp only [STy.memShape, STy.bytes.injEq, reduceCtorEq] at h
  · exact .inl (by rw [h])
  · exact .inr (by rw [h])

/-- **`writeLoc` to a memory byte, progress and preservation**: at an
address the heap typing gives a `bytes` or `string` type, in a shaped
heap, a byte write is never `stuck` (the code writes or panics; the
statement excludes only `stuck`). A `memory` reference to a `bytes` or
`string` gives the precondition (`STy.memShape_bytes`, `Val.RefOK`, `StOK.le`). -/
theorem writeLoc_memByte_ok {H : HeapTy} (F : Fr) (n a i : Nat) (v : Val E.layout (.fixedBytes 1 (by decide))) :
    Hoare (fun y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧
        ∃ l, y.2.heap.ty a = some (.bytes l) ∨ y.2.heap.ty a = some (.string l))
      (writeLoc F n (.memByte a i) v : EM E Γ Unit)
      (fun _ y => EMOK E H y ∧ HeapShaped y.2.heap)
      (fun e y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧ NotStuck e) := by
  simp only [writeLoc]
  refine Hoare.bind (heapObj_top (a := a) (fun _ h => h.1) fun y ⟨_, l, hl⟩ hg => ?_) fun ⟨σ, d⟩ => ?_
  · exfalso
    simp only [Heap.ty, Heap.get] at hl hg
    rw [hg] at hl
    rcases hl with hl | hl <;> cases hl
  cases d with
  | bytes bs =>
    exact Hoare.ite' (fun _ => Hoare.conseq (heapPut_shaped a _)
      (fun y hy => ⟨hy.1.1, hy.2.1, .bytes _, trivial⟩) (fun _ _ h => h) (fun _ _ h => h.elim))
      (fun _ => Hoare.lift' fun y hy => ⟨hy.1.1, trivial⟩)
  | string bs =>
    exact Hoare.ite' (fun _ => Hoare.conseq (heapPut_shaped a _)
      (fun y hy => ⟨hy.1.1, hy.2.1, .string _, trivial⟩) (fun _ _ h => h) (fun _ _ h => h.elim))
      (fun _ => Hoare.lift' fun y hy => ⟨hy.1.1, trivial⟩)
  | val w =>
    refine Hoare.of_false fun y ⟨⟨_, l, hl⟩, hty, _, ht⟩ => ?_
    rw [hty] at hl
    rcases hl with hl | hl <;> cases hl <;> simp only [Data.Top, STy.loc?, reduceCtorEq] at ht
  | _ =>
    refine Hoare.of_false fun y ⟨⟨_, l, hl⟩, hty, _⟩ => ?_
    rw [hty] at hl
    rcases hl with hl | hl <;> cases hl


/-- Replacing a field at its own type succeeds. -/
theorem DataList.setNth_ok {τ : STy} (y : Data E.layout τ) : {τs : List STy} → (fs : DataList E.layout τs) →
    (i : Nat) → τs[i]? = some τ → ∃ fs', fs.setNth i y = .ok fs'
  | _, .nil, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | _, .cons (τ := σ) x r, 0, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨_, by simp only [DataList.setNth, dite_true]; rfl⟩
  | _, .cons x r, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨r', hr⟩ := DataList.setNth_ok y r i h
    exact ⟨_, by simp only [DataList.setNth, hr]; rfl⟩

/-- **`memSet`, progress and preservation**: storing an agreeing value as
an element of an array of its type, or as a member of its type, in a
shaped heap, is never `stuck` (the code writes, or panics out of bounds;
the statement excludes only `stuck`). -/
theorem memSet_ok {H : HeapTy} (a i : Nat) {τ : STy} (v : Val E.layout τ) :
    Hoare (fun y => ((EMOK E H y ∧ HeapShaped y.2.heap) ∧ v.RefOK E y.2.heap.ty) ∧
        ((∃ l k, y.2.heap.ty a = some (.array l τ k)) ∨
         (∃ l d, y.2.heap.ty a = some (.struct l d) ∧ (E.layout.fields d)[i]? = some τ)))
      (memSet a i v : EM E Γ Unit)
      (fun _ y => EMOK E H y ∧ HeapShaped y.2.heap)
      (fun e y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧ NotStuck e) := by
  unfold memSet
  refine Hoare.bind (heapObj_top (a := a) (fun _ h => h.1.1) fun y ⟨_, hc⟩ hg => ?_) fun ⟨σ, d⟩ => ?_
  · exfalso
    simp only [Heap.ty, Heap.get] at hc hg
    rw [hg] at hc
    rcases hc with ⟨_, _, hc⟩ | ⟨_, _, hc, _⟩ <;> cases hc
  cases d with
  | array len hl xs =>
    refine Hoare.dite' (fun h => Hoare.dite' (fun e => ?_) (fun e => Hoare.of_false ?_))
      (fun _ => Hoare.lift' fun y hy => ⟨hy.1.1.1, trivial⟩)
    · subst e
      refine Hoare.conseq (heapPut_shaped a _) (fun y ⟨⟨⟨hok, hv⟩, _⟩, hty, hd, _⟩ => ⟨hok, hty, ?_, trivial⟩)
        (fun _ _ h => h) (fun _ _ h => h.elim)
      cases hd with
      | array hxs =>
        refine .array fun j => ?_
        by_cases hj : j.val = i
        · simp only [hj, if_true]; exact .val hv
        · simp only [hj, if_false]; exact hxs j
    · intro y ⟨⟨_, hc⟩, hty, _⟩
      rcases hc with ⟨_, _, hc⟩ | ⟨_, _, hc, _⟩ <;> rw [hty] at hc <;> cases hc
      exact e rfl
  | @struct l d fs =>
    refine Hoare.bind (Hoare.lift' (Q := fun fs' y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧
        y.2.heap.ty a = some (.struct l d) ∧ DataOK E y.2.heap.ty (Data.struct (l := l) (d := d) fs'))
      fun y ⟨⟨⟨hok, hv⟩, hc⟩, hty, hd, _⟩ => ?_) fun fs' =>
        Hoare.conseq (heapPut_shaped a ⟨.struct l d, .struct fs'⟩)
          (fun y ⟨hok, hty, hd⟩ => ⟨hok, hty, hd, trivial⟩) (fun _ _ h => h) (fun _ _ h => h.elim)
    have hf : (E.layout.fields d)[i]? = some τ := by
      rcases hc with ⟨_, _, hc⟩ | ⟨_, _, hc, hf⟩ <;> rw [hty] at hc <;> cases hc
      exact hf
    obtain ⟨fs', hr⟩ := DataList.setNth_ok (Data.val v) fs i hf
    rw [hr]
    cases hd with
    | struct hfs => exact ⟨hok, hty, .struct (hfs.setNth fs i _ (.val hv) hr)⟩
  | val w =>
    refine Hoare.of_false fun y ⟨⟨_, hc⟩, hty, _, ht⟩ => ?_
    rcases hc with ⟨_, _, hc⟩ | ⟨_, _, hc, _⟩ <;> rw [hty] at hc <;> cases hc <;>
      simp only [Data.Top, STy.loc?, reduceCtorEq] at ht
  | _ =>
    refine Hoare.of_false fun y ⟨⟨_, hc⟩, hty, _⟩ => ?_
    rcases hc with ⟨_, _, hc⟩ | ⟨_, _, hc, _⟩ <;> rw [hty] at hc <;> cases hc


/-- **`writeLoc` to memory, progress and preservation** (`memSet_ok`). -/
theorem writeLoc_mem_ok {H : HeapTy} (F : Fr) (n a i : Nat) {τ : STy} (v : Val E.layout τ) :
    Hoare (fun y => ((EMOK E H y ∧ HeapShaped y.2.heap) ∧ v.RefOK E y.2.heap.ty) ∧
        ((∃ l k, y.2.heap.ty a = some (.array l τ k)) ∨
         (∃ l d, y.2.heap.ty a = some (.struct l d) ∧ (E.layout.fields d)[i]? = some τ)))
      (writeLoc F n (.mem a i) v : EM E Γ Unit)
      (fun _ y => EMOK E H y ∧ HeapShaped y.2.heap)
      (fun e y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧ NotStuck e) :=
  memSet_ok a i v


/-- The memory shape of an array is the array itself. -/
theorem STy.memShape_array {σ ρ : STy} {l : DataLoc} {k : Option Nat}
    (h : σ.memShape = .array l ρ k) : σ = .array l ρ k := by
  cases σ <;> simp only [STy.memShape, reduceCtorEq] at h
  exact h

/-- **`heapBytes`, progress**: at an address the heap typing gives a
`bytes` or `string` type, in a shaped heap, the read succeeds. -/
theorem heapBytes_ok {H : HeapTy} {P : EMState E Γ → Prop} (a : Nat)
    (hP : ∀ y, P y → (EMOK E H y ∧ HeapShaped y.2.heap) ∧
      ∃ l, y.2.heap.ty a = some (.bytes l) ∨ y.2.heap.ty a = some (.string l)) :
    Hoare P (heapBytes a : EM E Γ (List UInt8)) (fun _ y => P y) (fun _ _ => False) := by
  unfold heapBytes
  refine Hoare.bind (heapObj_top (a := a) (fun y h => (hP y h).1) fun y hy hg => ?_) fun ⟨σ, d⟩ => ?_
  · obtain ⟨_, l, hl⟩ := hP y hy
    simp only [Heap.ty, Heap.get] at hl hg
    rw [hg] at hl
    rcases hl with hl | hl <;> cases hl
  cases d with
  | bytes bs => exact Hoare.pure' fun y hy => hy.1
  | string bs => exact Hoare.pure' fun y hy => hy.1
  | val w =>
    refine Hoare.of_false fun y ⟨hp, hty, _, ht⟩ => ?_
    obtain ⟨_, l, hl⟩ := hP y hp
    rw [hty] at hl
    rcases hl with hl | hl <;> cases hl <;> simp only [Data.Top, STy.loc?, reduceCtorEq] at ht
  | _ =>
    refine Hoare.of_false fun y ⟨hp, hty, _⟩ => ?_
    obtain ⟨_, l, hl⟩ := hP y hp
    rw [hty] at hl
    rcases hl with hl | hl <;> cases hl

/-- **`readLoc` of a memory byte, progress and preservation**: at a
`bytes`/`string` address in a shaped heap, the read is never `stuck` (the
code reads or panics out of bounds; the statement excludes only `stuck`). -/
theorem readLoc_memByte_ok {H : HeapTy} (F : Fr) (a i : Nat) :
    Hoare (fun y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧
        ∃ l, y.2.heap.ty a = some (.bytes l) ∨ y.2.heap.ty a = some (.string l))
      (readLoc F (.memByte a i) : EM E Γ (Val E.layout (.fixedBytes 1 (by decide))))
      (fun _ y => EMOK E H y ∧ HeapShaped y.2.heap)
      (fun e y => (EMOK E H y ∧ HeapShaped y.2.heap) ∧ NotStuck e) := by
  simp only [readLoc]
  refine Hoare.bind (Hoare.conseq (heapBytes_ok a fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun _ _ h => h.elim)) fun bs => ?_
  split
  · exact Hoare.pure' fun y hy => hy.1
  · exact Hoare.lift' fun y hy => ⟨hy.1, trivial⟩

end

end Solidity.Source
