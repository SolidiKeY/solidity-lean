import Solidity.Theory.Typed.MemMirror

/-! Intrinsic threshold reading of the two selected H28 freshness clauses.
For `a[i] = x`, successful writes preserve the typing, even when x is a
reference. A storage copy allocates; its threshold therefore only grows.
-/
namespace Solidity.SolkeyAgreementH28

/-- An identity is beyond every allocated object in this actual heap typing. -/
def Fresh (H : HTy) (id : Nat) : Prop := H.length ≤ id

/-- The threshold is exact: no intrinsically typed object has this identity. -/
theorem fresh_iff_absent (H : HTy) (id : Nat) :
    Fresh H id ↔ ∀ R (r : HRef H R), r.id ≠ id := by
  constructor
  · intro hf R r he
    have hr := HRef.id_lt r
    change H.length ≤ id at hf
    omega
  · intro ha
    by_cases hi : H.length ≤ id
    · exact hi
    · have hit : id < H.length := Nat.lt_of_not_ge hi
      let r : HRef H H[id] := ⟨id, List.getElem?_eq_getElem hit⟩
      exact False.elim (ha H[id] r rfl)

/-- Successful typed writes preserve the entire object typing. -/
theorem write_typing {H : HTy} {T : Ty} {m n : Grown H (fun _ => Unit)}
    {a : MAddrT T} {v : MvT T} (h : m.writeT a v = some n) : n.H' = m.H' := by
  unfold Grown.writeT at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨ad, _, w, _, hp, _, rfl⟩ := h
  rfl

/-- `newFromWrite`: equality in both directions, for every identity. -/
theorem newFromWrite {H : HTy} {T : Ty} {m n : Grown H (fun _ => Unit)}
    {a : MAddrT T} {v : MvT T} (h : m.writeT a v = some n) (id : Nat) :
    Fresh n.H' id ↔ Fresh m.H' id := by
  rw [write_typing h]

/-- A finite spine of successful actual writes, at arbitrary slot types. -/
inductive Writes {H : HTy} : Grown H (fun _ => Unit) → Grown H (fun _ => Unit) → Prop
  | nil (m) : Writes m m
  | snoc {m n p} {T : Ty} (prev : Writes m n) (a : MAddrT T) (v : MvT T)
      (step : n.writeT a v = some p) : Writes m p

/-- Composition closes over any finite spine, not just one selected update. -/
theorem Writes.typing {H : HTy} {m n : Grown H (fun _ => Unit)} (h : Writes m n) :
    n.H' = m.H' := by
  induction h with
  | nil => rfl
  | snoc prev a v step ih => exact (write_typing step).trans ih

/-- Arbitrary write spines preserve precisely the same freshness threshold. -/
theorem Writes.fresh_iff {H : HTy} {m n : Grown H (fun _ => Unit)} (h : Writes m n)
    (id : Nat) : Fresh n.H' id ↔ Fresh m.H' id := by
  rw [h.typing]

/-- Preexisting and fresh identities stay separate across every write spine. -/
theorem Writes.separate {H : HTy} {m n : Grown H (fun _ => Unit)} (h : Writes m n)
    {R : RefTy} (r : HRef m.H' R) (id : Nat) (hf : Fresh m.H' id) :
    Fresh n.H' id ∧ r.id ≠ id := by
  refine ⟨(h.fresh_iff id).2 hf, ?_⟩
  have hr : r.id < m.H'.length := HRef.id_lt r
  change m.H'.length ≤ id at hf
  omega

/-- Allocation transports freshness backwards, including nested storage copies. -/
theorem newFromCopySt {H : HTy} (hp : Heap H) {T : Ty} (v : SVal T)
    (hm : T.mapFree = true) (id : Nat) :
    Fresh (v.copyStToM hp hm).H' id → Fresh H id := by
  exact Nat.le_trans (v.copyStToM hp hm).ext.length_le

/-- A reference copy supplies a new identity, apart from each original object. -/
theorem copy_witness {H : HTy} (hp : Heap H) {R S : RefTy} (v : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true) (old : HRef H S) :
    let g := v.copyStToM hp hm
    Fresh H g.val.id ∧ ¬ Fresh g.H' g.val.id ∧ (old.wk g.ext).id ≠ g.val.id := by
  have hf : H.length ≤ (v.copyStToM hp hm).val.id := SVal.copyStToM_id_ge hp v hm
  have hn := HRef.id_lt (v.copyStToM hp hm).val
  have ho := HRef.id_lt old
  refine ⟨hf, ?_, ?_⟩
  · exact Nat.not_le_of_lt hn
  · change old.id ≠ (v.copyStToM hp hm).val.id
    omega

/-- The tempting forward converse fails for every inhabited reference copy. -/
theorem copy_not_converse {H : HTy} (hp : Heap H) {R : RefTy} (v : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true) :
    ¬ (∀ id, Fresh H id → Fresh (v.copyStToM hp hm).H' id) := by
  intro h
  have hf := h (v.copyStToM hp hm).val.id (SVal.copyStToM_id_ge hp v hm)
  exact Nat.not_le_of_lt (HRef.id_lt (v.copyStToM hp hm).val) hf

/-- Actual copies and writes may be arbitrarily interleaved; no separation premise. -/
inductive Operations : {H K : HTy} → Heap H → Heap K → Prop
  | nil {H} (hp : Heap H) : Operations hp hp
  | write {H K} {hp : Heap H} {hq : Heap K} (prev : Operations hp hq)
      {T : Ty} (a : MAddr K T) (v : MVal K T) (hr : Heap K)
      (step : hq.writeAddr a v = some hr) : Operations hp hr
  | copy {H K} {hp : Heap H} {hq : Heap K} (prev : Operations hp hq)
      {T : Ty} (v : SVal T) (hm : T.mapFree = true) :
      Operations hp (v.copyStToM hq hm).heap

/-- Composition derives growth from actual constructors, for arbitrarily many copies. -/
theorem Operations.prefix {H K : HTy} {hp : Heap H} {hq : Heap K}
    (h : Operations hp hq) : H <+: K := by
  induction h with
  | nil => exact List.prefix_refl _
  | write prev a v hr step ih => exact ih
  | copy prev v hm ih => exact ih.trans (v.copyStToM _ hm).ext

/-- An arbitrary mixed sequence transports threshold certificates backwards. -/
theorem Operations.fresh_back {H K : HTy} {hp : Heap H} {hq : Heap K}
    (h : Operations hp hq) (id : Nat) : Fresh K id → Fresh H id :=
  Nat.le_trans h.prefix.length_le

/-- Old references retain identity and remain apart from every finally fresh id. -/
theorem Operations.separate {H K : HTy} {hp : Heap H} {hq : Heap K}
    (h : Operations hp hq) {R : RefTy} (r : HRef H R) (id : Nat) (hf : Fresh K id) :
    (r.wk h.prefix).id = r.id ∧ (r.wk h.prefix).id ≠ id := by
  refine ⟨rfl, ?_⟩
  change r.id ≠ id
  have hb : Fresh H id := h.fresh_back id hf
  have hr := HRef.id_lt r
  change H.length ≤ id at hb
  omega

/-- Copied roots retain separation through any later copy/write sequence.
For `b = copy(a); b[i] = x`, this talks about identities even after writes
change the copied contents; it does not assert that contents still mirror a. -/
theorem copy_then_witness {H K : HTy} (hp : Heap H) {R S : RefTy}
    (v : SVal (.ref R)) (hm : (Ty.ref R).mapFree = true) (old : HRef H S)
    {hq : Heap K} (suffix : Operations (v.copyStToM hp hm).heap hq) :
    let g := v.copyStToM hp hm
    let root : HRef K R := HRef.wk suffix.prefix g.val
    root.id = g.val.id ∧ Fresh H root.id ∧ ¬ Fresh K root.id ∧
      (old.wk (g.ext.trans suffix.prefix)).id ≠ root.id := by
  have hf := SVal.copyStToM_id_ge hp v hm
  have ho := HRef.id_lt old
  have hr := HRef.id_lt (HRef.wk suffix.prefix (v.copyStToM hp hm).val)
  refine ⟨rfl, hf, Nat.not_le_of_lt hr, ?_⟩
  change old.id ≠ (v.copyStToM hp hm).val.id
  omega

/-- Copies separated by arbitrary actual operations have strictly ordered roots.
No injectivity or separation assumption is supplied by the caller. -/
theorem copies_ordered {H K : HTy} (hp : Heap H) {R S : RefTy}
    (v : SVal (.ref R)) (hv : (Ty.ref R).mapFree = true) {hq : Heap K}
    (middle : Operations (v.copyStToM hp hv).heap hq)
    (w : SVal (.ref S)) (hw : (Ty.ref S).mapFree = true) :
    (HRef.wk middle.prefix (v.copyStToM hp hv).val).id < (w.copyStToM hq hw).val.id := by
  have ha := HRef.id_lt (v.copyStToM hp hv).val
  have hb := middle.prefix.length_le
  have hc := SVal.copyStToM_id_ge hq w hw
  change (v.copyStToM hp hv).val.id < (w.copyStToM hq hw).val.id
  omega

/-- The complete structural mirror certificate includes every nested allocation. -/
theorem copy_mirror {H : HTy} (hp : Heap H) {T : Ty} (v : SVal T)
    (hm : T.mapFree = true) :
    v.Mirrors (v.copyStToM hp hm).heap H.length (v.copyStToM hp hm).val :=
  SVal.mirrors_copyStToM hp v hm

#print axioms fresh_iff_absent
#print axioms copy_then_witness
#print axioms copies_ordered
#print axioms newFromWrite
#print axioms Writes.typing
#print axioms Writes.separate
#print axioms newFromCopySt
#print axioms copy_witness
#print axioms copy_not_converse
#print axioms Operations.prefix
#print axioms Operations.separate
#print axioms copy_mirror
end Solidity.SolkeyAgreementH28
