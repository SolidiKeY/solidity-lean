import Solidity.Evm.MemoryObjectAllocator
import Solidity.Evm.MemoryGrowResult

/-! Typed heap growth retains every older child identity and pointer word. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

/-- The source heap append has exactly one new typed identity. -/
theorem allocRef_split {H : HTy} {R T : RefTy} (hp : Heap H) (o : MObj H R)
    (r : HRef (H ++ [R]) T) :
    (∃ q : HRef H T, q.wk (List.prefix_append H [R]) = r) ∨
      (T = R ∧ HEq r (hp.alloc o).2) := by
  by_cases hi : r.id < H.length
  · let q : HRef H T := ⟨r.id, by simpa only [List.getElem?_append_left hi] using r.get?⟩
    have he : q.wk (List.prefix_append H [R]) = r := by cases r; rfl
    exact .inl ⟨q, he⟩
  · have hr : r.id = H.length := by
      have hl : r.id < (H ++ [R]).length := r.id_lt
      simp only [List.length_append, List.length_singleton] at hl
      omega
    exact .inr (HRef.heq_of_id r (hp.alloc o).2 hr)

theorem ValueRepr.wk {H H' : HTy} {base base' : Nat → Fin W} (e : H <+: H')
    (hb : BaseExtends H base base') {T : Ty} {v : MVal H T} {w : Word}
    (h : ValueRepr base T v w) : ValueRepr base' T (MVal.wk e T v) w := by
  cases T with
  | prim p => exact h
  | ref R => change w = .val (base' v.id); exact h.trans (congrArg Word.val (hb v).symm)

theorem cells_keeps {H H' : HTy} {hp : Heap H} {hp' : Heap H'} (e : H <+: H')
    (hk : Heap.Keeps e hp hp') {R : RefTy} (r : HRef H R) :
    cells hp' (r.wk e) = cells hp r := by
  cases R with
  | array E => simp only [cells, Heap.len, hk r, MObj.elems_wk, List.length_map]
  | fixed E n => rfl
  | struct s => rfl
  | mapping k E => rfl

theorem ArrayRepr.keeps {H H' : HTy} {hp : Heap H} {hp' : Heap H'}
    {A : RefTy} {E : Ty} {r : HRef H A} {a : ArrTy A E}
    {base base' : Nat → Fin W} {m : Machine} (h : ArrayRepr hp r a base m)
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (hb : BaseExtends H base base') :
    ArrayRepr hp' (r.wk e) a base' m := by
  have hr : base' (r.wk e).id = base r.id := hb r
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hr, cells_keeps e hk] using h.space
  · intro hh
    simpa only [hr, Heap.len, hk r, MObj.elems_wk, List.length_map] using h.length hh
  · intro i v hv
    rw [hk r, MObj.elems_wk, List.getElem?_map] at hv
    cases hx : (MObj.elems a (hp.get r))[i]? with
    | none => simp only [hx, Option.map_none] at hv; cases hv
    | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at hv
      subst v
      rw [hr]
      exact (h.elements i x hx).wk e hb

/-- Adopt an already represented fresh array at an independently reserved address.
This permits source children-before-parent order and target parent-before-children order. -/
theorem HeapRepr.adoptArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m)
    {A : RefTy} {E : Ty} (a : ArrTy A E) (o : MObj H A) (addr : Fin W)
    (ha : frame ≤ addr.val)
    (hf : ArrayRepr (hp.alloc o).1 (hp.alloc o).2 a (upd base H.length addr) m)
    (hd : ∀ {R : RefTy} (r : HRef H R),
      (base r.id).val + cells hp r ≤ addr.val ∨
        addr.val + cells (hp.alloc o).1 (hp.alloc o).2 ≤ (base r.id).val) :
    HeapRepr (hp.alloc o).1 (upd base H.length addr) frame m := by
  let e := List.prefix_append H [A]
  have hb : BaseExtends H base (upd base H.length addr) := fun r =>
    upd_other base addr (Nat.ne_of_lt r.id_lt)
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  have fresh : (hp.alloc o).2.id = H.length := rfl
  have oldbase {R : RefTy} (r : HRef H R) :
      upd base H.length addr (r.wk e).id = base r.id := hb r
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro R r
    rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
    · rw [oldbase]; exact h.owner.above q
    · cases ht; cases he
      simpa only [fresh, upd_same] using ha
  · intro R r
    rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
    · rw [oldbase, cells_keeps e hk]; exact h.owner.space q
    · cases ht; cases he; exact hf.space
  · intro R Q r q hn
    rcases allocRef_split hp o r with ⟨r, rfl⟩ | ⟨ht, he⟩
    · rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
      · simpa only [oldbase, cells_keeps e hk] using h.owner.separated r q hn
      · cases ht; cases he
        simpa only [oldbase, cells_keeps e hk, fresh, upd_same] using hd r
    · cases ht; cases he
      rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
      · have hdq := hd q
        simpa only [oldbase, cells_keeps e hk, fresh, upd_same] using hdq.symm
      · cases ht; cases he; exact (hn rfl).elim
  · intro B F b r
    rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
    · exact (h.arrays b q).keeps e hk hb
    · cases ht; cases he
      have heq : E = F ∧ HEq a b := by cases a <;> cases b <;> exact ⟨rfl, HEq.rfl⟩
      obtain ⟨rfl, heq⟩ := heq
      cases heq
      exact hf
  · intro s r
    rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
    · rw [oldbase]; exact (h.structs q).keeps e hk
    · exact (a.ne_struct s ht.symm).elim
  · exact RefFieldsRepr.alloc h.refs o addr (fun _ _ => rfl) (fun ht _ => a.ne_struct _ ht)

end Solidity.Evm.Memory.Objects
