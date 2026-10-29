import Solidity.Evm.MemoryObjectAccess

/-! Whole-heap framing for typed element writes. The same proof handles a
primitive value or a child pointer in either dynamic or fixed arrays. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

/-- Positive disjoint reservations distinguish all actual object identities. -/
theorem Ownership.base_injective {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} (h : Ownership hp base frame) {R Q : RefTy}
    (r : HRef H R) (q : HRef H Q) (hb : base r.id = base q.id) : r.id = q.id := by
  by_cases he : r.id = q.id
  · exact he
  · have hd := h.separated r q he
    have hr := cells_pos hp r
    have hq := cells_pos hp q
    have hv := congrArg Fin.val hb
    rcases hd with hd | hd <;> omega

/-- Element replacement changes no object's reservation size. -/
theorem cells_set {H : HTy} {A Q : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H A) (a : ArrTy A E) (i : Nat) (v : MVal H E) (q : HRef H Q) :
    cells (hp.set r (MObj.setElem a (hp.get r) i v)) q = cells hp q := by
  by_cases he : r.id = q.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
    cases ht
    cases hr
    exact cells_set_self hp r a i v
  · cases Q with
    | array T => simp only [cells, Heap.len, Heap.get_set_ne hp r q he]
    | fixed T n => rfl
    | struct s => rfl
    | mapping k T => rfl

theorem Ownership.setArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} (h : Ownership hp base frame) {A : RefTy} {E : Ty}
    (r : HRef H A) (a : ArrTy A E) (i : Nat) (v : MVal H E) :
    Ownership (hp.set r (MObj.setElem a (hp.get r) i v)) base frame := by
  refine ⟨h.above, ?_, ?_⟩
  · intro Q q
    simpa only [cells_set] using h.space q
  · intro Q T q t hn
    simpa only [cells_set] using h.separated q t hn

private theorem array_same {A : RefTy} {E F : Ty} (a : ArrTy A E) (b : ArrTy A F) :
    E = F ∧ HEq a b := by
  cases a <;> cases b <;> exact ⟨rfl, HEq.rfl⟩

/-- Every child object and every other parent's words retain their representation. -/
theorem HeapRepr.setArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) {A : RefTy} {E : Ty}
    (r : HRef H A) (a : ArrTy A E) (i : Nat) (hi : i < hp.len r a)
    (v : MVal H E) (w : Word) (hw : ValueRepr base E v w) :
    HeapRepr (hp.set r (MObj.setElem a (hp.get r) i v)) base frame
      (writeMachine m ((base r.id).val + header a + i) w) := by
  have hrspan : (base r.id).val + header a + i < (base r.id).val + cells hp r := by
    have hs := header_len_le_cells hp a r
    omega
  refine ⟨h.owner.setArray r a i v, ?_, ?_, ?_⟩
  · intro B F b q
    by_cases he : r.id = q.id
    · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
      cases ht
      cases hr
      obtain ⟨hE, hb⟩ := array_same a b
      cases hE
      cases hb
      exact (h.arrays a r).set i hi v w hw
    · have hq := h.arrays b q
      have hd := h.owner.separated r q he
      have hpos := cells_pos hp q
      refine ⟨?_, ?_, ?_⟩
      · simpa only [cells_set] using hq.space
      · intro hb
        change upd m.mem _ _ (base q.id).val = _
        rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
        simpa only [Heap.len, Heap.get_set_ne hp r q he] using hq.length hb
      · intro j x hx
        rw [Heap.get_set_ne hp r q he] at hx
        have hj : j < hp.len q b := (List.getElem?_eq_some_iff.mp hx).1
        have hqspan : (base q.id).val + header b + j < (base q.id).val + cells hp q := by
          have hs := header_len_le_cells hp b q
          omega
        change ValueRepr base F x (upd m.mem _ _ _)
        rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
        exact hq.elements j x hx
  · intro s q
    have he : r.id ≠ q.id := by
      intro he
      exact (a.ne_struct s) (HRef.heq_of_id r q he).1
    refine ⟨(h.structs q).space, ?_⟩
    intro f p hf
    simp only [Heap.field, Heap.get_set_ne hp r q he]
    have hd := h.owner.separated r q he
    have ho := fieldOffset_bound hf
    have hs : (structDef s).length ≤ cells hp q := Nat.le_max_right _ _
    change ReprV p _ (upd m.mem _ _ _)
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact (h.structs q).fields hf
  · intro s f Q q hf
    have he : r.id ≠ q.id := by
      intro he
      exact (a.ne_struct s) (HRef.heq_of_id r q he).1
    simp only [Heap.field, Heap.get_set_ne hp r q he]
    have hd := h.owner.separated r q he
    have ho := fieldOffset_bound hf
    have hs : (structDef s).length ≤ cells hp q := Nat.le_max_right _ _
    change upd m.mem _ _ _ = _
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact h.refs q hf

/-- A raw word outside all live object intervals preserves the typed heap.
This also frames a reserved, not-yet-adopted parent during child allocation. -/
theorem HeapRepr.writeOutside {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) (addr : Nat) (w : Word)
    (ho : ∀ {R : RefTy} (r : HRef H R), addr < (base r.id).val ∨
      (base r.id).val + cells hp r ≤ addr) :
    HeapRepr hp base frame (writeMachine m addr w) := by
  refine ⟨h.owner, ?_, ?_, ?_⟩
  · intro A E a r
    have hd := ho r
    have hpos := cells_pos hp r
    refine ⟨(h.arrays a r).space, ?_, ?_⟩
    · intro hh
      change upd m.mem addr w (base r.id).val = _
      rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
      exact (h.arrays a r).length hh
    · intro i v hv
      have hi : i < hp.len r a := (List.getElem?_eq_some_iff.mp hv).1
      have hs := header_len_le_cells hp a r
      change ValueRepr base E v (upd m.mem addr w _)
      rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
      exact (h.arrays a r).elements i v hv
  · intro s r
    have hd := ho r
    refine ⟨(h.structs r).space, ?_⟩
    intro f p hf
    have hf' := fieldOffset_bound hf
    have hs : (structDef s).length ≤ cells hp r := Nat.le_max_right _ _
    change ReprV p _ (upd m.mem addr w _)
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact (h.structs r).fields hf
  · intro s f R r hf
    have hd := ho r
    have hf' := fieldOffset_bound hf
    have hs : (structDef s).length ≤ cells hp r := Nat.le_max_right _ _
    change upd m.mem addr w _ = _
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact h.refs r hf

variable {C : Contract}

theorem StateRepr.setArray {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {A : RefTy} {E : Ty}
    (r : HRef σ.H A) (a : ArrTy A E) (i : Nat) (hi : i < σ.heap.len r a)
    (v : MVal σ.H E) (w : Word) (hw : ValueRepr base E v w) :
    StateRepr L b frame F (σ.withHeap (σ.heap.set r (MObj.setElem a (σ.heap.get r) i v)))
      base (writeMachine m ((base r.id).val + header a + i) w) := by
  have hm : ∀ l, l < frame →
      (writeMachine m ((base r.id).val + header a + i) w).mem l = m.mem l := by
    intro l hl
    have hb := h.heap.owner.above r
    exact upd_other _ _ (by omega)
  have hc := h.core.congrMem (fun l _ hl => hm l (Nat.lt_of_lt_of_le hl h.locals))
  refine ⟨⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
    hc.fragile, hc.env, hc.funds, hc.oracle⟩, h.heap.setArray r a i hi v w hw, ?_, h.locals⟩
  intro Q j
  obtain ⟨q, hq, hj⟩ := h.pointers j
  exact ⟨q, hq, (hm _ (Nat.lt_of_lt_of_le (lvl_lt b j) h.locals)).trans hj⟩

theorem StateRepr.setMem {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (dst : Idx Γ (.mem R)) (r : HRef σ.H R) :
    StateRepr L b frame F (σ.setLocal dst (some r)) base
      (writeMachine m (cellOf b dst) (.val (base r.id))) := by
  have old := h.legacy.setMem dst r
  exact ⟨old.core, h.heap.localWrite _ (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _,
    old.pointers, old.locals⟩

theorem StateRepr.setVal {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy} (dst : Idx Γ (.val p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StateRepr L b frame F (σ.setLocal dst v) base (writeMachine m (cellOf b dst) w) := by
  have old := h.legacy.setVal dst v w hw
  exact ⟨old.core, h.heap.localWrite _ (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _,
    old.pointers, old.locals⟩

theorem StateRepr.consMem {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy} (r : HRef σ.H R)
    (hcap : b + (Γ.length + 1) ≤ frame) :
    StateRepr L b frame (F.push (.mem R) .ok) (σ.push (t := .mem R) (some r)) base
      (writeMachine m (cell (b + Γ.length)) (.val (base r.id))) := by
  have old := h.legacy.consMem r hcap
  exact ⟨old.core, h.heap.localWrite (b + Γ.length) (by omega) _, old.pointers, old.locals⟩

theorem StateRepr.consVal {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy} (v : p.Denote) (w : Word)
    (hw : ReprV p v w) (hcap : b + (Γ.length + 1) ≤ frame) :
    StateRepr L b frame (F.push (.val p) .ok) (σ.push (t := .val p) v) base
      (writeMachine m (cell (b + Γ.length)) w) := by
  have old := h.legacy.consVal v w hw hcap
  exact ⟨old.core, h.heap.localWrite (b + Γ.length) (by omega) _, old.pointers, old.locals⟩

end Solidity.Evm.Memory.Objects
