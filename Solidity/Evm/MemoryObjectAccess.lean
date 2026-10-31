import Solidity.Evm.MemoryObjects

/-! Checked element addressing for both memory array layouts. Fixed arrays
have no length header; their type supplies the bound. Even a model bound at
least 2^256 is handled without wrapping that bound to a zero word. -/
namespace Solidity.Evm.Memory.Objects

/-- A fixed array checks its constant bound and adds no header offset. -/
def fixedAddrCode (n : Nat) : List Instr :=
  (if n < W then [.push (.val (wmod n)), .dup 2, .lt] ++ assertTop else []) ++ [.add]

/-- Address calculation follows the actual typed array kind. -/
def addressCode {A : RefTy} {E : Ty} (a : ArrTy A E) : List Instr :=
  @ArrTy.casesOn (fun _ _ _ => List Instr) A E a
    (fun {_} => arrayAddrStackCode) (fun {_} {n} => fixedAddrCode n)

def readCode {A : RefTy} {E : Ty} (a : ArrTy A E) : List Instr := addressCode a ++ [.mloadAt]
def writeCode {A : RefTy} {E : Ty} (a : ArrTy A E) : List Instr := addressCode a ++ [.mstoreAt]

/-- A value result retains its source type; bounds failures are exact reverts. -/
def ValueOut {H : HTy} {E : Ty} (base : Nat → Fin W)
    (source : TRes (MVal H E)) (target : Out) (m : Machine) : Prop :=
  (∃ v w, source = .ok v ∧ ValueRepr base E v w ∧ target = .ok (m.push w) 0) ∨
  (source = .error .revert ∧ target = .revert)

theorem ValueOut.primitive {H : HTy} {p : PrimTy} {base : Nat → Fin W}
    {source : TRes (MVal H (.prim p))} {target : Out} {m : Machine}
    (h : ValueOut base source target m) : ValOutT p source target m := h

theorem ValueOut.reference {H : HTy} {R : RefTy} {base : Nat → Fin W}
    {source : TRes (MVal H (.ref R))} {target : Out} {m : Machine}
    (h : ValueOut base source target m) : RefOut base source target m := by
  rcases h with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · change w = .val (base v.id) at hw
    rw [hw] at hc
    exact .inl ⟨v, hv, hc⟩
  · exact .inr ⟨hv, hc⟩

theorem fixedAddr_run (m : Machine) (base i : Fin W) (n : Nat) :
    run (fixedAddrCode n) ((m.push (.val base)).push (.val i)) =
      if i.val < n then .ok (m.push (.val (wmod (base.val + i.val)))) 0 else .revert := by
  by_cases hn : n < W
  · by_cases hi : i.val < n <;>
      simp only [run, fixedAddrCode, hn, assertTop, List.cons_append, List.nil_append,
        wmod_def, Nat.mod_eq_of_lt hn, Machine.push, exec_cons_zero, Instr.step,
        Machine.next, Out.ok_bind, Nat.add_one_sub_one, List.getElem?_cons_succ, List.getElem?_cons_zero,
        bword, hi, decide_true,
        decide_false, Bool.false_eq_true, ↓reduceIte, Fin.mk_one, Fin.isValue,
        Fin.val_one, Nat.succ_ne_self, exec_cons_succ, exec_nil, Fin.zero_eta,
        Fin.val_zero, Out.revert_bind, Nat.add_comm]
  · have hi : i.val < n := Nat.lt_of_lt_of_le i.isLt (Nat.le_of_not_gt hn)
    simp only [run, fixedAddrCode, hn, if_false, List.nil_append, if_pos hi,
      Machine.push, exec_cons_zero, Instr.step, Machine.next, Out.ok_bind,
      exec_nil, Nat.add_comm]

theorem ArrayRepr.address {H : HTy} {A : RefTy} {E : Ty} {hp : Heap H}
    {r : HRef H A} {a : ArrTy A E} {base : Nat → Fin W} {m : Machine}
    (h : ArrayRepr hp r a base m) (i : Fin W) :
    run (addressCode a) ((m.push (.val (base r.id))).push (.val i)) =
      if i.val < hp.len r a then
        .ok (m.push (.val (wmod ((base r.id).val + header a + i.val)))) 0 else .revert := by
  cases a with
  | dyn => exact arrayAddrStack_run m (base r.id) i _ (hp.len_dyn_lt r) (h.length rfl)
  | @fixed E n =>
    have hn : hp.len r .fixed = n := by
      change (MObj.elems .fixed (hp.get r)).length = n
      rw [MObj.elems_fixed]
      exact (hp.get r).property
    simpa only [addressCode, header, hn, Nat.add_zero] using fixedAddr_run m (base r.id) i n

/-- Pointer and primitive reads use the same typed heap evaluator. -/
theorem ArrayRepr.read {H : HTy} {A : RefTy} {E : Ty} {hp : Heap H}
    {r : HRef H A} {a : ArrTy A E} {base : Nat → Fin W} {m : Machine}
    (h : ArrayRepr hp r a base m) (i : Fin W) :
    ValueOut base (TRes.ofOpt (hp.index r a (indexValue i)))
      (run (readCode a) ((m.push (.val (base r.id))).push (.val i))) m := by
  have hc := h.address i
  by_cases hi : i.val < hp.len r a
  · rw [if_pos hi] at hc
    let v : MVal H E := (MObj.elems a (hp.get r))[i.val]'hi
    have hv : (MObj.elems a (hp.get r))[i.val]? = some v :=
      getElem?_pos (MObj.elems a (hp.get r)) i.val hi
    refine .inl ⟨v, m.mem ((base r.id).val + header a + i.val), ?_, h.elements _ _ hv, ?_⟩
    · simp only [Heap.index, indexValue, Int.toNat_natCast, hv, TRes.ofOpt]
    · have hs := h.space
      have hl := header_len_le_cells hp a r
      have ha : (base r.id).val + header a + i.val < W := by omega
      rw [readCode, run_append_ok hc]
      simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next,
        wmod_of_lt ha, Out.ok_bind, exec_nil]
  · rw [if_neg hi] at hc
    refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Heap.index, indexValue, Int.toNat_natCast,
      getElem?_neg (MObj.elems a (hp.get r)) i.val hi, TRes.ofOpt]

theorem cells_set_self {H : HTy} {A : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H A) (a : ArrTy A E) (i : Nat) (v : MVal H E) :
    cells (hp.set r (MObj.setElem a (hp.get r) i v)) r = cells hp r := by
  cases a <;> simp only [cells, Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set]

/-- Both layouts preserve every other element and their exact source length. -/
theorem ArrayRepr.set {H : HTy} {A : RefTy} {E : Ty} {hp : Heap H}
    {r : HRef H A} {a : ArrTy A E} {base : Nat → Fin W} {m : Machine}
    (h : ArrayRepr hp r a base m) (i : Nat) (hi : i < hp.len r a)
    (v : MVal H E) (w : Word) (hw : ValueRepr base E v w) :
    ArrayRepr (hp.set r (MObj.setElem a (hp.get r) i v)) r a base
      (writeMachine m ((base r.id).val + header a + i) w) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [cells_set_self] using h.space
  · intro hh
    change upd m.mem _ _ (base r.id).val = _
    rw [upd_other _ _ (by omega)]
    simpa only [Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set] using h.length hh
  · intro j x hx
    simp only [Heap.get_set_same, MObj.elems_setElem] at hx
    change ValueRepr base E x (upd m.mem _ _ ((base r.id).val + header a + j))
    by_cases he : i = j
    · subst j
      rw [List.getElem?_set_self hi] at hx
      obtain rfl := Option.some.inj hx
      rw [upd_same]
      exact hw
    · rw [List.getElem?_set_ne (l := MObj.elems a (hp.get r)) (a := v) he] at hx
      rw [upd_other _ _ (by omega)]
      exact h.elements j x hx

/-- An indexed typed pointer write agrees with the actual heap write or reverts. -/
theorem ArrayRepr.write {H : HTy} {A : RefTy} {E : Ty} {hp : Heap H}
    {r : HRef H A} {a : ArrTy A E} {base : Nat → Fin W} {m : Machine}
    (h : ArrayRepr hp r a base m) (i : Fin W) (v : MVal H E) (w : Word)
    (hw : ValueRepr base E v w) :
    (∃ hp', hp.writeAddr (.index r a (indexValue i)) v = some hp' ∧
      run (writeCode a) (((m.push w).push (.val (base r.id))).push (.val i)) =
        .ok (writeMachine m ((base r.id).val + header a + i.val) w) 0 ∧
      ArrayRepr hp' r a base (writeMachine m ((base r.id).val + header a + i.val) w)) ∨
    (hp.writeAddr (.index r a (indexValue i)) v = none ∧
      run (writeCode a) (((m.push w).push (.val (base r.id))).push (.val i)) = .revert) := by
  have hh : ArrayRepr hp r a base (m.push w) := ⟨h.space, h.length, h.elements⟩
  have hc := hh.address i
  by_cases hi : i.val < hp.len r a
  · rw [if_pos hi] at hc
    refine .inl ⟨hp.set r (MObj.setElem a (hp.get r) i.val v), ?_, ?_, h.set _ hi v w hw⟩
    · simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
      exact if_pos hi
    · have hs := h.space
      have hl := header_len_le_cells hp a r
      have ha : (base r.id).val + header a + i.val < W := by omega
      rw [writeCode, run_append_ok hc]
      simp only [run, Machine.push, exec_cons_zero, Instr.step, wmod_of_lt ha,
        Out.ok_bind, exec_nil, writeMachine]
  · rw [if_neg hi] at hc
    refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
    exact if_neg hi

end Solidity.Evm.Memory.Objects
