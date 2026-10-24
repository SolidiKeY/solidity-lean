import Solidity.Evm.SimLemmas
import Solidity.Theory.Typed.Mem

/-!
# Memory arrays on the word-addressed machine

A dynamic primitive array has a length cell followed by its elements.
References to the same source object use the same base. `ArrayRepr` relates
the actual typed heap to those cells, with an explicit no-wrap bound.
The access code checks the source index before computing an address; an
out-of-bounds access reverts, rather than reading an unconstrained cell.

These are the local simulation lemmas for memory compilation. The existing
whole-program compiler fragment is extended only once its heap/local frame
relation also preserves these representations.
-/
namespace Solidity.Evm.Memory

/-- Compute the cell of an indexed element, leaving the rest of the stack.
The input index is on top. Both callers check bounds before accessing memory. -/
def arrayAddrCode (base : Fin W) : List Instr :=
  [.push (.val base), .mloadAt, .dup 2, .lt] ++ assertTop ++
    [.push (.val (wmod (base.1 + 1))), .add]

/-- A primitive element read from an array whose pointer is `base`. -/
def readArrayCode (base : Fin W) : List Instr := arrayAddrCode base ++ [.mloadAt]

/-- A primitive element write: the input index is above the value to write. -/
def writeArrayCode (base : Fin W) : List Instr := arrayAddrCode base ++ [.mstoreAt]

/-- The runtime-pointer variant consumes an index above its array base. -/
def arrayAddrStackCode : List Instr :=
  [.dup 2, .mloadAt, .dup 2, .lt] ++ assertTop ++ [.add, .push w[1], .add]

def readArrayStackCode : List Instr := arrayAddrStackCode ++ [.mloadAt]
def writeArrayStackCode : List Instr := arrayAddrStackCode ++ [.mstoreAt]

/-- The word index as the interpreter's typed unsigned value. -/
def indexValue (i : Fin W) : PrimTy.uint.Denote :=
  ⟨i.1, by
    change decide (0 ≤ (i.1 : Int) ∧ (i.1 : Int) < (W : Int)) = true
    exact decide_eq_true ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr i.2⟩⟩

/-- One actual typed array represented in a bounded, contiguous memory region. -/
structure ArrayRepr {H : HTy} {p : PrimTy} (hp : Heap H)
    (r : HRef H (.array (.prim p))) (base : Fin W) (m : Machine) : Prop where
  space : base.1 + 1 + hp.len r .dyn ≤ W
  length : m.mem base.1 = .val (wmod (hp.len r .dyn))
  elements : ∀ i v, (MObj.elems .dyn (hp.get r))[i]? = some v →
    ReprV p v (m.mem (base.1 + 1 + i))

/-- The stack does not change the array representation. -/
theorem ArrayRepr.stack {H : HTy} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.array (.prim p))} {base : Fin W} {m : Machine}
    (h : ArrayRepr hp r base m) (st : List Word) :
    ArrayRepr hp r base {m with stack := st} :=
  ⟨h.space, h.length, h.elements⟩

/-- Bounds are checked against the represented length before address arithmetic. -/
theorem arrayAddr_run (m : Machine) (base i : Fin W) (n : Nat) (hn : n < W)
    (hmem : m.mem base.1 = .val (wmod n)) :
    run (arrayAddrCode base) (m.push (.val i)) =
      if i.1 < n then .ok (m.push (.val (wmod (base.1 + 1 + i.1)))) 0 else .revert := by
  by_cases hi : i.1 < n <;>
    simp only [run, arrayAddrCode, assertTop, List.cons_append, List.nil_append,
      wmod_def, Nat.add_mod, Nat.dvd_refl, Nat.mod_mod_of_dvd, Machine.push,
      exec_cons_zero, Instr.step, Machine.next, Out.ok_bind, hmem, Nat.mod_eq_of_lt hn,
      Nat.add_one_sub_one, List.length_cons, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ,
      getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, bword, hi,
      decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, Fin.mk_one,
      Fin.isValue, Fin.val_one, Nat.succ_ne_self, exec_cons_succ, exec_nil,
      Fin.zero_eta, Fin.val_zero, Out.revert_bind]

/-- Runtime pointers have exactly the same checked address calculation. -/
theorem arrayAddrStack_run (m : Machine) (base i : Fin W) (n : Nat) (hn : n < W)
    (hmem : m.mem base.1 = .val (wmod n)) :
    run arrayAddrStackCode ((m.push (.val base)).push (.val i)) =
      if i.1 < n then .ok (m.push (.val (wmod (base.1 + 1 + i.1)))) 0 else .revert := by
  by_cases hi : i.1 < n <;>
    simp only [run, arrayAddrStackCode, assertTop, List.cons_append, List.nil_append,
      wmod_def, Nat.add_mod, Nat.dvd_refl, Nat.mod_mod_of_dvd, Machine.push,
      exec_cons_zero, Instr.step, Machine.next, Out.ok_bind, hmem, Nat.mod_eq_of_lt hn,
      Nat.add_one_sub_one, List.length_cons, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ,
      getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, bword, hi,
      decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, Fin.mk_one,
      Fin.isValue, Fin.val_one, Nat.succ_ne_self, exec_cons_succ, exec_nil,
      Fin.zero_eta, Fin.val_zero, Out.revert_bind]
  simp only [Nat.mod_mod, ← Nat.add_mod, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Stack pointers and literal pointers agree even with a following operation. -/
theorem arrayStack_append_eq (m : Machine) (base i : Fin W) (n : Nat) (hn : n < W)
    (hmem : m.mem base.1 = .val (wmod n)) (tail : List Instr) :
    run (arrayAddrStackCode ++ tail) ((m.push (.val base)).push (.val i)) =
      run (arrayAddrCode base ++ tail) (m.push (.val i)) := by
  unfold run
  rw [exec_append, exec_append]
  congr 1
  exact (arrayAddrStack_run m base i n hn hmem).trans (arrayAddr_run m base i n hn hmem).symm

/-- A compiled primitive array read returns the same typed value or reverts
on exactly the same out-of-bounds index. -/
theorem readArray_correct {H : HTy} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.array (.prim p))} {base : Fin W} {m : Machine}
    (h : ArrayRepr hp r base m) (i : Fin W) :
    ValOutT p (TRes.ofOpt (hp.index r .dyn (indexValue i)))
      (run (readArrayCode base) (m.push (.val i))) m := by
  have hc := arrayAddr_run m base i _ (hp.len_dyn_lt r) h.length
  by_cases hi : i.1 < hp.len r .dyn
  · rw [if_pos hi] at hc
    let v : p.Denote := (MObj.elems .dyn (hp.get r))[i.1]'hi
    have hv : (MObj.elems .dyn (hp.get r))[i.1]? = some v :=
      getElem?_pos (MObj.elems .dyn (hp.get r)) i.1 hi
    refine .inl ⟨v, m.mem (base.1 + 1 + i.1), ?_, h.elements _ _ hv, ?_⟩
    · simp only [Heap.index, indexValue, Int.toNat_natCast, hv, TRes.ofOpt]
    · have haddr : base.1 + 1 + i.1 < W := by have hs := h.space; omega
      rw [readArrayCode, run_append_ok hc]
      simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next,
        wmod_of_lt haddr, Out.ok_bind, exec_nil]
  · rw [if_neg hi] at hc
    refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Heap.index, indexValue, Int.toNat_natCast,
      getElem?_neg (MObj.elems .dyn (hp.get r)) i.1 hi, TRes.ofOpt]

/-- A word write in the target memory, preserving every other machine field. -/
def writeMachine (m : Machine) (addr : Nat) (w : Word) : Machine :=
  {m with mem := upd m.mem addr w}

/-- Updating an in-bounds primitive element preserves the array representation. -/
theorem ArrayRepr.set {H : HTy} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.array (.prim p))} {base : Fin W} {m : Machine}
    (h : ArrayRepr hp r base m) (i : Nat) (hi : i < hp.len r .dyn)
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    ArrayRepr (hp.set r (MObj.setElem .dyn (hp.get r) i v)) r base
      (writeMachine m (base.1 + 1 + i) w) := by
  constructor
  · simpa only [Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set] using h.space
  · show upd m.mem (base.1 + 1 + i) w base.1 = _
    rw [upd_other _ _ (show base.1 ≠ base.1 + 1 + i by omega)]
    simpa only [Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set] using h.length
  · intro j x hx
    simp only [Heap.get_set_same, MObj.elems_setElem] at hx
    show ReprV p x (upd m.mem (base.1 + 1 + i) w (base.1 + 1 + j))
    by_cases hij : i = j
    · subst j
      rw [List.getElem?_set_self hi] at hx
      obtain rfl := Option.some.inj hx
      rw [upd_same]
      exact hw
    · rw [List.getElem?_set_ne (l := MObj.elems .dyn (hp.get r)) (a := v) hij] at hx
      rw [upd_other _ _ (show base.1 + 1 + j ≠ base.1 + 1 + i by omega)]
      exact h.elements j x hx

/-- A compiled write agrees with the actual typed heap update, including
reversion at the length boundary. Successful writes keep their representation. -/
theorem writeArray_correct {H : HTy} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.array (.prim p))} {base : Fin W} {m : Machine}
    (h : ArrayRepr hp r base m) (i : Fin W) (v : p.Denote) (w : Word)
    (hw : ReprV p v w) :
    (∃ hp', hp.writeAddr (.index r .dyn (indexValue i)) v = some hp' ∧
      run (writeArrayCode base) ((m.push w).push (.val i)) =
        .ok (writeMachine m (base.1 + 1 + i.1) w) 0 ∧
      ArrayRepr hp' r base (writeMachine m (base.1 + 1 + i.1) w)) ∨
    (hp.writeAddr (.index r .dyn (indexValue i)) v = none ∧
      run (writeArrayCode base) ((m.push w).push (.val i)) = .revert) := by
  have hc := arrayAddr_run (m.push w) base i _ (hp.len_dyn_lt r) h.length
  by_cases hi : i.1 < hp.len r .dyn
  · rw [if_pos hi] at hc
    refine .inl ⟨hp.set r (MObj.setElem .dyn (hp.get r) i.1 v), ?_, ?_, h.set _ hi v w hw⟩
    · simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
      exact if_pos hi
    · have haddr : base.1 + 1 + i.1 < W := by have hs := h.space; omega
      rw [writeArrayCode, run_append_ok hc]
      simp only [run, Machine.push, exec_cons_zero, Instr.step,
        wmod_of_lt haddr, Out.ok_bind, exec_nil, writeMachine]
  · rw [if_neg hi] at hc
    refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
    exact if_neg hi

end Solidity.Evm.Memory
