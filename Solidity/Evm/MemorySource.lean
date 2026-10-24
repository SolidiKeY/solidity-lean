import Solidity.Evm.MemoryHeap
import Solidity.Evm.MemoryRefs
import Solidity.Evm.Expr
import Solidity.Semantics.RunFrame

/-!
# Scoped source operations on represented memory

The core simulation is augmented by a separated heap and actual pointer
locals. The frame limit covers every local frame the compiled program uses.
Primitive arrays and structs occupy disjoint regions above it; every memory
local retains its typed reference and runtime pointer through source updates.
-/
namespace Solidity.Evm.Memory

variable {C : Contract}

/-- Every memory local is initialized, and its typed reference agrees
with its runtime pointer cell. Unset declarations need a separate rule. -/
def PointerRepr {Γ : Ctx} (σ : State C Γ) (base : Nat → Fin W) (b : Nat)
    (m : Machine) : Prop :=
  ∀ {R : RefTy} (i : Idx Γ (.mem R)),
    ∃ r, TEnv.get i σ.env = some r ∧ m.mem (cellOf b i) = .val (base r.id)

/-- The core state, heap objects and live pointers are represented together. -/
structure StateRepr (L b frame : Nat) {Γ : Ctx} (F : Frag Γ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop where
  core : Sim C L b F σ m
  heap : HeapRepr σ.heap base frame m
  pointers : PointerRepr σ base b m
  locals : b + Γ.length ≤ frame
  structs : StructHeapRepr σ.heap base frame m
  separated : StructArraySeparated σ.heap base
  refs : RefFieldsRepr σ.heap base m

theorem StateRepr.push {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (w : Word) :
    StateRepr L b frame F σ base (m.push w) :=
  ⟨h.core.push w, ⟨fun r => (h.heap.arrays r).stack _, h.heap.above, h.heap.separated⟩,
    h.pointers, h.locals, h.structs.stack _, h.separated, RefFieldsRepr.mem_eq h.refs rfl⟩

/-- A primitive local assignment preserves the separated heap and pointers. -/
theorem StateRepr.setVal {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (i : Idx Γ (.val p)) (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StateRepr L b frame F (σ.setLocal i v) base (writeMachine m (cellOf b i) w) := by
  have hl : lvl b i < frame := Nat.lt_of_lt_of_le (lvl_lt b i) h.locals
  constructor
  · have hc := (h.core.setVal i hw).congrLook (fun j => Look.ofTEnv_set i v σ.env j)
    exact ⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩
  · exact h.heap.localWrite _ hl w
  · intro q j
    have hne : i.toNat ≠ j.toNat := fun he => by cases Idx.ty_eq i j he
    obtain ⟨r, hr, hm⟩ := h.pointers j
    refine ⟨r, ?_, ?_⟩
    · exact (TEnv.get_set_ne i j v σ.env hne).trans hr
    · change upd m.mem (cellOf b i) w (cellOf b j) = _
      rw [upd_other _ _ (fun he => hne ((lvl_eq_iff b i j).mp he.symm))]
      exact hm
  · exact h.locals
  · exact h.structs.localWrite _ hl w
  · exact h.separated
  · exact RefFieldsRepr.localWrite h.refs h.structs _ hl w

/-- Heap updates cannot disturb the core simulation or any pointer local. -/
theorem StateRepr.set {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (r : HRef σ.H (.array (.prim p))) (i : Nat) (hi : i < σ.heap.len r .dyn)
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StateRepr L b frame F (σ.withHeap (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) i v)))
      base (writeMachine m ((base r.id).1 + 1 + i) w) := by
  have hc := h.core.congrMem (mem := upd m.mem ((base r.id).1 + 1 + i) w)
    (fun l _ hl => h.heap.write_below r i w l (Nat.lt_of_lt_of_le hl h.locals))
  constructor
  · exact ⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩
  · exact h.heap.set r i hi v w hw
  · intro q j
    obtain ⟨s, hs, hm⟩ := h.pointers j
    refine ⟨s, hs, ?_⟩
    rw [h.heap.write_below r i w (lvl b j) (Nat.lt_of_lt_of_le (lvl_lt b j) h.locals)]
    exact hm
  · exact h.locals
  · exact h.structs.arraySet h.separated r i hi v w
  · exact StructArraySeparated.setArray h.separated r i v
  · exact RefFieldsRepr.arraySet h.refs h.separated r i hi v w

/-- Compile an array read through a local pointer and an existing core index
expression. The pointer is evaluated before its index, as in the source. -/
def readLocalCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (j : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint) : List Instr :=
  [.mload (cellOf b j)] ++ compileVal b i ++ readArrayStackCode

def readLocalValueCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (j : Idx Γ (.mem (.array (.prim p)))) (index : List Instr) : List Instr :=
  [.mload (cellOf b j)] ++ index ++ readArrayStackCode

/-- A read through an actual typed pointer local agrees with the source. -/
theorem readLocalValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (j : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint) (index : List Instr)
    (hi : ∀ {m' : Machine}, StateRepr L b frame F σ base m' →
      ValOutT .uint (i.evalT σ) (run index m') m') :
    ValOutT p ((Val.readMem (.index .dyn (.var j rfl) i)).evalT σ)
      (run (readLocalValueCode b j index) m) m := by
  obtain ⟨r, hr, hm⟩ := h.pointers j
  have harr := h.heap.arrays r
  simp only [Val.evalT, MLoc.addrT, MPath.mvalT, hr, bind, Except.bind]
  rw [readLocalValueCode, List.append_assoc, run_append_ok (show
    run [.mload (cellOf b j)] m = .ok (m.push (.val (base r.id))) 0 by
      change Out.ok (m.push (m.mem (cellOf b j))) 0 = _
      rw [hm])]
  rcases hi (h.push (.val (base r.id))) with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · obtain ⟨a, ha, hva, rfl⟩ := hw.uint_inv
    have he : v = indexValue ⟨a, ha⟩ := Subtype.ext hva
    subst v
    rw [hv, run_append_ok hc]
    rw [readArrayStackCode, arrayStack_append_eq m (base r.id) ⟨a, ha⟩ _
      (σ.heap.len_dyn_lt r) harr.length, ← readArrayCode]
    exact readArray_correct harr ⟨a, ha⟩
  · rw [hv, run_append_revert hc]
    exact .inr ⟨rfl, rfl⟩

theorem readLocal_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (j : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint)
    (hi : valIn F i = true) :
    ValOutT p ((Val.readMem (.index .dyn (.var j rfl) i)).evalT σ)
      (run (readLocalCode b j i) m) m :=
  readLocalValue_correct h j i (Evm.compileVal b i) (fun h' => val_sim i h'.core hi)

/-- The compiler emits the RHS first, then the receiver pointer and index. -/
def writeLocalCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (j : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint) (v : Val C Γ p) : List Instr :=
  compileVal b v ++ [.mload (cellOf b j)] ++ compileVal b i ++ writeArrayStackCode

def writeLocalValueCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (j : Idx Γ (.mem (.array (.prim p)))) (index value : List Instr) : List Instr :=
  value ++ [.mload (cellOf b j)] ++ index ++ writeArrayStackCode

/-- An existing allocator survives statements that allocate no object. The
nonzero frame premise is required only when the caller has an allocator. -/
def KeepsAllocator {Γ Δ : Ctx} (b frame : Nat) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (τ : State C Δ) (m' : Machine) : Prop :=
  ∀ cursor, 0 < b → StructAllocatorRepr σ.heap base frame cursor m →
    StructAllocatorRepr τ.heap base frame cursor m'

/-- Matching successful source/machine results, or matching reversion.
Successful code preserves the stack and any existing allocator. -/
def ResultRepr {Γ Δ : Ctx} (L b frame : Nat) (F : Frag Δ) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (res : TRes (Solidity.Out C σ.H Δ)) (out : Out) : Prop :=
  (∃ o m', res = .ok o ∧ out = .ok m' 0 ∧ StateRepr L b frame F o.st base m' ∧
    m'.stack = m.stack ∧ KeepsAllocator b frame σ base m o.st m') ∨
      (res = .error .revert ∧ out = .revert)

/-- Store a compiled read in a typed primitive local. -/
def readAssignCode {Γ : Ctx} {p : PrimTy} (b : Nat) (dst : Idx Γ (.val p))
    (src : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint) : List Instr :=
  readLocalCode b src i ++ [.mstore (cellOf b dst)]

theorem readAssign_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (dst : Idx Γ (.val p)) (src : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint)
    (hi : valIn F i = true) :
    ResultRepr L b frame F σ base m
      (TRun.assignLocal dst (.readMem (.index .dyn (.var src rfl) i)) σ)
      (run (readAssignCode b dst src i) m) := by
  rcases readLocal_correct h src i hi with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · refine .inl ⟨⟨σ.setLocal dst v, List.prefix_refl _⟩,
      writeMachine m (cellOf b dst) w, ?_, ?_, h.setVal dst v w hw, rfl, ?_⟩
    · simp only [TRun.assignLocal, hv, bind, Except.bind]
      rfl
    · rw [readAssignCode, run_append_ok hc]
      rfl
    · intro cursor hb ha
      exact ha.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
        (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) w
  · refine .inr ⟨?_, ?_⟩
    · simp only [TRun.assignLocal, hv, bind, Except.bind]
    · exact run_append_revert hc

/-- A scoped source write preserves the full state relation, including aliases,
independent arrays and local frames, or reverts on both sides. -/
theorem writeLocalValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (j : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint) (v : Val C Γ p)
    (index value : List Instr)
    (hi : ∀ {m' : Machine}, StateRepr L b frame F σ base m' →
      ValOutT .uint (i.evalT σ) (run index m') m')
    (hv : ValOutT p (v.evalT σ) (run value m) m) :
    ResultRepr L b frame F σ base m
      (TRun.assignMem (.index .dyn (.var j rfl) i) (.val v) σ)
      (run (writeLocalValueCode b j index value) m) := by
  obtain ⟨r, hr, hm⟩ := h.pointers j
  have harr := h.heap.arrays r
  simp only [ResultRepr, TRun.assignMem, MSrc.mvalT, MLoc.addrT, MPath.mvalT,
    hr, bind, Except.bind]
  rw [writeLocalValueCode, List.append_assoc, List.append_assoc]
  rcases hv with ⟨x, w, hx, hw, hc⟩ | ⟨hx, hc⟩
  · rw [hx, run_append_ok hc]
    rw [run_append_ok (show run [.mload (cellOf b j)] (m.push w) =
      .ok ((m.push w).push (.val (base r.id))) 0 by
        change Out.ok ((m.push w).push (m.mem (cellOf b j))) 0 = _
        rw [hm])]
    rcases hi ((h.push w).push (.val (base r.id))) with
      ⟨iv, iw, hiv, hiw, hic⟩ | ⟨hiv, hic⟩
    · obtain ⟨a, ha, hva, rfl⟩ := hiw.uint_inv
      have he : iv = indexValue ⟨a, ha⟩ := Subtype.ext hva
      subst iv
      rw [hiv, run_append_ok hic, writeArrayStackCode,
        arrayStack_append_eq (m.push w) (base r.id) ⟨a, ha⟩ _
          (σ.heap.len_dyn_lt r) harr.length, ← writeArrayCode]
      by_cases hin : a < σ.heap.len r .dyn
      · have hc := arrayAddr_run (m.push w) (base r.id) ⟨a, ha⟩ _
          (σ.heap.len_dyn_lt r) harr.length
        rw [if_pos hin] at hc
        have haddr : (base r.id).1 + 1 + a < W := by have hs := harr.space; omega
        rw [writeArrayCode, run_append_ok hc]
        have hrun : run [Instr.mstoreAt]
            ((m.push w).push (.val (wmod ((base r.id).1 + 1 + a)))) =
            .ok (writeMachine m ((base r.id).1 + 1 + a) w) 0 := by
          simp only [run, Machine.push, exec_cons_zero, Instr.step, wmod_of_lt haddr,
            Out.ok_bind, exec_nil, writeMachine]
        rw [hrun]
        refine .inl ⟨⟨σ.withHeap (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) a x)),
          List.prefix_refl _⟩, _, ?_, rfl, h.set r a hin x w hw, rfl, ?_⟩
        · simp only [pure, Except.pure, Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
          rw [if_pos (show a < (MObj.elems .dyn (σ.heap.get r)).length from hin)]
          rfl
        · exact fun _ _ ha => ha.setArray r a hin x w hw
      · have hc := arrayAddr_run (m.push w) (base r.id) ⟨a, ha⟩ _
          (σ.heap.len_dyn_lt r) harr.length
        rw [if_neg hin] at hc
        refine .inr ⟨?_, run_append_revert hc⟩
        simp only [pure, Except.pure, Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
        rw [if_neg (show ¬a < (MObj.elems .dyn (σ.heap.get r)).length from hin)]
        rfl
    · rw [hiv, run_append_revert hic]
      exact .inr ⟨rfl, rfl⟩
  · rw [hx, run_append_revert hc]
    exact .inr ⟨rfl, rfl⟩

theorem writeLocal_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (j : Idx Γ (.mem (.array (.prim p)))) (i : Val C Γ .uint) (v : Val C Γ p)
    (hi : valIn F i = true) (hv : valIn F v = true) :
    ResultRepr L b frame F σ base m
      (TRun.assignMem (.index .dyn (.var j rfl) i) (.val v) σ)
      (run (writeLocalCode b j i v) m) :=
  writeLocalValue_correct h j i v (Evm.compileVal b i) (Evm.compileVal b v)
    (fun h' => val_sim i h'.core hi) (val_sim v h.core hv)

end Solidity.Evm.Memory
