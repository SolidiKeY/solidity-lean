import Solidity.Evm.MemoryObjectValues
import Solidity.Evm.MemoryObjectFieldFrame

/-! Generic typed element stores and alias binding, with full allocator framing. -/
namespace Solidity.Evm.Memory.Objects
open Semantics
variable {C : Contract}

inductive SrcFrag (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {T : Ty} → MSrc C Γ T → List Instr → Prop where
  | val {p : PrimTy} (v : Val C Γ p) (code : List Instr) (hv : ValFrag b F v code) :
      SrcFrag b F (.val v) code
  | ref {R : RefTy} (v : MPath C Γ (.ref R)) (code : List Instr) (hv : PtrFrag b F v code) :
      SrcFrag b F (.ref v) code

structure CompiledSrc (b : Nat) {Γ : Ctx} (F : Frag Γ) {T : Ty} (v : MSrc C Γ T) where
  code : List Instr
  cert : SrcFrag b F v code

def compileSrc (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {T : Ty} → (v : MSrc C Γ T) → Option (CompiledSrc b F v)
  | _, .val v => do
    let r ← compileVal b F v
    pure ⟨_, .val v r.code r.cert⟩
  | _, .ref v => do
    let r ← compilePtr b F v
    pure ⟨_, .ref v r.code r.cert⟩

theorem SrcFrag.correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {T : Ty} {v : MSrc C Γ T} {code : List Instr}
    (hv : SrcFrag b F v code) : ValueOut base (v.mvalT σ) (run code m) m := by
  cases hv with
  | val v code hv => exact hv.correct h
  | ref v code hv =>
    rcases hv.correct h with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
    · exact .inl ⟨r, .val (base r.id), hr, rfl, hc⟩
    · exact .inr ⟨hr, hc⟩

/-- Successful nonallocating execution preserves all objects and any complete allocator. -/
def ResultRepr {Γ Δ : Ctx} (L b frame : Nat) (F : Frag Δ) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (res : TRes (Solidity.Out C σ.H Δ)) (out : Out) : Prop :=
  (∃ o m', res = .ok o ∧ out = .ok m' 0 ∧ StateRepr L b frame F o.st base m' ∧
    m'.stack = m.stack ∧ KeepsAllocator b frame σ base m o.st m') ∨
  (res = .error .revert ∧ out = .revert)

theorem PtrFrag.write {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {A : RefTy} {E : Ty}
    (a : ArrTy A E) {dst : MPath C Γ (.ref A)} {v : MSrc C Γ E}
    {pointer value : List Instr} (hd : PtrFrag b F dst pointer) (hv : SrcFrag b F v value)
    (i : Val C Γ .uint) (hi : valIn F i = true) :
    ResultRepr L b frame F σ base m (TRun.assignMem (.index a dst i) v σ)
      (run (value ++ pointer ++ Evm.compileVal b i ++ writeCode a) m) := by
  simp only [ResultRepr, TRun.assignMem, bind, Except.bind]
  rw [List.append_assoc, List.append_assoc]
  rcases hv.correct h with ⟨v, w, hv, hw, hcv⟩ | ⟨hv, hcv⟩
  · rw [hv, run_append_ok hcv]
    rcases hd.correct (h.push w) with ⟨r, hr, hcr⟩ | ⟨hr, hcr⟩
    · simp only [MLoc.addrT, hr, bind, Except.bind]
      rw [run_append_ok hcr]
      rcases val_sim i ((h.push w).push (.val (base r.id))).core hi with
        ⟨iv, iw, hiv, hiw, hic⟩ | ⟨hiv, hic⟩
      · obtain ⟨n, hn, hvn, rfl⟩ := hiw.uint_inv
        have he : iv = indexValue ⟨n, hn⟩ := Subtype.ext hvn
        subst iv
        rw [hiv, run_append_ok hic]
        simp only [pure, Except.pure]
        rcases (h.heap.arrays a r).write ⟨n, hn⟩ v w hw with
          ⟨hp', hpwrite, hrun, _⟩ | ⟨hpwrite, hrun⟩
        · rw [hpwrite, hrun]
          have hin : n < (MObj.elems a (σ.heap.get r)).length := by
            by_cases hin : n < (MObj.elems a (σ.heap.get r)).length
            · exact hin
            · simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast,
                if_neg hin] at hpwrite
              cases hpwrite
          have he : hp' = σ.heap.set r (MObj.setElem a (σ.heap.get r) n v) := by
            simpa only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast,
              if_pos hin, Option.some.injEq] using hpwrite.symm
          subst hp'
          refine .inl ⟨⟨σ.withHeap (σ.heap.set r (MObj.setElem a (σ.heap.get r) n v)), List.prefix_refl _⟩, _, rfl, rfl,
            h.setArray r a n hin v w hw, rfl, ?_⟩
          intro cursor hb ha
          exact ha.setArray r a n hin v w hw
        · rw [hpwrite, hrun]
          exact .inr ⟨rfl, rfl⟩
      · rw [hiv, run_append_revert hic]
        exact .inr ⟨rfl, rfl⟩
    · refine .inr ⟨?_, run_append_revert hcr⟩
      simp only [MLoc.addrT, hr, bind, Except.bind]
  · rw [hv, run_append_revert hcv]
    exact .inr ⟨rfl, rfl⟩

theorem PtrFrag.writeField {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    {dst : MPath C Γ (.ref (.struct s))} {v : Val C Γ p}
    {pointer value : List Instr} (hd : PtrFrag b F dst pointer) (hv : ValFrag b F v value)
    (hf : C.fieldType s f = some (.prim p)) :
    ResultRepr L b frame F σ base m (TRun.assignMem (.field dst f hf) (.val v) σ)
      (run (value ++ pointer ++ writeFieldCode (fieldOffset (structDef s) f)) m) := by
  simp only [ResultRepr, TRun.assignMem, MSrc.mvalT, bind, Except.bind]
  rw [List.append_assoc]
  rcases hv.correct h with ⟨v, w, hv, hw, hcv⟩ | ⟨hv, hcv⟩
  · rw [hv, run_append_ok hcv]
    rcases hd.correct (h.push w) with ⟨r, hr, hcr⟩ | ⟨hr, hcr⟩
    · simp only [MLoc.addrT, hr, bind, Except.bind, pure, Except.pure]
      rw [run_append_ok hcr, (writeField_correct (h.heap.structs r) hf v w hw).2.1]
      refine .inl ⟨⟨σ.withHeap (σ.heap.setField r hf v), List.prefix_refl _⟩, _, rfl, rfl,
        h.setStruct r hf v w hw, rfl, ?_⟩
      intro cursor hb ha
      exact ha.setStruct r hf v w hw
    · refine .inr ⟨?_, run_append_revert hcr⟩
      simp only [MLoc.addrT, hr, bind, Except.bind]
  · rw [hv, run_append_revert hcv]
    exact .inr ⟨rfl, rfl⟩

theorem PtrFrag.rebind {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : PtrFrag b F src code)
    (dst : Idx Γ (.mem R)) :
    ResultRepr L b frame F σ base m (TRun.rebindMem dst (.alias src) σ)
      (run (code ++ [.mstore (cellOf b dst)]) m) := by
  rcases hs.correct h with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
  · refine .inl ⟨⟨σ.setLocal dst (some r), List.prefix_refl _⟩, _, ?_, ?_,
      h.setMem dst r, rfl, ?_⟩
    · simp only [TRun.rebindMem, MRhs.evalT, hr, bind, Except.bind, pure, Except.pure]
    · rw [run_append_ok hc]
      rfl
    · intro cursor hb ha
      exact ha.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
        (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [TRun.rebindMem, MRhs.evalT, hr, bind, Except.bind]

theorem PtrFrag.declareAlias {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : PtrFrag b F src code) (hm)
    (hcap : b + (Γ.length + 1) ≤ frame) :
    ResultRepr L b frame (F.push (.mem R) .ok) σ base m
      (TRun.declMem R (some (.alias src)) hm σ)
      (run (code ++ [.mstore (cell (b + Γ.length))]) m) := by
  rcases hs.correct h with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
  · refine .inl ⟨⟨σ.push (t := .mem R) (some r), List.prefix_refl _⟩, _, ?_, ?_,
      h.consMem r hcap, rfl, ?_⟩
    · simp only [TRun.declMem, MRhs.evalT, hr, bind, Except.bind, pure, Except.pure]
    · rw [run_append_ok hc]
      rfl
    · intro cursor hb ha
      exact ha.localWrite (b + Γ.length) (by omega) (by omega) _
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [TRun.declMem, MRhs.evalT, hr, bind, Except.bind]

theorem assignValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (dst : Idx Γ (.val p)) (e : Val C Γ p) (code : List Instr)
    (he : ValOutT p (e.evalT σ) (run code m) m) :
    ResultRepr L b frame F σ base m (TRun.assignLocal dst e σ)
      (run (code ++ [.mstore (cellOf b dst)]) m) := by
  rcases he with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · refine .inl ⟨⟨σ.setLocal dst v, List.prefix_refl _⟩,
      writeMachine m (cellOf b dst) w, ?_, ?_, h.setVal dst v w hw, rfl, ?_⟩
    · simp only [TRun.assignLocal, hv, bind, Except.bind]
      rfl
    · rw [run_append_ok hc]
      rfl
    · intro cursor hb ha
      exact ha.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
        (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) w
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [TRun.assignLocal, hv, bind, Except.bind]

theorem declareValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (e : Val C Γ p) (code : List Instr) (he : ValOutT p (e.evalT σ) (run code m) m)
    (hcap : b + (Γ.length + 1) ≤ frame) :
    ResultRepr L b frame (F.push (.val p) .ok) σ base m
      (TRun.declLocal p (some e) σ) (run (code ++ [.mstore (cell (b + Γ.length))]) m) := by
  rcases he with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · refine .inl ⟨⟨σ.push (t := .val p) v, List.prefix_refl _⟩,
      writeMachine m (cell (b + Γ.length)) w, ?_, ?_, h.consVal v w hw hcap, rfl, ?_⟩
    · simp only [TRun.declLocal, hv, bind, Except.bind]
      rfl
    · rw [run_append_ok hc]
      rfl
    · intro cursor hb ha
      exact ha.localWrite (b + Γ.length) (by omega) (by omega) w
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [TRun.declLocal, hv, bind, Except.bind]

end Solidity.Evm.Memory.Objects
