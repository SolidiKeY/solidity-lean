import Solidity.Evm.MemoryStructSource

/-!
# Typed pointer paths through memory structs

Path certificates follow initialized locals and reference-valued struct
members. Each pointer word denotes the source path's actual heap identity
under the shared address map; following it neither changes memory nor loses
the types of its endpoints. Array-element reference paths remain separate.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

inductive PtrFrag (b : Nat) {Γ : Ctx} : {R : RefTy} → MPath C Γ (.ref R) → List Instr → Prop where
  | local {R : RefTy} (src : Idx Γ (.mem R)) (hm) :
      PtrFrag b (.var src hm) [.mload (cellOf b src)]
  | field {s f : Name} {R : RefTy} (src : MPath C Γ (.ref (.struct s)))
      (hf : C.fieldType s f = some (.ref R)) (code : List Instr) (hs : PtrFrag b src code) :
      PtrFrag b (.loc (.field src f hf)) (code ++ readFieldCode (fieldOffset (structDef s) f))

structure CompiledPtr (b : Nat) {Γ : Ctx} {R : RefTy} (p : MPath C Γ (.ref R)) where
  code : List Instr
  cert : PtrFrag b p code

/-- Keeping the full endpoint index variable permits structural recursion.
A reference-only index makes Lean choose well-founded recursion, whose
opaque accessibility proof prevents kernel reduction of acceptance checks. -/
private def compilePtrAny (b : Nat) {Γ : Ctx} : {T : Ty} →
    (p : MPath C Γ T) → Option (match T with | .prim _ => PUnit | .ref _ => CompiledPtr b p)
  | .prim _, _ => none
  | .ref _, .var src hm => some ⟨_, .local src hm⟩
  | .ref _, .loc (.field src _ hf) => do
    let parent ← compilePtrAny b src
    pure ⟨_, .field src hf parent.code parent.cert⟩
  | .ref _, .loc (.index ..) => none
termination_by structural _T p => p

def compilePtr (b : Nat) {Γ : Ctx} {R : RefTy} (p : MPath C Γ (.ref R)) :
    Option (CompiledPtr b p) := compilePtrAny b p

theorem PtrFrag.correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy} {p : MPath C Γ (.ref R)}
    {code : List Instr} (hp : PtrFrag b p code) :
    ∃ r, p.mvalT σ = .ok r ∧ run code m = .ok (m.push (.val (base r.id))) 0 := by
  induction hp with
  | «local» src hm =>
    obtain ⟨r, hr, hc⟩ := h.pointers src
    refine ⟨r, ?_, ?_⟩
    · simp only [MPath.mvalT, hr]
    · change Out.ok (m.push (m.mem (cellOf b src))) 0 = _
      rw [hc]
  | field src hf code hs ih =>
    obtain ⟨r, hr, hc⟩ := ih
    refine ⟨σ.heap.field r hf, ?_, ?_⟩
    · simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind, pure, Except.pure,
        Heap.readAddr, TRes.ofOpt]
    · rw [run_append_ok hc]
      exact RefFieldsRepr.readField h.refs h.structs r hf

theorem PtrFrag.readPrimitive {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    {src : MPath C Γ (.ref (.struct s))} {code : List Instr} (hs : PtrFrag b src code)
    (hf : C.fieldType s f = some (.prim p)) :
    ValOutT p ((Val.readMem (.field src f hf)).evalT σ)
      (run (code ++ readFieldCode (fieldOffset (structDef s) f)) m) m := by
  obtain ⟨r, hr, hc⟩ := hs.correct h
  simp only [Val.evalT, MLoc.addrT, hr, bind, Except.bind,
    pure, Except.pure, Heap.readAddr, TRes.ofOpt]
  rw [run_append_ok hc]
  exact readField_correct (h.structs.objects r) hf

theorem PtrFrag.run_of_eval {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : PtrFrag b src code)
    {r : HRef σ.H R} (hr : src.mvalT σ = .ok r) :
    run code m = .ok (m.push (.val (base r.id))) 0 := by
  obtain ⟨q, hq, hc⟩ := hs.correct h
  have he : q = r := Except.ok.inj (hq.symm.trans hr)
  subst q
  exact hc

theorem PtrFrag.writePrimitive {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    {src : MPath C Γ (.ref (.struct s))} {pointer : List Instr} (hs : PtrFrag b src pointer)
    (hf : C.fieldType s f = some (.prim p)) (v : Val C Γ p) (value : List Instr)
    (hv : ValOutT p (v.evalT σ) (run value m) m) :
    ResultRepr L b frame F σ base m (TRun.assignMem (.field src f hf) (.val v) σ)
      (run (value ++ pointer ++ writeFieldCode (fieldOffset (structDef s) f)) m) := by
  obtain ⟨r, hr, _⟩ := hs.correct h
  simp only [ResultRepr, TRun.assignMem, MSrc.mvalT, MLoc.addrT, hr, bind, Except.bind]
  rw [List.append_assoc]
  rcases hv with ⟨x, w, hx, hw, hc⟩ | ⟨hx, hc⟩
  · rw [hx, run_append_ok hc, run_append_ok (hs.run_of_eval (h.push w) hr)]
    rw [(writeField_correct (h.structs.objects r) hf x w hw).2.1]
    refine .inl ⟨⟨σ.withHeap (σ.heap.setField r hf x), List.prefix_refl _⟩, _, ?_, rfl,
      h.setStruct r hf x w hw, rfl, fun _ _ ha => ha.setStruct r hf x w hw⟩
    rfl
  · exact .inr ⟨by rw [hx], run_append_revert hc⟩

theorem PtrFrag.length {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    {src : MPath C Γ (.ref (.array (.prim p)))} {code : List Instr} (hs : PtrFrag b src code) :
    ValOutT .uint ((Val.mlen src rfl).evalT σ) (run (code ++ [.mloadAt]) m) m := by
  obtain ⟨r, hr, hc⟩ := hs.correct h
  refine .inl ⟨σ.heap.lenU r, .val (wmod (σ.heap.len r .dyn)), ?_, ?_, ?_⟩
  · simp only [Val.evalT, hr, bind, Except.bind]
    rfl
  · have hn : σ.heap.len r .dyn < W := σ.heap.len_dyn_lt r
    exact ReprV.uint_of (by
      simp only [Heap.lenU, Solidity.lenU, wmod_def, Nat.mod_eq_of_lt hn])
  · rw [run_append_ok hc]
    simp only [run, exec_cons_zero, Instr.step, Machine.next,
      Out.ok_bind, (h.heap.arrays r).length, exec_nil, Machine.push]

theorem PtrFrag.readArray {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    {src : MPath C Γ (.ref (.array (.prim p)))} {code : List Instr} (hs : PtrFrag b src code)
    (i : Val C Γ .uint) (index : List Instr)
    (hi : ∀ {m' : Machine}, StateRepr L b frame F σ base m' →
      ValOutT .uint (i.evalT σ) (run index m') m') :
    ValOutT p ((Val.readMem (.index .dyn src i)).evalT σ)
      (run (code ++ index ++ readArrayStackCode) m) m := by
  obtain ⟨r, hr, hc⟩ := hs.correct h
  have harr := h.heap.arrays r
  simp only [Val.evalT, MLoc.addrT, hr, bind, Except.bind]
  rw [List.append_assoc, run_append_ok hc]
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

theorem PtrFrag.rebind {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : PtrFrag b src code)
    (dst : Idx Γ (.mem R)) :
    ResultRepr L b frame F σ base m (TRun.rebindMem dst (.alias src) σ)
      (run (code ++ [.mstore (cellOf b dst)]) m) := by
  obtain ⟨r, hr, hc⟩ := hs.correct h
  refine .inl ⟨⟨σ.setLocal dst (some r), List.prefix_refl _⟩, _, ?_, ?_, h.setMem dst r, rfl, ?_⟩
  · simp only [TRun.rebindMem, MRhs.evalT, hr, bind, Except.bind, pure, Except.pure]
  · rw [run_append_ok hc]
    rfl
  · exact fun _ hb ha => ha.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _

theorem PtrFrag.writeArray {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    {src : MPath C Γ (.ref (.array (.prim p)))} {pointer : List Instr} (hs : PtrFrag b src pointer)
    (i : Val C Γ .uint) (v : Val C Γ p) (index value : List Instr)
    (hi : ∀ {m' : Machine}, StateRepr L b frame F σ base m' →
      ValOutT .uint (i.evalT σ) (run index m') m')
    (hv : ValOutT p (v.evalT σ) (run value m) m) :
    ResultRepr L b frame F σ base m (TRun.assignMem (.index .dyn src i) (.val v) σ)
      (run (value ++ pointer ++ index ++ writeArrayStackCode) m) := by
  obtain ⟨r, hr, _⟩ := hs.correct h
  have harr := h.heap.arrays r
  simp only [ResultRepr, TRun.assignMem, MSrc.mvalT, MLoc.addrT, hr, bind, Except.bind]
  rw [List.append_assoc, List.append_assoc]
  rcases hv with ⟨x, w, hx, hw, hc⟩ | ⟨hx, hc⟩
  · rw [hx, run_append_ok hc, run_append_ok (hs.run_of_eval (h.push w) hr)]
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
        have haddr : (base r.id).val + 1 + a < W := by have hs := harr.space; omega
        rw [writeArrayCode, run_append_ok hc]
        have hrun : run [Instr.mstoreAt]
            ((m.push w).push (.val (wmod ((base r.id).val + 1 + a)))) =
            .ok (writeMachine m ((base r.id).val + 1 + a) w) 0 := by
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
        rw [if_neg (show ¬ a < (MObj.elems .dyn (σ.heap.get r)).length from hin)]
        rfl
    · rw [hiv, run_append_revert hic]
      exact .inr ⟨rfl, rfl⟩
  · rw [hx, run_append_revert hc]
    exact .inr ⟨rfl, rfl⟩

theorem PtrFrag.declareAlias {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : PtrFrag b src code)
    (hm : (Ty.ref R).mapFree = true) (hcap : b + (Γ.length + 1) ≤ frame) :
    ResultRepr L b frame (F.push (.mem R) .ok) σ base m (TRun.declMem R (some (.alias src)) hm σ)
      (run (code ++ [.mstore (cell (b + Γ.length))]) m) := by
  obtain ⟨r, hr, hc⟩ := hs.correct h
  refine .inl ⟨⟨σ.push (t := .mem R) (some r), List.prefix_refl _⟩, _, ?_, ?_, h.consMem r hcap, rfl, ?_⟩
  · simp only [TRun.declMem, MRhs.evalT, hr, bind, Except.bind, pure, Except.pure]
  · rw [run_append_ok hc]
    rfl
  · exact fun _ hb ha => ha.localWrite (b + Γ.length) (by omega) (by omega) _

end Solidity.Evm.Memory
