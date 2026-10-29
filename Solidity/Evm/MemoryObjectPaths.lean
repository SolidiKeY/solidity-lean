import Solidity.Evm.MemoryObjectAllocator

/-! Fallible reference paths over both memory array kinds. Endpoints retain
their intrinsic reference type; fixed indexing uses the headerless layout. -/
namespace Solidity.Evm.Memory.Objects
open Semantics
variable {C : Contract}

inductive PtrFrag (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {R : RefTy} → MPath C Γ (.ref R) → List Instr → Prop where
  | local {R : RefTy} (src : Idx Γ (.mem R)) (hm) :
      PtrFrag b F (.var src hm) [.mload (cellOf b src)]
  | field {s f : Name} {R : RefTy} (src : MPath C Γ (.ref (.struct s)))
      (hf : C.fieldType s f = some (.ref R)) (code : List Instr) (hs : PtrFrag b F src code) :
      PtrFrag b F (.loc (.field src f hf)) (code ++ readFieldCode (fieldOffset (structDef s) f))
  | index {A R : RefTy} (a : ArrTy A (.ref R)) (src : MPath C Γ (.ref A))
      (pointer : List Instr) (hs : PtrFrag b F src pointer)
      (i : Val C Γ .uint) (hi : valIn F i = true) :
      PtrFrag b F (.loc (.index a src i)) (pointer ++ compileVal b i ++ readCode a)

structure CompiledPtr (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (p : MPath C Γ (.ref R)) where
  code : List Instr
  cert : PtrFrag b F p code

private def compilePtrAny (b : Nat) {Γ : Ctx} (F : Frag Γ) : {T : Ty} →
    (p : MPath C Γ T) → Option (match T with | .prim _ => PUnit | .ref _ => CompiledPtr b F p)
  | .prim _, _ => none
  | .ref _, .var src hm => some ⟨_, .local src hm⟩
  | .ref _, .loc (.field src _ hf) => do
    let parent ← compilePtrAny b F src
    pure ⟨_, .field src hf parent.code parent.cert⟩
  | .ref _, .loc (.index a src i) => do
    let parent ← compilePtrAny b F src
    if hi : valIn F i = true then
      pure ⟨_, .index a src parent.code parent.cert i hi⟩
    else none
termination_by structural _T p => p

def compilePtr (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (p : MPath C Γ (.ref R)) : Option (CompiledPtr b F p) := compilePtrAny b F p

theorem PtrFrag.correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy} {p : MPath C Γ (.ref R)}
    {code : List Instr} (hp : PtrFrag b F p code) :
    RefOut base (p.mvalT σ) (run code m) m := by
  induction hp with
  | «local» src hm =>
    obtain ⟨r, hr, hc⟩ := h.pointers src
    refine .inl ⟨r, ?_, ?_⟩
    · simp only [MPath.mvalT, hr]
    · change Out.ok (m.push (m.mem (cellOf b src))) 0 = _
      rw [hc]
  | field src hf code hs ih =>
    rcases ih with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
    · refine .inl ⟨σ.heap.field r hf, ?_, ?_⟩
      · simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind,
          pure, Except.pure, Heap.readAddr, TRes.ofOpt]
      · rw [run_append_ok hc]
        exact RefFieldsRepr.readField h.heap.refs h.heap.structHeap r hf
    · exact .inr ⟨by simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind],
        run_append_revert hc⟩
  | index a src pointer hs i hi ih =>
    rcases ih with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
    · have harr := h.heap.arrays a r
      simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind]
      rw [List.append_assoc, run_append_ok hc]
      rcases val_sim i (h.legacy.push (.val (base r.id))).core hi with
        ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
      · obtain ⟨n, hn, hvn, rfl⟩ := hw.uint_inv
        have he : v = indexValue ⟨n, hn⟩ := Subtype.ext hvn
        subst v
        rw [hv, run_append_ok hc]
        exact (harr.read ⟨n, hn⟩).reference
      · rw [hv, run_append_revert hc]
        exact .inr ⟨rfl, rfl⟩
    · refine .inr ⟨?_, run_append_revert (run_append_revert hc)⟩
      simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind]

theorem PtrFrag.run_of_eval {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : PtrFrag b F src code)
    {r : HRef σ.H R} (hr : src.mvalT σ = .ok r) :
    run code m = .ok (m.push (.val (base r.id))) 0 := by
  rcases hs.correct h with ⟨q, hq, hc⟩ | ⟨hq, _⟩
  · cases Except.ok.inj (hq.symm.trans hr)
    exact hc
  · cases hq.symm.trans hr

/-- The read may fail at any parent or element bound, on both evaluators. -/
theorem PtrFrag.readPrimitive {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {A : RefTy} {p : PrimTy}
    {src : MPath C Γ (.ref A)} {code : List Instr} (hs : PtrFrag b F src code)
    (a : ArrTy A (.prim p)) (i : Val C Γ .uint) (hi : valIn F i = true) :
    ValOutT p ((Val.readMem (.index a src i)).evalT σ)
      (run (code ++ compileVal b i ++ readCode a) m) m := by
  rcases hs.correct h with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
  · have harr := h.heap.arrays a r
    simp only [Val.evalT, MLoc.addrT, hr, bind, Except.bind]
    rw [List.append_assoc, run_append_ok hc]
    rcases val_sim i (h.legacy.push (.val (base r.id))).core hi with
      ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
    · obtain ⟨n, hn, hvn, rfl⟩ := hw.uint_inv
      have he : v = indexValue ⟨n, hn⟩ := Subtype.ext hvn
      subst v
      rw [hv, run_append_ok hc]
      exact (harr.read ⟨n, hn⟩).primitive
    · rw [hv, run_append_revert hc]
      exact .inr ⟨rfl, rfl⟩
  · refine .inr ⟨?_, run_append_revert (run_append_revert hc)⟩
    simp only [Val.evalT, MLoc.addrT, hr, bind, Except.bind]

theorem PtrFrag.readField {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    {src : MPath C Γ (.ref (.struct s))} {code : List Instr} (hs : PtrFrag b F src code)
    (hf : C.fieldType s f = some (.prim p)) :
    ValOutT p ((Val.readMem (.field src f hf)).evalT σ)
      (run (code ++ readFieldCode (fieldOffset (structDef s) f)) m) m := by
  rcases hs.correct h with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
  · simp only [Val.evalT, MLoc.addrT, hr, bind, Except.bind, pure, Except.pure,
      Heap.readAddr, TRes.ofOpt]
    rw [run_append_ok hc]
    exact readField_correct (h.heap.structs r) hf
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Val.evalT, MLoc.addrT, hr, bind, Except.bind]

theorem PtrFrag.length {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {E : Ty}
    {src : MPath C Γ (.ref (.array E))} {code : List Instr} (hs : PtrFrag b F src code) :
    ValOutT .uint ((Val.mlen src rfl).evalT σ) (run (code ++ [.mloadAt]) m) m := by
  rcases hs.correct h with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
  · refine .inl ⟨σ.heap.lenU r, .val (wmod (σ.heap.len r .dyn)), ?_, ?_, ?_⟩
    · simp only [Val.evalT, hr, bind, Except.bind]
      rfl
    · have hn : σ.heap.len r .dyn < W := σ.heap.len_dyn_lt r
      exact ReprV.uint_of (by
        simp only [Heap.lenU, Solidity.lenU, wmod_def, Nat.mod_eq_of_lt hn])
    · rw [run_append_ok hc]
      simp only [run, exec_cons_zero, Instr.step, Machine.next, Out.ok_bind,
        (h.heap.arrays .dyn r).length rfl, exec_nil, Machine.push]
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Val.evalT, hr, bind, Except.bind]

end Solidity.Evm.Memory.Objects
