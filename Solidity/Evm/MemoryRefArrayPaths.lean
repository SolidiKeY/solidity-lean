import Solidity.Evm.MemoryRefArrayState
import Solidity.Evm.MemoryPaths

/-! Fallible typed pointer paths. Unlike `PtrFrag`, indexed reference paths
may revert; no success premise hides their bounds check. -/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

inductive RefPtrFrag (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {R : RefTy} → MPath C Γ (.ref R) → List Instr → Prop where
  | local {R : RefTy} (src : Idx Γ (.mem R)) (hm) :
      RefPtrFrag b F (.var src hm) [.mload (cellOf b src)]
  | field {s f : Name} {R : RefTy} (src : MPath C Γ (.ref (.struct s)))
      (hf : C.fieldType s f = some (.ref R)) (code : List Instr) (hs : RefPtrFrag b F src code) :
      RefPtrFrag b F (.loc (.field src f hf)) (code ++ readFieldCode (fieldOffset (structDef s) f))
  | index {R : RefTy} (src : MPath C Γ (.ref (.array (.ref R)))) (pointer : List Instr)
      (hs : RefPtrFrag b F src pointer) (i : Val C Γ .uint) (hi : valIn F i = true) :
      RefPtrFrag b F (.loc (.index .dyn src i)) (pointer ++ compileVal b i ++ readArrayStackCode)

structure CompiledRefPtr (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (p : MPath C Γ (.ref R)) where
  code : List Instr
  cert : RefPtrFrag b F p code

private def compileRefPtrAny (b : Nat) {Γ : Ctx} (F : Frag Γ) : {T : Ty} →
    (p : MPath C Γ T) → Option (match T with | .prim _ => PUnit | .ref _ => CompiledRefPtr b F p)
  | .prim _, _ => none
  | .ref _, .var src hm => some ⟨_, .local src hm⟩
  | .ref _, .loc (.field src _ hf) => do
    let parent ← compileRefPtrAny b F src
    pure ⟨_, .field src hf parent.code parent.cert⟩
  | .ref _, .loc (.index .dyn src i) => do
    let parent ← compileRefPtrAny b F src
    if hi : valIn F i = true then
      pure ⟨_, .index src parent.code parent.cert i hi⟩
    else none
  | .ref _, .loc (.index .fixed ..) => none
termination_by structural _T p => p

def compileRefPtr (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (p : MPath C Γ (.ref R)) : Option (CompiledRefPtr b F p) := compileRefPtrAny b F p

theorem RefPtrFrag.correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {R : RefTy} {p : MPath C Γ (.ref R)}
    {code : List Instr} (hp : RefPtrFrag b F p code) :
    RefOut base (p.mvalT σ) (run code m) m := by
  induction hp with
  | «local» src hm =>
    obtain ⟨r, hr, hc⟩ := h.state.pointers src
    refine .inl ⟨r, ?_, ?_⟩
    · simp only [MPath.mvalT, hr]
    · change Out.ok (m.push (m.mem (cellOf b src))) 0 = _
      rw [hc]
  | field src hf code hs ih =>
    rcases ih with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
    · refine .inl ⟨σ.heap.field r hf, ?_, ?_⟩
      · simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind, pure, Except.pure,
          Heap.readAddr, TRes.ofOpt]
      · rw [run_append_ok hc]
        exact RefFieldsRepr.readField h.state.refs h.state.structs r hf
    · exact .inr ⟨by simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind],
        run_append_revert hc⟩
  | index src pointer hs i hi ih =>
    rcases ih with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
    · have harr := h.arrays.arrays r
      simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind]
      rw [List.append_assoc, run_append_ok hc]
      rcases val_sim i (h.state.push (.val (base r.id))).core hi with
        ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
      · obtain ⟨a, ha, hva, rfl⟩ := hw.uint_inv
        have he : v = indexValue ⟨a, ha⟩ := Subtype.ext hva
        subst v
        rw [hv, run_append_ok hc]
        rw [readArrayStackCode, arrayStack_append_eq m (base r.id) ⟨a, ha⟩ _
          (σ.heap.len_dyn_lt r) harr.length, ← readArrayCode]
        exact harr.read ⟨a, ha⟩
      · rw [hv, run_append_revert hc]
        exact .inr ⟨rfl, rfl⟩
    · refine .inr ⟨?_, run_append_revert (run_append_revert hc)⟩
      simp only [MPath.mvalT, MLoc.addrT, hr, bind, Except.bind]

end Solidity.Evm.Memory
