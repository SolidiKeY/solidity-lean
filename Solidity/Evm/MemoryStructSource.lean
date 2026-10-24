import Solidity.Evm.MemoryLocals

/-!
# Scoped primitive struct fields

Source field accesses use initialized typed local pointers. Their target
instructions share the array compiler's state and allocator relations, so
mixed writes preserve aliases, independent objects and local frames.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

theorem StateRepr.setStruct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    (r : HRef σ.H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StateRepr L b frame F (σ.withHeap (σ.heap.setField r hf v)) base
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  have hc := h.core.congrMem (mem := upd m.mem ((base r.id).val + fieldOffset (structDef s) f) w)
    (fun l _ hl => h.structs.write_below r hf w l (Nat.lt_of_lt_of_le hl h.locals))
  refine ⟨⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩,
    h.heap.structWrite h.separated r hf v w, ?_, h.locals,
    h.structs.set r hf v w hw, StructArraySeparated.setStruct h.separated r hf v,
    RefFieldsRepr.setPrimitive h.refs h.structs r hf v w⟩
  intro R j
  obtain ⟨q, hq, hm⟩ := h.pointers j
  refine ⟨q, hq, ?_⟩
  rw [h.structs.write_below r hf w (lvl b j) (Nat.lt_of_lt_of_le (lvl_lt b j) h.locals)]
  exact hm

def readLocalFieldCode {Γ : Ctx} {s : Name} (b : Nat)
    (src : Idx Γ (.mem (.struct s))) (f : Name) : List Instr :=
  [.mload (cellOf b src)] ++ readFieldCode (fieldOffset (structDef s) f)

theorem readLocalField_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    (src : Idx Γ (.mem (.struct s))) (hmf : (Ty.ref (.struct s)).mapFree = true)
    (hf : C.fieldType s f = some (.prim p)) :
    ValOutT p ((Val.readMem (.field (.var src hmf) f hf)).evalT σ)
      (run (readLocalFieldCode b src f) m) m := by
  obtain ⟨r, hr, hm⟩ := h.pointers src
  simp only [Val.evalT, MLoc.addrT, MPath.mvalT, hr, bind, Except.bind,
    pure, Except.pure, Heap.readAddr, TRes.ofOpt]
  rw [readLocalFieldCode, run_append_ok (show run [.mload (cellOf b src)] m =
      .ok (m.push (.val (base r.id))) 0 by
    change Out.ok (m.push (m.mem (cellOf b src))) 0 = _
    rw [hm])]
  exact readField_correct (h.structs.objects r) hf

def writeLocalFieldCode {Γ : Ctx} {s : Name} (b : Nat)
    (dst : Idx Γ (.mem (.struct s))) (f : Name) (value : List Instr) : List Instr :=
  value ++ [.mload (cellOf b dst)] ++ writeFieldCode (fieldOffset (structDef s) f)

theorem writeLocalField_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    (dst : Idx Γ (.mem (.struct s))) (hmf : (Ty.ref (.struct s)).mapFree = true)
    (hf : C.fieldType s f = some (.prim p)) (v : Val C Γ p) (value : List Instr)
    (hv : ValOutT p (v.evalT σ) (run value m) m) :
    ResultRepr L b frame F σ base m (TRun.assignMem (.field (.var dst hmf) f hf) (.val v) σ)
      (run (writeLocalFieldCode b dst f value) m) := by
  obtain ⟨r, hr, hm⟩ := h.pointers dst
  simp only [ResultRepr, TRun.assignMem, MSrc.mvalT, MLoc.addrT, MPath.mvalT,
    hr, bind, Except.bind]
  rw [writeLocalFieldCode, List.append_assoc]
  rcases hv with ⟨x, w, hx, hw, hc⟩ | ⟨hx, hc⟩
  · rw [hx, run_append_ok hc]
    rw [run_append_ok (show run [.mload (cellOf b dst)] (m.push w) =
        .ok ((m.push w).push (.val (base r.id))) 0 by
      change Out.ok ((m.push w).push (m.mem (cellOf b dst))) 0 = _
      rw [hm])]
    rw [(writeField_correct (h.structs.objects r) hf x w hw).2.1]
    refine .inl ⟨⟨σ.withHeap (σ.heap.setField r hf x), List.prefix_refl _⟩, _, ?_, rfl,
      h.setStruct r hf x w hw, rfl, fun _ _ ha => ha.setStruct r hf x w hw⟩
    rfl
  · exact .inr ⟨by rw [hx], run_append_revert hc⟩

end Solidity.Evm.Memory
