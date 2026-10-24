import Solidity.Evm.MemoryRefWrite
import Solidity.Evm.MemoryStructDefault

/-!
# Fresh defaults for reference-valued memory members

The interpreter first identifies the parent field, then allocates a fresh
default child and installs its weakened reference. Older aliases keep their
previous objects. These source equalities precede the matching allocator and
pointer-store simulation.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

private theorem adopt_clear_alloc {Γ : Ctx} {s f : Name} {R : RefTy} (σ : State C Γ)
    (r : HRef σ.H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref R))
    (o : MObj σ.H R) (g : Grown σ.H (MVal · (.ref R)))
    (hg : g = Grown.alloc ⟨List.prefix_refl _, σ.heap, o⟩)
    (e : σ.H <+: (σ.adopt g).1.H) :
    (match (σ.adopt g).1.heap.writeAddr ((MAddr.field r hf).wk e) g.val with
      | some hp => .ok ⟨(σ.adopt g).1.withHeap hp, e⟩
      | none => .error .revert : TRes (Solidity.Out C σ.H Γ)) =
      .ok ⟨(σ.alloc o).1.withHeap ((σ.alloc o).1.heap.setField
        (r.wk (List.prefix_append _ _)) hf (σ.alloc o).2), List.prefix_append _ _⟩ := by
  subst hg
  rfl

theorem clearStructField {Γ : Ctx} (σ : State C Γ) {s t f : Name}
    (r : HRef σ.H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref (.struct t)))
    (hp : primitiveMembers (structDef t) = true) (hm : (Ty.ref (.struct t)).mapFree = true) :
    TRun.clearT σ (.field r hf) hm =
      .ok ⟨(σ.alloc (R := .struct t) (defaultFields (structDef t) hp)).1.withHeap
        ((σ.alloc (R := .struct t) (defaultFields (structDef t) hp)).1.heap.setField
          (r.wk (List.prefix_append _ _)) hf
          (σ.alloc (R := .struct t) (defaultFields (structDef t) hp)).2), List.prefix_append _ _⟩ := by
  have he := defaultStruct_alloc σ.heap hp hm
  simp only [TRun.clearT, State.allocDefaultG, State.grow]
  with_unfolding_all exact adopt_clear_alloc σ r hf _ _ he _

theorem defaultArray_alloc {H : HTy} (hp : Heap H) (p : PrimTy) :
    hp.allocDefault (.array (.prim p)) rfl =
      Grown.alloc ⟨List.prefix_refl _, hp, defaultArray p (wmod 0)⟩ := by
  with_unfolding_all rfl

theorem clearArrayField {Γ : Ctx} (σ : State C Γ) {s f : Name} (p : PrimTy)
    (r : HRef σ.H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref (.array (.prim p)))) :
    TRun.clearT σ (.field r hf) rfl =
      .ok ⟨(σ.alloc (defaultArray p (wmod 0))).1.withHeap
        ((σ.alloc (defaultArray p (wmod 0))).1.heap.setField
          (r.wk (List.prefix_append _ _)) hf
          (σ.alloc (defaultArray p (wmod 0))).2), List.prefix_append _ _⟩ := by
  have he := defaultArray_alloc σ.heap p
  simp only [TRun.clearT, State.allocDefaultG, State.grow]
  with_unfolding_all exact adopt_clear_alloc σ r hf _ _ he _

def clearReferenceCode (pointer allocation : List Instr) (offset : Nat) : List Instr :=
  pointer ++ (allocation ++ ([.swap 1] ++ writeFieldCode offset))

/-- Keep the resolved parent below the allocator's result, then store that child. -/
theorem clearReference_run (m allocated : Machine) (parent child : Fin W) (offset : Nat)
    (pointer allocation : List Instr)
    (hp : run pointer m = .ok (m.push (.val parent)) 0)
    (ha : run allocation (m.push (.val parent)) =
      .ok ((allocated.push (.val parent)).push (.val child)) 0)
    (hb : parent.val + offset < W) :
    run (clearReferenceCode pointer allocation offset) m =
      .ok (writeMachine allocated (parent.val + offset) (.val child)) 0 := by
  rw [clearReferenceCode, run_append_ok hp, run_append_ok ha,
    run_append_ok (show run [.swap 1] ((allocated.push (.val parent)).push (.val child)) =
      .ok ((allocated.push (.val child)).push (.val parent)) 0 by rfl)]
  exact writeFieldWord_run allocated parent offset (.val child) hb

theorem deleteStructField_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s t f : Name} {src : MPath C Γ (.ref (.struct s))} {pointer : List Instr}
    (hs : PtrFrag b src pointer) (r : HRef σ.H (.struct s)) (hr : src.mvalT σ = .ok r)
    (hf : C.fieldType s f = some (.ref (.struct t)))
    (hp : primitiveMembers (structDef t) = true) (hm : (Ty.ref (.struct t)).mapFree = true)
    (hspace : cursor.val + structAllocationSize t < W) :
    let a := σ.alloc (R := .struct t) (defaultFields (structDef t) hp)
    let σ' := a.1.withHeap (a.1.heap.setField (r.wk (List.prefix_append _ _)) hf a.2)
    let base' := upd base σ.H.length cursor
    let allocated := allocateStructMachine m cursor (structAllocationSize t)
    let m' := writeMachine allocated ((base r.id).val + fieldOffset (structDef s) f) (.val cursor)
    TRun.deleteMem (.loc (.field src f hf)) σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (clearReferenceCode pointer (allocateStructCode (structAllocationSize t))
        (fieldOffset (structDef s) f)) m = .ok m' 0 ∧
      StateRepr L b frame F σ' base' m' ∧
      StructAllocatorRepr σ'.heap base' frame ⟨cursor.val + structAllocationSize t, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simp only [TRun.deleteMem, MLoc.addrT, hr, bind, Except.bind, pure, Except.pure]
    exact clearStructField σ r hf hp hm
  · apply clearReference_run m _ (base r.id) cursor _ pointer _ (hs.run_of_eval h hr)
    · exact allocateStruct_run (m.push (.val (base r.id))) cursor _ ha.arrays.free.cell
    · have ho := fieldOffset_bound hf
      have he := (h.structs.objects r).space
      omega
  · have hid : (σ.alloc (R := .struct t) (defaultFields (structDef t) hp)).2.id = σ.H.length := rfl
    simpa only [HRef.wk, allocationBase_old base cursor r, hid, upd_same] using
      (h.allocateStruct ha hb hp hm hspace).setReference (r.wk (List.prefix_append _ _)) hf
        (σ.alloc (R := .struct t) (defaultFields (structDef t) hp)).2
  · have hid : (σ.alloc (R := .struct t) (defaultFields (structDef t) hp)).2.id = σ.H.length := rfl
    simpa only [HRef.wk, allocationBase_old base cursor r, hid, upd_same] using
      (ha.reserveStruct (s := t) (defaultFields (structDef t) hp)
        (defaultFields_defaults σ.heap hp hm) (structAllocationSize t) (Nat.le_max_right _ _) hspace).setReference
        (r.wk (List.prefix_append _ _)) hf (σ.alloc (R := .struct t) (defaultFields (structDef t) hp)).2

theorem deleteArrayField_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s f : Name} {p : PrimTy} {src : MPath C Γ (.ref (.struct s))} {pointer : List Instr}
    (hs : PtrFrag b src pointer) (r : HRef σ.H (.struct s)) (hr : src.mvalT σ = .ok r)
    (hf : C.fieldType s f = some (.ref (.array (.prim p))))
    (hspace : cursor.val + 1 < W) :
    let a := σ.alloc (defaultArray p (wmod 0))
    let σ' := a.1.withHeap (a.1.heap.setField (r.wk (List.prefix_append _ _)) hf a.2)
    let base' := upd base σ.H.length cursor
    let allocated := allocateMachine m cursor (wmod 0)
    let m' := writeMachine allocated ((base r.id).val + fieldOffset (structDef s) f) (.val cursor)
    TRun.deleteMem (.loc (.field src f hf)) σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (clearReferenceCode pointer ([.push w[0]] ++ allocateArrayCode)
        (fieldOffset (structDef s) f)) m = .ok m' 0 ∧
      StateRepr L b frame F σ' base' m' ∧
      StructAllocatorRepr σ'.heap base' frame ⟨cursor.val + 1, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simp only [TRun.deleteMem, MLoc.addrT, hr, bind, Except.bind, pure, Except.pure]
    exact clearArrayField σ p r hf
  · apply clearReference_run m _ (base r.id) cursor _ pointer _ (hs.run_of_eval h hr)
    · rw [run_append_ok (show run [.push w[0]] (m.push (.val (base r.id))) =
        .ok ((m.push (.val (base r.id))).push (.val (wmod 0))) 0 by rfl)]
      exact allocateArray_run (m.push (.val (base r.id))) cursor (wmod 0) ha.arrays.free.cell
    · have ho := fieldOffset_bound hf
      have he := (h.structs.objects r).space
      omega
  · have hid : (σ.alloc (defaultArray p (wmod 0))).2.id = σ.H.length := rfl
    simpa only [HRef.wk, allocationBase_old base cursor r, hid, upd_same] using
      (h.allocate ha hb p (wmod 0) hspace).setReference (r.wk (List.prefix_append _ _)) hf
        (σ.alloc (defaultArray p (wmod 0))).2
  · have hid : (σ.alloc (defaultArray p (wmod 0))).2.id = σ.H.length := rfl
    simpa only [HRef.wk, allocationBase_old base cursor r, hid, upd_same] using
      (ha.allocateArray p (wmod 0) hspace).setReference
        (r.wk (List.prefix_append _ _)) hf (σ.alloc (defaultArray p (wmod 0))).2

end Solidity.Evm.Memory
