import Solidity.Evm.MemoryStructSource
import Solidity.Evm.MemoryAllocSource
import Solidity.Typing.Values

/-!
# Source allocation of primitive structs

Primitive members need one fresh object and no recursive child allocation.
The source default-copy fold is identified with that actual typed object;
its target reservation has no header and uses the allocator's zero tail.
An empty model struct reserves one padding cell so allocation always carries
an allocator premise, even though it has no field cells.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

def primitiveMembers : List (Name × Ty) → Bool
  | [] => true
  | (_, .prim _) :: fs => primitiveMembers fs
  | (_, .ref _) :: _ => false

theorem primitiveMembers_noRef {fs : List (Name × Ty)}
    (h : primitiveMembers fs = true) {f : Name} {R : RefTy}
    (hf : lookupBy f fs = some (.ref R)) : False := by
  induction fs with
  | nil => cases hf
  | cons ft fs ih =>
    obtain ⟨g, T⟩ := ft
    cases T with
    | prim p =>
      by_cases he : f = g
      · cases SFields.lookupBy_cons_pos he hf
      · exact ih h (SFields.lookupBy_cons_neg he hf)
    | ref R => cases h

def defaultFields {H : HTy} : (fs : List (Name × Ty)) →
    primitiveMembers fs = true → MFields H fs
  | [], _ => ()
  | (_, .prim p) :: fs, h => (p.dflt, defaultFields fs h)
  | (_, .ref _) :: _, h => by cases h

private theorem defaultFields_cons_eq {H : HTy} (hp : Heap H) (f : Name) (p : PrimTy)
    (fs : List (Name × Ty)) (h : primitiveMembers fs = true) (g : Grown H (MFields · fs))
    (hg : g = ⟨List.prefix_refl H, hp, defaultFields fs h⟩) :
    (⟨(List.prefix_refl H).trans g.ext, g.heap, (MVal.wk g.ext (.prim p) p.dflt, g.val)⟩ :
      Grown H (MFields · ((f, .prim p) :: fs))) =
      ⟨List.prefix_refl H, hp, defaultFields ((f, .prim p) :: fs) h⟩ := by
  subst hg
  rfl

private theorem defaultFields_copy {H : HTy} (hp : Heap H) (fs : List (Name × Ty))
    (h : primitiveMembers fs = true) (hm : ∀ fT ∈ fs, fT.2.mapFree = true) :
    (SFields.dflt fs).copyStToM hp hm = ⟨List.prefix_refl H, hp, defaultFields fs h⟩ := by
  induction fs with
  | nil => rw [SFields.dflt, SFields.copyStToM_nil]; rfl
  | cons fT fs ih =>
    obtain ⟨f, T⟩ := fT
    cases T with
    | prim p =>
      rw [SFields.dflt, SFields.copyStToM_cons, SVal.dflt_prim, SVal.copyStToM_prim]
      with_unfolding_all exact defaultFields_cons_eq hp f p fs h _ (ih h _)
    | ref R => cases h

/-- Primitive defaults in the actual copied object satisfy the target field relation. -/
theorem defaultFields_defaults {H : HTy} (hp : Heap H) {s : Name}
    (h : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    StructDefaults (H := H) (s := s) (defaultFields (structDef s) h) := by
  intro f p hf
  have hh := SFields.copyStToM_get_prim hp (SFields.dflt (structDef s))
    (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using hm)) hf
  rw [defaultFields_copy hp _ h] at hh
  simpa only [SFields.dflt_get, SVal.dflt_prim, SVal.view_prim] using hh

/-- Default construction grows by exactly one primitive struct object. -/
theorem defaultStruct_alloc {H : HTy} (hp : Heap H) {s : Name}
    (h : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    hp.allocDefault (.struct s) hm =
      Grown.alloc (R := .struct s) ⟨List.prefix_refl H, hp, defaultFields (structDef s) h⟩ := by
  rw [Heap.allocDefault, SVal.dflt_struct, SVal.copyStToM_struct, defaultFields_copy hp _ h]

/-- The scoped declaration adopts that fresh identity and binds its pointer. -/
theorem defaultStruct_decl {Γ : Ctx} (σ : State C Γ) {s : Name}
    (h : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    TRun.declMem (.struct s) none hm σ =
      .ok ⟨σ.allocPush (R := .struct s) (defaultFields (structDef s) h), List.prefix_append _ _⟩ := by
  have he := defaultStruct_alloc σ.heap h hm
  simp only [TRun.declMem, State.allocDefaultG, State.grow, pure, Except.pure]
  with_unfolding_all exact State.adopt_push_alloc σ _ _ he _ _

def structAllocationSize (s : Name) : Nat := max 1 (structDef s).length

/-- Source heap growth retains every older typed local and target pointer. -/
theorem StateRepr.allocateStruct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s : Name} (hp : primitiveMembers (structDef s) = true)
    (hmf : (Ty.ref (.struct s)).mapFree = true)
    (hspace : cursor.val + structAllocationSize s < W) :
    StateRepr L b frame F (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).1
      (upd base σ.H.length cursor) (allocateStructMachine m cursor (structAllocationSize s)) := by
  have hm : ∀ l, b ≤ l → l < b + Γ.length →
      (allocateStructMachine m cursor (structAllocationSize s)).mem (cell l) = m.mem (cell l) := by
    intro l hl _
    exact allocateStructMachine_other m cursor _ l (by omega)
  have hg := ha.reserveStruct (s := s) (defaultFields (structDef s) hp)
    (defaultFields_defaults σ.heap hp hmf) (structAllocationSize s) (Nat.le_max_right _ _) hspace
  refine ⟨?_, hg.arrays.heap, ?_, h.locals, hg.structs, hg.separated,
    RefFieldsRepr.allocateStruct h.refs ha _ (fun hf => primitiveMembers_noRef hp hf) _⟩
  · have hc := (h.core.congrMem hm).congrLook
      (fun i => Look.ofTEnv_wk (List.prefix_append σ.H [.struct s]) σ.env i)
    exact ⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩
  · intro R i
    obtain ⟨r, hr, hm'⟩ := h.pointers i
    refine ⟨r.wk (List.prefix_append _ _), ?_, ?_⟩
    · change TEnv.get i (TEnv.wk _ Γ σ.env) = _
      rw [TEnv.get_wk, hr]
      rfl
    · change (allocateStructMachine m cursor (structAllocationSize s)).mem (cell (lvl b i)) =
        .val (upd base σ.H.length cursor r.id)
      rw [hm _ (le_lvl b i) (lvl_lt b i), allocationBase_old base cursor r]
      exact hm'

def declareStructCode {Γ : Ctx} (b : Nat) (s : Name) : List Instr :=
  allocateStructCode (structAllocationSize s) ++ [.mstore (cell (b + Γ.length))]

private theorem adopt_delete_alloc {Γ : Ctx} {R : RefTy} (σ : State C Γ)
    (dst : Idx Γ (.mem R)) (o : MObj σ.H R) (g : Grown σ.H (MVal · (.ref R)))
    (hg : g = Grown.alloc ⟨List.prefix_refl _, σ.heap, o⟩)
    (e : σ.H <+: (σ.adopt g).1.H) :
    (Except.ok ⟨(σ.adopt g).1.setLocal dst (some g.val), e⟩ : TRes (Solidity.Out C σ.H Γ)) =
      .ok ⟨(σ.alloc o).1.setLocal dst (some (σ.alloc o).2), List.prefix_append _ _⟩ := by
  subst hg
  rfl

/-- Whole-local deletion adopts a fresh default object; older aliases keep theirs. -/
theorem defaultStruct_delete {Γ : Ctx} (σ : State C Γ) {s : Name}
    (dst : Idx Γ (.mem (.struct s)))
    (hp : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    TRun.deleteMem (.var dst hm) σ =
      .ok ⟨(σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).1.setLocal dst
        (some (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).2),
        List.prefix_append _ _⟩ := by
  have he := defaultStruct_alloc σ.heap hp hm
  simp only [TRun.deleteMem, State.allocDefaultG, State.grow, pure, Except.pure]
  with_unfolding_all exact adopt_delete_alloc σ dst _ _ he _

def deleteStructCode {Γ : Ctx} {s : Name} (b : Nat)
    (dst : Idx Γ (.mem (.struct s))) : List Instr :=
  allocateStructCode (structAllocationSize s) ++ [.mstore (cellOf b dst)]

/-- Whole-local deletion grows the source heap and updates just its destination pointer. -/
theorem deleteStruct_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s : Name} (dst : Idx Γ (.mem (.struct s)))
    (hp : primitiveMembers (structDef s) = true) (hmf : (Ty.ref (.struct s)).mapFree = true)
    (hspace : cursor.val + structAllocationSize s < W) :
    let σ' := (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).1.setLocal dst
      (some (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).2)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateStructMachine m cursor (structAllocationSize s))
      (cellOf b dst) (.val cursor)
    TRun.deleteMem (.var dst hmf) σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (deleteStructCode b dst) m = .ok m' 0 ∧
      StateRepr L b frame F σ' base' m' ∧
      StructAllocatorRepr σ'.heap base' frame ⟨cursor.val + structAllocationSize s, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨defaultStruct_delete σ dst hp hmf, ?_, ?_, ?_, rfl⟩
  · rw [deleteStructCode, run_append_ok (allocateStruct_run m cursor _ ha.arrays.free.cell)]
    rfl
  · have hid : (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocateStruct ha hb hp hmf hspace).setMem dst
        (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).2
  · exact (ha.reserveStruct (s := s) (defaultFields (structDef s) hp)
      (defaultFields_defaults σ.heap hp hmf) (structAllocationSize s) (Nat.le_max_right _ _) hspace).localWrite
      (cellOf b dst) (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) (.val cursor)

/-- Default source declaration and emitted allocation agree with exact cursor growth. -/
theorem defaultStruct_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s : Name} (hp : primitiveMembers (structDef s) = true)
    (hmf : (Ty.ref (.struct s)).mapFree = true)
    (hspace : cursor.val + structAllocationSize s < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let σ' := σ.allocPush (R := .struct s) (defaultFields (structDef s) hp)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateStructMachine m cursor (structAllocationSize s))
      (cell (b + Γ.length)) (.val cursor)
    TRun.declMem (.struct s) none hmf σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (declareStructCode (Γ := Γ) b s) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.struct s)) .ok) σ' base' m' ∧
      StructAllocatorRepr σ'.heap base' frame ⟨cursor.val + structAllocationSize s, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨defaultStruct_decl σ hp hmf, ?_, ?_, ?_, rfl⟩
  · rw [declareStructCode, run_append_ok (allocateStruct_run m cursor _ ha.arrays.free.cell)]
    rfl
  · have hid : (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocateStruct ha hb hp hmf hspace).consMem
        (σ.alloc (R := .struct s) (defaultFields (structDef s) hp)).2 hcap
  · exact (ha.reserveStruct (s := s) (defaultFields (structDef s) hp)
      (defaultFields_defaults σ.heap hp hmf) (structAllocationSize s) (Nat.le_max_right _ _) hspace).localWrite
      (b + Γ.length) (by omega) (by omega) (.val cursor)

end Solidity.Evm.Memory
