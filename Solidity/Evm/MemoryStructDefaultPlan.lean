import Solidity.Evm.MemoryStructReferenceCode
import Solidity.Evm.MemoryStructDefaultLayout
import Solidity.Evm.MemoryRefDelete
import Solidity.Evm.MemoryGrowResult
import Solidity.Semantics.RunWk

/-!
# Certificates for finite default construction

Plans are indexed by the existing reference type and speak directly about
Heap.allocDefault. Field certificates speak about the actual storage-default
copy fold; no alternate value or heap representation is introduced.
-/
-- Preserve pre-4.35 proof elaboration transparency; declarations are unchanged.
set_option backward.isDefEq.respectTransparency false

namespace Solidity.Evm.Memory
open Semantics

private theorem env_wk_refl {C : Contract} {H : HTy} (Γ : Ctx) (env : TEnv C H Γ) :
    TEnv.wk (List.prefix_refl H) Γ env = env := by
  apply TEnv.ext
  intro t i
  rw [TEnv.get_wk]
  cases t <;> try rfl
  change (TEnv.get i env).map _ = TEnv.get i env
  cases TEnv.get i env <;> rfl

def DefaultPlanSound (R : RefTy) (cost root : Nat) (code : List Instr) : Prop :=
  ∀ {C : Contract} {Γ : Ctx} (σ : State C Γ)
    {L b frame : Nat} {F : Frag Γ} (base : Nat → Fin W) (cursor : Fin W) (m : Machine)
    (hm : (Ty.ref R).mapFree = true),
    StateRepr L b frame F σ base m → StructAllocatorRepr σ.heap base frame cursor m →
    0 < b → ∀ hs : cursor.val + cost < W,
    let g := σ.heap.allocDefault R hm
    ∃ (base' : Nat → Fin W) (mem : Nat → Word),
      StateRepr L b frame F (σ.adopt g).1 base' {m with mem := mem} ∧
      StructAllocatorRepr g.heap base' frame ⟨cursor.val + cost, hs⟩ {m with mem := mem} ∧
      BaseExtends σ.H base base' ∧
      base' g.val.id = wmod (cursor.val + root) ∧
      run code m = .ok (({m with mem := mem} : Machine).push (.val (wmod (cursor.val + root)))) 0

structure DefaultPlan (R : RefTy) where
  cost : Nat
  root : Nat
  code : List Instr
  cells : finiteDefaultCells (.ref R) = some cost
  root_lt : root < cost
  sound : DefaultPlanSound R cost root code

def DefaultFieldsPlanSound (fs : List (Name × Ty)) (cost : Nat)
    (offsets : Name → Nat) (code : List Instr) : Prop :=
  ∀ {C : Contract} {Γ : Ctx} (σ : State C Γ)
    {L b frame : Nat} {F : Frag Γ} (base : Nat → Fin W) (cursor : Fin W) (m : Machine)
    (hm : ∀ fT ∈ fs, fT.2.mapFree = true),
    StateRepr L b frame F σ base m → StructAllocatorRepr σ.heap base frame cursor m →
    0 < b → ∀ hs : cursor.val + cost < W,
    let g := (SFields.dflt fs).copyStToM σ.heap hm
    ∃ (base' : Nat → Fin W) (mem : Nat → Word),
      StateRepr L b frame F (σ.adopt g).1 base' {m with mem := mem} ∧
      StructAllocatorRepr g.heap base' frame ⟨cursor.val + cost, hs⟩ {m with mem := mem} ∧
      BaseExtends σ.H base base' ∧
      (∀ {f : Name} {p : PrimTy} (hf : lookupBy f fs = some (.prim p)),
        MFields.get fs g.val hf = p.dflt) ∧
      (∀ {f : Name} {R : RefTy} (hf : lookupBy f fs = some (.ref R)),
        base' (MFields.get fs g.val hf).id = wmod (cursor.val + offsets f)) ∧
      run code m = .ok {m with mem := mem} 0

structure DefaultFieldsPlan (fs : List (Name × Ty)) where
  cost : Nat
  offsets : Name → Nat
  code : List Instr
  cells : finiteDefaultFieldCells fs = some cost
  offsets_lt : ∀ {f : Name} {R : RefTy}, lookupBy f fs = some (.ref R) → offsets f < cost
  sound : DefaultFieldsPlanSound fs cost offsets code

/-- The empty field fold allocates nothing and leaves its input represented. -/
private theorem defaultNilFields_sound  :
    DefaultFieldsPlanSound [] 0 (fun _ => 0) [] := by
  intro C Γ σ L b frame F base cursor m hm h ha hb hs
  refine ⟨base, m.mem, ?_, ?_, BaseExtends.refl base, ?_, ?_, rfl⟩
  · simpa only [SFields.dflt, SFields.copyStToM_nil, State.adopt, env_wk_refl] using h
  · simpa only [SFields.dflt, SFields.copyStToM_nil, Nat.add_zero] using ha
  · intro f p hf; cases hf
  · intro f R hf; cases hf

def DefaultFieldsPlan.nil : DefaultFieldsPlan [] where
  cost := 0
  offsets := fun _ => 0
  code := []
  cells := by rw [finiteDefaultFieldCells]
  offsets_lt := by intro f R hf; cases hf
  sound := defaultNilFields_sound

/-- Empty primitive arrays use the existing allocation simulation. -/
private theorem defaultArray_sound (p : PrimTy) :
    DefaultPlanSound (.array (.prim p)) 1 0 ([.push w[0]] ++ allocateArrayCode) := by
  intro C Γ σ L b frame F base cursor m hm h ha hb hs
  have he : σ.heap.allocDefault (.array (.prim p)) hm =
      Grown.alloc ⟨List.prefix_refl _, σ.heap, defaultArray p (wmod 0)⟩ := defaultArray_alloc σ.heap p
  have hshape : allocateMachine m cursor (wmod 0) =
      {m with mem := (allocateMachine m cursor (wmod 0)).mem} := rfl
  have hz : (wmod 0).val = 0 := rfl
  have hspace : cursor.val + (wmod 0).val + 1 < W := hs
  dsimp only
  rw [he]
  refine ⟨upd base σ.H.length cursor, (allocateMachine m cursor (wmod 0)).mem, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.adopt, State.alloc, Grown.alloc, ← hshape] using
      h.allocate ha hb p (wmod 0) hspace
  · simpa only [Grown.alloc, hz, Nat.add_zero, ← hshape] using
      ha.allocateArray p (wmod 0) hspace
  · exact fun r => allocationBase_old base cursor r
  · simp only [Grown.alloc, Heap.alloc, upd_same, Nat.add_zero,
      wmod_of_lt cursor.isLt]
  · rw [run_append_ok (show run [.push w[0]] m = .ok (m.push w[0]) 0 from rfl)]
    have hrun := allocateArray_run m cursor (wmod 0) ha.arrays.free.cell
    rw [hshape] at hrun
    simpa only [Nat.add_zero, wmod_of_lt cursor.isLt, wmod_def, Nat.zero_mod] using hrun

def DefaultPlan.array (p : PrimTy) : DefaultPlan (.array (.prim p)) where
  cost := 1
  root := 0
  code := [.push w[0]] ++ allocateArrayCode
  cells := by rw [finiteDefaultCells]
  root_lt := by decide
  sound := defaultArray_sound p

/-- Primitive fields allocate nothing; their siblings retain the real copy fold. -/
private theorem defaultPrimitiveField_sound (f : Name) (p : PrimTy) {fs : List (Name × Ty)}
    (tail : DefaultFieldsPlan fs) :
    DefaultFieldsPlanSound ((f, .prim p) :: fs) tail.cost tail.offsets tail.code := by
  intro C Γ σ L b frame F base cursor m hm h ha hb hs
  let hmt : ∀ fT ∈ fs, fT.2.mapFree = true := fun fT hf => hm fT (List.mem_cons_of_mem _ hf)
  obtain ⟨base', mem, hst, hal, hext, hprim, href, hrun⟩ :=
    tail.sound σ base cursor m hmt h ha hb hs
  dsimp only
  rw [SFields.dflt, SFields.copyStToM_cons, SVal.dflt_prim, SVal.copyStToM_prim]
  refine ⟨base', mem, hst, hal, hext, ?_, ?_, hrun⟩
  · intro g q hf
    by_cases he : g = f
    · subst g
      have ht := SFields.lookupBy_cons_pos rfl hf
      cases ht
      simp only [MFields.get, dite_true, MVal.wk]
    · simpa only [MFields.get, he, ite_false, dite_false] using hprim (SFields.lookupBy_cons_neg he hf)
  · intro g R hf
    by_cases he : g = f
    · cases SFields.lookupBy_cons_pos he hf
    · simpa only [MFields.get, he, ite_false, dite_false] using href (SFields.lookupBy_cons_neg he hf)

def DefaultFieldsPlan.consPrimitive (f : Name) (p : PrimTy) {fs : List (Name × Ty)}
    (tail : DefaultFieldsPlan fs) : DefaultFieldsPlan ((f, .prim p) :: fs) where
  cost := tail.cost
  offsets := tail.offsets
  code := tail.code
  cells := by
    rw [finiteDefaultFieldCells, finiteDefaultCells, tail.cells]
    change some (0 + tail.cost) = some tail.cost
    rw [Nat.zero_add]
  offsets_lt := by
    intro g R hf
    by_cases he : g = f
    · cases SFields.lookupBy_cons_pos he hf
    · exact tail.offsets_lt (SFields.lookupBy_cons_neg he hf)
  sound := defaultPrimitiveField_sound f p tail

/-- A reference field allocates its child first. Later siblings weaken the
reference while preserving the earlier child's identity and address. -/
private theorem defaultReferenceField_sound (f : Name) {R : RefTy} {fs : List (Name × Ty)}
    (head : DefaultPlan R) (tail : DefaultFieldsPlan fs) :
    DefaultFieldsPlanSound ((f, .ref R) :: fs) (head.cost + tail.cost)
    (fun g => if g = f then head.root else head.cost + tail.offsets g)
    (head.code ++ ([.pop] ++ tail.code)) := by
  intro C Γ σ L b frame F base cursor m hm h ha hb hs
  let hmh : (Ty.ref R).mapFree = true := hm _ List.mem_cons_self
  let hmt : ∀ fT ∈ fs, fT.2.mapFree = true := fun fT hf => hm fT (List.mem_cons_of_mem _ hf)
  let g₁ := σ.heap.allocDefault R hmh
  have hs₁ : cursor.val + head.cost < W := by omega
  obtain ⟨base₁, mem₁, hst₁, hal₁, hext₁, href₁, hrun₁⟩ :=
    head.sound σ base cursor m hmh h ha hb hs₁
  let σ₁ := (σ.adopt g₁).1
  let m₁ : Machine := {m with mem := mem₁}
  let cursor₁ : Fin W := ⟨cursor.val + head.cost, hs₁⟩
  have hs₂ : cursor₁.val + tail.cost < W := by dsimp only [cursor₁]; omega
  obtain ⟨base₂, mem₂, hst₂, hal₂, hext₂, hprim₂, href₂, hrun₂⟩ :=
    tail.sound σ₁ base₁ cursor₁ m₁ hmt hst₁ hal₁ hb hs₂
  dsimp only
  rw [SFields.dflt, SFields.copyStToM_cons]
  refine ⟨base₂, mem₂, ?_, ?_, hext₁.trans g₁.ext hext₂, ?_, ?_, ?_⟩
  · simpa only [σ₁, g₁, m₁, Heap.allocDefault, State.adopt, TEnv.wk_trans] using hst₂
  · simpa only [σ₁, g₁, m₁, Heap.allocDefault, State.adopt, cursor₁, Nat.add_assoc] using hal₂
  · intro g p hf
    by_cases he : g = f
    · cases SFields.lookupBy_cons_pos he hf
    · simpa only [σ₁, g₁, Heap.allocDefault, State.adopt, MFields.get, he, ite_false, dite_false] using hprim₂ (SFields.lookupBy_cons_neg he hf)
  · intro g Q hf
    by_cases he : g = f
    · subst g
      have ht := SFields.lookupBy_cons_pos rfl hf
      cases ht
      simp only [MFields.get, dite_true, if_true, MVal.wk]
      exact (hext₂ g₁.val).trans href₁
    · simpa only [σ₁, g₁, Heap.allocDefault, State.adopt, MFields.get, he, ite_false, dite_false, cursor₁, Nat.add_assoc] using
        href₂ (SFields.lookupBy_cons_neg he hf)
  · rw [run_append_ok hrun₁,
      run_append_ok (show run [.pop] (m₁.push (.val (wmod (cursor.val + head.root)))) =
        .ok m₁ 0 from rfl)]
    exact hrun₂

def DefaultFieldsPlan.consReference (f : Name) {R : RefTy} {fs : List (Name × Ty)}
    (head : DefaultPlan R) (tail : DefaultFieldsPlan fs) :
    DefaultFieldsPlan ((f, .ref R) :: fs) where
  cost := head.cost + tail.cost
  offsets := fun g => if g = f then head.root else head.cost + tail.offsets g
  code := head.code ++ ([.pop] ++ tail.code)
  cells := by
    rw [finiteDefaultFieldCells, head.cells, tail.cells]
    rfl
  offsets_lt := by
    intro g Q hf
    by_cases he : g = f
    · simp only [he, if_true]
      have hh := head.root_lt
      omega
    · simp only [he, ite_false, dite_false]
      have ht := tail.offsets_lt (SFields.lookupBy_cons_neg he hf)
      omega
  sound := defaultReferenceField_sound f head tail

/-- A struct allocates every field child, then initializes its own pointer words. -/
private theorem defaultStruct_sound (s : Name) (fields : DefaultFieldsPlan (structDef s)) :
    DefaultPlanSound (.struct s) (fields.cost + structAllocationSize s) fields.cost
    (fields.code ++ (allocateStructCode (structAllocationSize s) ++
      initializeReferenceCode (structDef s) fields.offsets fields.cost 0)) := by
  intro C Γ σ L b frame F base cursor m hm h ha hb hs
  let hmf : ∀ fT ∈ structDef s, fT.2.mapFree = true :=
    mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using hm)
  let g₁ := (SFields.dflt (structDef s)).copyStToM σ.heap hmf
  have hs₁ : cursor.val + fields.cost < W := by omega
  obtain ⟨base₁, mem₁, hst₁, hal₁, hext₁, hprim₁, href₁, hrun₁⟩ :=
    fields.sound σ base cursor m hmf h ha hb hs₁
  let σ₁ := (σ.adopt g₁).1
  let m₁ : Machine := {m with mem := mem₁}
  let cursor₁ : Fin W := ⟨cursor.val + fields.cost, hs₁⟩
  have hs₂ : cursor₁.val + structAllocationSize s < W := by dsimp only [cursor₁]; omega
  have hlinks : ∀ {f : Name} {R : RefTy}
      (hf : lookupBy f (structDef s) = some (.ref R)),
      base₁ (MFields.get (structDef s) g₁.val hf).id =
        wmod (cursor₁.val - (fields.cost - fields.offsets f)) := by
    intro f R hf
    have hoff := fields.offsets_lt hf
    have he : cursor.val + fields.offsets f = cursor₁.val - (fields.cost - fields.offsets f) := by
      dsimp only [cursor₁]; omega
    rw [← he]
    exact href₁ hf
  let allocated := allocateStructMachine m₁ cursor₁ (structAllocationSize s)
  let final := initializeReferenceMachine (structDef s) fields.offsets fields.cost 0 cursor₁ allocated
  have hparent := allocateReferenceStruct_correct hst₁ hal₁ hb g₁.val hprim₁
    fields.offsets fields.cost (by dsimp only [cursor₁]; omega) hlinks hs₂
  have hshape : final = {m with mem := final.mem} := by
    dsimp only [final]
    rw [initializeReference_shape]
    rfl
  have hadopt : (σ.adopt (Grown.alloc (R := .struct s) g₁)).1 = (σ₁.alloc (R := .struct s) g₁.val).1 := by
    simp only [σ₁, State.alloc, State.adopt, Grown.alloc, TEnv.wk_trans]
  dsimp only
  rw [Heap.allocDefault, SVal.dflt_struct, SVal.copyStToM_struct]
  refine ⟨upd base₁ g₁.H'.length cursor₁, final.mem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hadopt]
    exact Eq.mp (congrArg (fun n => StateRepr L b frame F (σ₁.alloc (R := .struct s) g₁.val).1
      (upd base₁ g₁.H'.length cursor₁) n) hshape) hparent.2.1
  · have hp := Eq.mp (congrArg (fun n => StructAllocatorRepr (σ₁.alloc (R := .struct s) g₁.val).1.heap
      (upd base₁ g₁.H'.length cursor₁) frame
      (⟨cursor₁.val + structAllocationSize s, hs₂⟩ : Fin W) n) hshape) hparent.2.2
    simpa only [σ₁, g₁, State.alloc, State.adopt, cursor₁, Nat.add_assoc, Grown.alloc] using hp
  · exact hext₁.trans g₁.ext (fun r => allocationBase_old base₁ cursor₁ r)
  · simp only [g₁, cursor₁, Grown.alloc, Heap.alloc, upd_same, wmod_of_lt hs₁]
  · rw [run_append_ok hrun₁]
    have hp := Eq.mp (congrArg (fun n => run (allocateStructCode (structAllocationSize s) ++
      initializeReferenceCode (structDef s) fields.offsets fields.cost 0) m₁ =
        .ok (n.push (.val cursor₁)) 0) hshape) hparent.1
    simpa only [cursor₁, wmod_of_lt hs₁] using hp

def DefaultPlan.struct (s : Name) (fields : DefaultFieldsPlan (structDef s)) :
    DefaultPlan (.struct s) where
  cost := fields.cost + structAllocationSize s
  root := fields.cost
  code := fields.code ++ (allocateStructCode (structAllocationSize s) ++
    initializeReferenceCode (structDef s) fields.offsets fields.cost 0)
  cells := by rw [finiteDefaultCells, fields.cells]; rfl
  root_lt := by have hn : 1 ≤ structAllocationSize s := Nat.le_max_left _ _; omega
  sound := defaultStruct_sound s fields

/-- Field construction recurses structurally, given the previous rank's child constructor. -/
def defaultFieldsPlanWith (child : (R : RefTy) → Option (DefaultPlan R)) :
    (fs : List (Name × Ty)) → Option (DefaultFieldsPlan fs)
  | [] => some DefaultFieldsPlan.nil
  | (f, .prim p) :: fs => (defaultFieldsPlanWith child fs).map (DefaultFieldsPlan.consPrimitive f p)
  | (f, .ref R) :: fs => do
    let head ← child R
    let tail ← defaultFieldsPlanWith child fs
    pure (DefaultFieldsPlan.consReference f head tail)

def defaultPlanAt : Nat → (R : RefTy) → Option (DefaultPlan R)
  | _, .array (.prim p) => some (DefaultPlan.array p)
  | 0, .struct _ => none
  | depth + 1, .struct s =>
    (defaultFieldsPlanWith (defaultPlanAt depth) (structDef s)).map (DefaultPlan.struct s)
  | _, .array (.ref _) | _, .fixed _ _ | _, .mapping _ _ => none
termination_by structural depth => depth

/-- The bound comes from the same certified finite type layout as the specification. -/
def defaultPlan? (R : RefTy) : Option (DefaultPlan R) := defaultPlanAt (tyRank (.ref R)) R

end Solidity.Evm.Memory
