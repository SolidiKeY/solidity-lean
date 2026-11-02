import Solidity.Evm.MemoryStructReferenceAlloc

/-!
# Initializing a parent with previously allocated children

The caller keeps its parent pointer on the stack. A child lies a statically
known distance below it because default construction allocates children first.
The store retains the parent pointer and every word below it.
-/
namespace Solidity.Evm.Memory
open Semantics

/-- Store an earlier child's pointer without consuming the parent pointer. -/
def writeBackReferenceCode (distance offset : Nat) : List Instr :=
  [.dup 1, .push (.val (wmod distance)), .swap 1, .sub, .dup 2] ++ writeFieldCode offset

/-- Under the construction bounds subtraction names the real earlier address. -/
theorem writeBackReference_run (m : Machine) (parent : Fin W) (distance offset : Nat)
    (hd : distance ≤ parent.val) (hs : parent.val + offset < W) :
    run (writeBackReferenceCode distance offset) (m.push (.val parent)) =
      .ok ((writeMachine m (parent.val + offset)
        (.val (wmod (parent.val - distance)))).push (.val parent)) 0 := by
  have hdist : distance < W := Nat.lt_of_le_of_lt hd parent.isLt
  have hsub : wmod (parent.val + (W - distance)) = wmod (parent.val - distance) := by
    apply Fin.ext
    change (parent.val + (W - distance)) % W = (parent.val - distance) % W
    have he : parent.val + (W - distance) = (parent.val - distance) + W := by omega
    rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  have hp : run [.dup 1, .push (.val (wmod distance)), .swap 1, .sub, .dup 2]
        (m.push (.val parent)) =
      .ok (((m.push (.val parent)).push (.val (wmod (parent.val - distance)))).push (.val parent)) 0 := by
    simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, Nat.reduceSub,
      Out.ok_bind, exec_nil, wmod_of_lt hdist, hsub]
  rw [writeBackReferenceCode, run_append_ok hp]
  exact writeFieldWord_run (m.push (.val parent)) parent offset _ hs

/-- Initialize just reference words; primitive default words remain in the zero tail. -/
def initializeReferenceCode : List (Name × Ty) → (Name → Nat) → Nat → Nat → List Instr
  | [], _, _, _ => []
  | (_, .prim _) :: fs, offsets, root, member =>
    initializeReferenceCode fs offsets root (member + 1)
  | (f, .ref _) :: fs, offsets, root, member =>
    writeBackReferenceCode (root - offsets f) member ++
      initializeReferenceCode fs offsets root (member + 1)

def initializeReferenceMachine : List (Name × Ty) → (Name → Nat) → Nat → Nat → Fin W → Machine → Machine
  | [], _, _, _, _, m => m
  | (_, .prim _) :: fs, offsets, root, member, parent, m =>
    initializeReferenceMachine fs offsets root (member + 1) parent m
  | (f, .ref _) :: fs, offsets, root, member, parent, m =>
    initializeReferenceMachine fs offsets root (member + 1) parent
      (writeMachine m (parent.val + member) (.val (wmod (parent.val - (root - offsets f)))))

theorem initializeReference_run (fs : List (Name × Ty)) (offsets : Name → Nat)
    (root member : Nat) (parent : Fin W) (m : Machine)
    (hr : root ≤ parent.val) (hs : parent.val + member + fs.length ≤ W) :
    run (initializeReferenceCode fs offsets root member) (m.push (.val parent)) =
      .ok ((initializeReferenceMachine fs offsets root member parent m).push (.val parent)) 0 := by
  induction fs generalizing member m with
  | nil => rfl
  | cons fT fs ih =>
    obtain ⟨f, T⟩ := fT
    have ht : parent.val + (member + 1) + fs.length ≤ W := by
      simp only [List.length_cons] at hs
      omega
    cases T with
    | prim p => exact ih (member + 1) m ht
    | ref R =>
      rw [initializeReferenceCode,
        run_append_ok (writeBackReference_run m parent (root - offsets f) member (by omega) (by
          simp only [List.length_cons] at hs; omega))]
      exact ih (member + 1) _ ht

/-- Initialization touches no address outside the parent's field interval. -/
theorem initializeReference_other (fs : List (Name × Ty)) (offsets : Name → Nat)
    (root member : Nat) (parent : Fin W) (m : Machine) (addr : Nat)
    (ha : addr < parent.val + member ∨ parent.val + member + fs.length ≤ addr) :
    (initializeReferenceMachine fs offsets root member parent m).mem addr = m.mem addr := by
  induction fs generalizing member m with
  | nil => rfl
  | cons fT fs ih =>
    obtain ⟨f, T⟩ := fT
    have ht : addr < parent.val + (member + 1) ∨
        parent.val + (member + 1) + fs.length ≤ addr := by
      simp only [List.length_cons] at ha
      omega
    cases T with
    | prim p => exact ih (member + 1) m ht
    | ref R =>
      rw [initializeReferenceMachine, ih (member + 1) _ ht]
      exact upd_other _ _ (by simp only [List.length_cons] at ha; omega)

/-- Primitive member cells are never changed by the reference initializer. -/
theorem initializeReference_primitive (fs : List (Name × Ty)) (offsets : Name → Nat)
    (root member : Nat) (parent : Fin W) (m : Machine) {f : Name} {p : PrimTy}
    (hf : lookupBy f fs = some (.prim p)) :
    (initializeReferenceMachine fs offsets root member parent m).mem
      (parent.val + member + fieldOffset fs f) = m.mem (parent.val + member + fieldOffset fs f) := by
  induction fs generalizing member m with
  | nil => cases hf
  | cons fT fs ih =>
    obtain ⟨g, T⟩ := fT
    by_cases he : f = g
    · subst g
      cases T with
      | ref R => cases SFields.lookupBy_cons_pos rfl hf
      | prim q =>
        simp only [initializeReferenceMachine, fieldOffset, if_true, Nat.add_zero]
        exact initializeReference_other fs offsets root (member + 1) parent m _ (.inl (by omega))
    · have hh := SFields.lookupBy_cons_neg he hf
      have hoff : parent.val + member + fieldOffset ((g, T) :: fs) f =
          parent.val + (member + 1) + fieldOffset fs f := by
        simp only [fieldOffset, he, if_false]; omega
      rw [hoff]
      cases T with
      | prim q => exact ih (member + 1) m hh
      | ref R =>
        rw [initializeReferenceMachine, ih (member + 1) _ hh]
        exact upd_other _ _ (by omega)

/-- A reference member contains the certified earlier child's pointer. -/
theorem initializeReference_reference (fs : List (Name × Ty)) (offsets : Name → Nat)
    (root member : Nat) (parent : Fin W) (m : Machine) {f : Name} {R : RefTy}
    (hf : lookupBy f fs = some (.ref R)) :
    (initializeReferenceMachine fs offsets root member parent m).mem
      (parent.val + member + fieldOffset fs f) = .val (wmod (parent.val - (root - offsets f))) := by
  induction fs generalizing member m with
  | nil => cases hf
  | cons fT fs ih =>
    obtain ⟨g, T⟩ := fT
    by_cases he : f = g
    · subst g
      cases T with
      | prim p => cases SFields.lookupBy_cons_pos rfl hf
      | ref Q =>
        simp only [initializeReferenceMachine, fieldOffset, if_true, Nat.add_zero]
        rw [initializeReference_other fs offsets root (member + 1) parent _ _ (.inl (by omega))]
        exact upd_same _ _ _
    · have hh := SFields.lookupBy_cons_neg he hf
      have hoff : parent.val + member + fieldOffset ((g, T) :: fs) f =
          parent.val + (member + 1) + fieldOffset fs f := by
        simp only [fieldOffset, he, if_false]; omega
      rw [hoff]
      cases T with
      | prim p => exact ih (member + 1) m hh
      | ref Q => exact ih (member + 1) _ hh

/-- The initializer changes only memory, preserving all machine observations. -/
theorem initializeReference_shape (fs : List (Name × Ty)) (offsets : Name → Nat)
    (root member : Nat) (parent : Fin W) (m : Machine) :
    initializeReferenceMachine fs offsets root member parent m =
      {m with mem := (initializeReferenceMachine fs offsets root member parent m).mem} := by
  induction fs generalizing member m with
  | nil => rfl
  | cons fT fs ih =>
    obtain ⟨f, T⟩ := fT
    cases T with
    | prim p => exact ih (member + 1) m
    | ref R =>
      rw [initializeReferenceMachine, ih (member + 1)]
      rfl

/-- Complete parent allocation: emitted instructions, actual typed heap extension,
old aliases, separated intervals and the zero tail share one initialized result. -/
theorem allocateReferenceStruct_correct {C : Contract} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    {s : Name} (o : MObj σ.H (.struct s)) (hd : StructDefaults o)
    (offsets : Name → Nat) (root : Nat) (hr : root ≤ cursor.val)
    (hlinks : ∀ {f : Name} {R : RefTy} (hf : lookupBy f (structDef s) = some (.ref R)),
      base (MFields.get (structDef s) o hf).id = wmod (cursor.val - (root - offsets f)))
    (hspace : cursor.val + structAllocationSize s < W) :
    let allocated := allocateStructMachine m cursor (structAllocationSize s)
    let final := initializeReferenceMachine (structDef s) offsets root 0 cursor allocated
    run (allocateStructCode (structAllocationSize s) ++
      initializeReferenceCode (structDef s) offsets root 0) m = .ok (final.push (.val cursor)) 0 ∧
    StateRepr L b frame F (σ.alloc o).1 (upd base σ.H.length cursor) final ∧
    StructAllocatorRepr (σ.alloc o).1.heap (upd base σ.H.length cursor) frame
      ⟨cursor.val + structAllocationSize s, hspace⟩ final := by
  dsimp only
  let allocated := allocateStructMachine m cursor (structAllocationSize s)
  let final := initializeReferenceMachine (structDef s) offsets root 0 cursor allocated
  have hlen : (structDef s).length ≤ structAllocationSize s := Nat.le_max_right _ _
  have hz : 0 < cursor.val := Nat.lt_of_lt_of_le ha.arrays.free.reserved ha.arrays.free.above
  have hshape : final = {m with mem := final.mem} := by
    rw [show final = initializeReferenceMachine (structDef s) offsets root 0 cursor allocated from rfl,
      initializeReference_shape]
    rfl
  have hrepr := h.reserveInitializedStruct ha hb o
    (next := ⟨cursor.val + structAllocationSize s, hspace⟩) (by simp only; omega) final.mem
    (by
      intro addr hpos hlt
      change (initializeReferenceMachine (structDef s) offsets root 0 cursor allocated).mem addr = _
      rw [initializeReference_other _ _ _ _ _ _ _ (.inl (by omega))]
      exact allocateStructMachine_other m cursor _ addr (by omega))
    (by
      change (initializeReferenceMachine (structDef s) offsets root 0 cursor allocated).mem 0 = _
      rw [initializeReference_other _ _ _ _ _ _ _ (.inl (by omega))]
      simp only [allocated, allocateStructMachine, writeMachine, upd_same, wmod_of_lt hspace])
    (by
      intro addr hnext
      change (initializeReferenceMachine (structDef s) offsets root 0 cursor allocated).mem addr = _
      rw [initializeReference_other _ _ _ _ _ _ _ (.inr (by simp only at hnext; omega)),
        allocateStructMachine_other m cursor _ addr (by simp only at hnext; omega)]
      exact ha.arrays.free.zero addr (by simp only at hnext; omega))
    (by
      intro f R hf
      change (initializeReferenceMachine (structDef s) offsets root 0 cursor allocated).mem
        (cursor.val + fieldOffset (structDef s) f) = _
      rw [show cursor.val + fieldOffset (structDef s) f =
        cursor.val + 0 + fieldOffset (structDef s) f from rfl,
        initializeReference_reference _ _ _ _ _ _ hf, hlinks hf])
    (by
      refine ⟨by omega, ?_⟩
      intro f p hf
      simp only [Heap.field, Heap.get_alloc, MObj.wk, MFields.get_wk, hd hf]
      change ReprV p p.dflt ((initializeReferenceMachine (structDef s) offsets root 0 cursor allocated).mem
        (cursor.val + fieldOffset (structDef s) f))
      rw [show cursor.val + fieldOffset (structDef s) f =
        cursor.val + 0 + fieldOffset (structDef s) f from rfl,
        initializeReference_primitive _ _ _ _ _ _ hf,
        allocateStructMachine_other m cursor _ _ (by omega),
        ha.arrays.free.zero _ (by omega)]
      exact ReprV.dflt_zero p)
  refine ⟨?_, ?_, ?_⟩
  · rw [run_append_ok (allocateStruct_run m cursor _ ha.arrays.free.cell)]
    exact initializeReference_run _ _ root 0 cursor allocated hr (by omega)
  · change StateRepr L b frame F (σ.alloc o).1 (upd base σ.H.length cursor) final
    rw [hshape]
    exact hrepr.1
  · change StructAllocatorRepr (σ.alloc o).1.heap (upd base σ.H.length cursor) frame
      ⟨cursor.val + structAllocationSize s, hspace⟩ final
    rw [hshape]
    exact hrepr.2

end Solidity.Evm.Memory
