import Solidity.Backend.MemoryCopies.CheckedStoragePathInterface

/-! Actual compiled storage paths feed the checked copy. Existing successful
Source and representation results are transported without changing semantics. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem append_run_eq (left right suffix : List Instr) (machine : Machine)
    (same : run left machine = run right machine) :
    run (left ++ suffix) machine = run (right ++ suffix) machine := by
  simp only [run] at same ⊢
  rw [exec_append,exec_append,same]

theorem checked_storage_path_run {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded)) :
    run (checkedStoragePathCode b path) machine =
      if cursor.val + (values.length + 1) < W then run (runtimePathArrayCode b path) machine else .revert := by
  rcases spath_sim path represented.core supported with
    ⟨actual,slot,value,resolution,live,_,sourceRepr,pathRun⟩ | ⟨refused,_⟩
  · rw [resolved] at resolution
    cases resolution
    have observed : state.storage.find reference = some value := Sto.find_of_findLive live
    rw [found] at observed
    cases observed
    rw [checkedStoragePathCode,run_append_ok pathRun,
      checked_storage_array_run state.heap primitive values bounded base frame cursor machine slot L allocator sourceRepr,
      runtimePathArrayCode,run_append_ok pathRun]
  · rw [resolved] at refused
    cases refused

theorem checked_storage_path_body_success {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) :
    CheckedStoragePathBodyResult b frame path values bounded state base cursor machine fits := by
  obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps⟩ :=
    runtime_path_array_body state base cursor machine path reference values bounded represented allocator supported resolved found fits
  refine ⟨base',target,?_,allocated,root,extension,shape,below,gaps⟩
  rw [checked_storage_path_run state base cursor machine path reference values bounded represented allocator supported resolved found,if_pos fits]
  exact ran

theorem checked_storage_path_declaration_success {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) (locals : b + (Γ.length + 1) ≤ frame) :
    CheckedStoragePathDeclarationResult L b frame frag state base cursor machine path values bounded fits := by
  obtain ⟨base',target,source,ran,afterRepr,allocated,extension,stack,root,localAt,below⟩ :=
    runtime_path_array_declaration state base cursor machine path reference values bounded represented allocator positive supported resolved found fits locals
  refine ⟨base',target,source,?_,afterRepr,allocated,extension,stack,root,localAt,below⟩
  have equal : run (checkedStoragePathCode b path) machine = run (runtimePathArrayCode b path) machine := by
    rw [checked_storage_path_run state base cursor machine path reference values bounded represented allocator supported resolved found,if_pos fits]
  exact (append_run_eq _ _ _ machine equal).trans ran

theorem checked_storage_path_rebind_success {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) :
    CheckedStoragePathRebindResult L b frame frag state base cursor machine destination path values bounded fits := by
  obtain ⟨base',target,source,ran,afterRepr,allocated,extension,stack,root,localAt,below,kept,fresh⟩ :=
    runtime_path_array_rebind state base cursor machine destination path reference values bounded represented allocator positive supported resolved found fits
  refine ⟨base',target,source,?_,afterRepr,allocated,extension,stack,root,localAt,below,kept,fresh⟩
  have equal : run (checkedStoragePathCode b path) machine = run (runtimePathArrayCode b path) machine := by
    rw [checked_storage_path_run state base cursor machine path reference values bounded represented allocator supported resolved found,if_pos fits]
  exact (append_run_eq _ _ _ machine equal).trans ran

theorem checked_storage_path_body {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded)) :
    (∃ fits, CheckedStoragePathBodyResult b frame path values bounded state base cursor machine fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run (checkedStoragePathCode b path) machine = .revert) := by
  by_cases fits : cursor.val + (values.length + 1) < W
  · exact Or.inl ⟨fits,checked_storage_path_body_success state base cursor machine path reference values bounded represented allocator supported resolved found fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [checked_storage_path_run state base cursor machine path reference values bounded represented allocator supported resolved found,if_neg fits]

theorem checked_storage_path_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (locals : b + (Γ.length + 1) ≤ frame) :
    (∃ fits, CheckedStoragePathDeclarationResult L b frame frag state base cursor machine path values bounded fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run (checkedStoragePathDeclareCode b path) machine = .revert) := by
  by_cases fits : cursor.val + (values.length + 1) < W
  · exact Or.inl ⟨fits,checked_storage_path_declaration_success state base cursor machine path reference values bounded represented allocator positive supported resolved found fits locals⟩
  · right
    refine ⟨fits,?_⟩
    have failed : run (checkedStoragePathCode b path) machine = .revert := by
      rw [checked_storage_path_run state base cursor machine path reference values bounded represented allocator supported resolved found,if_neg fits]
    exact run_append_revert failed

theorem checked_storage_path_rebind {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded)) :
    (∃ fits, CheckedStoragePathRebindResult L b frame frag state base cursor machine destination path values bounded fits) ∨
      (¬ cursor.val + (values.length + 1) < W ∧ run (checkedStoragePathRebindCode b destination path) machine = .revert) := by
  by_cases fits : cursor.val + (values.length + 1) < W
  · exact Or.inl ⟨fits,checked_storage_path_rebind_success state base cursor machine destination path reference values bounded represented allocator positive supported resolved found fits⟩
  · right
    refine ⟨fits,?_⟩
    have failed : run (checkedStoragePathCode b path) machine = .revert := by
      rw [checked_storage_path_run state base cursor machine path reference values bounded represented allocator supported resolved found,if_neg fits]
    exact run_append_revert failed

theorem checked_storage_path_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    (MRhs.copy path rfl).evalT state = .error .revert ∧ run (checkedStoragePathCode b path) machine = .revert := by
  refine ⟨(runtime_path_array_refusal state machine path represented supported refused).1,?_⟩
  rcases spath_sim path represented supported with ⟨actual,slot,value,source,_,_,_,_⟩ | ⟨_,failed⟩
  · rw [refused] at source
    cases source
  · exact run_append_revert failed

theorem checked_storage_path_declaration_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .error .revert ∧
    run (checkedStoragePathDeclareCode b path) machine = .revert := by
  refine ⟨(runtime_path_array_declaration_refusal state machine path represented supported refused).1,?_⟩
  exact run_append_revert (checked_storage_path_refusal state machine path represented supported refused).2

theorem checked_storage_path_rebind_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.rebindMem destination (.copy path rfl) state = .error .revert ∧
    run (checkedStoragePathRebindCode b destination path) machine = .revert := by
  refine ⟨(runtime_path_array_rebind_refusal state machine destination path represented supported refused).1,?_⟩
  exact run_append_revert (checked_storage_path_refusal state machine path represented supported refused).2

def checkedStoragePath : CheckedStoragePathCertificate :=
  ⟨checked_storage_path_body,checked_storage_path_declaration,checked_storage_path_rebind,checked_storage_path_refusal⟩

#print axioms checked_storage_path_run
#print axioms checked_storage_path_body_success
#print axioms checked_storage_path_declaration_success
#print axioms checked_storage_path_rebind_success
#print axioms checked_storage_path_body
#print axioms checked_storage_path_declaration
#print axioms checked_storage_path_rebind
#print axioms checked_storage_path_refusal
#print axioms checked_storage_path_declaration_refusal
#print axioms checked_storage_path_rebind_refusal
#print axioms checkedStoragePath
end Solidity.Backend.MemoryCopies
