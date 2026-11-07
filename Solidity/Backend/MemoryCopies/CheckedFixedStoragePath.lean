import Solidity.Backend.MemoryCopies.CheckedFixedStoragePathInterface

/-! Actual compiled storage paths feed the checked copy. Existing successful
Source and representation results are transported without changing semantics. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem append_run_eq (left right suffix : List Instr) (machine : Machine)
    (same : run left machine = run right machine) :
    run (left ++ suffix) machine = run (right ++ suffix) machine := by
  simp only [run] at same ⊢
  rw [exec_append,exec_append,same]

theorem checked_fixed_storage_path_run {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    run (checkedFixedStoragePathCode b path) machine =
      if cursor.val + max 1 count < W then run (fixedStoragePathCode b path) machine else .revert := by
  rcases spath_sim path represented.core supported with
    ⟨actual,slot,value,resolution,live,_,sourceRepr,pathRun⟩ | ⟨refused,_⟩
  · rw [resolved] at resolution
    cases resolution
    have observed : state.storage.find reference = some value := Sto.find_of_findLive live
    rw [found] at observed
    cases observed
    rw [checkedFixedStoragePathCode,run_append_ok pathRun,
      checked_fixed_storage_run count machine cursor slot allocator.free.cell,
      fixedStoragePathCode,run_append_ok pathRun]
  · rw [resolved] at refused
    cases refused

theorem checked_fixed_storage_path_body_success {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + max 1 count < W) :
    CheckedFixedStoragePathBodyResult b frame path value state base cursor machine fits := by
  obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps⟩ :=
    fixed_storage_path_body state base cursor machine path reference value represented allocator supported resolved found fits
  refine ⟨base',target,?_,allocated,root,extension,shape,below,gaps⟩
  rw [checked_fixed_storage_path_run state base cursor machine path reference value represented allocator supported resolved found,if_pos fits]
  exact ran

theorem checked_fixed_storage_path_declaration_success {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + max 1 count < W) (locals : b + (Γ.length + 1) ≤ frame) :
    CheckedFixedStoragePathDeclarationResult L b frame frag state base cursor machine path value fits := by
  obtain ⟨base',target,source,ran,afterRepr,allocated,extension,stack,root,localAt,below⟩ :=
    fixed_storage_path_declaration state base cursor machine path reference value represented allocator positive supported resolved found fits locals
  refine ⟨base',target,source,?_,afterRepr,allocated,extension,stack,root,localAt,below⟩
  have equal : run (checkedFixedStoragePathCode b path) machine = run (fixedStoragePathCode b path) machine := by
    rw [checked_fixed_storage_path_run state base cursor machine path reference value represented allocator supported resolved found,if_pos fits]
  exact (append_run_eq _ _ _ machine equal).trans ran

theorem checked_fixed_storage_path_rebind_success {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + max 1 count < W) :
    CheckedFixedStoragePathRebindResult L b frame frag state base cursor machine destination path value fits := by
  obtain ⟨base',target,source,ran,afterRepr,allocated,extension,stack,root,localAt,below,kept,fresh⟩ :=
    fixed_storage_path_rebind state base cursor machine destination path reference value represented allocator positive supported resolved found fits
  refine ⟨base',target,source,?_,afterRepr,allocated,extension,stack,root,localAt,below,kept,fresh⟩
  have equal : run (checkedFixedStoragePathCode b path) machine = run (fixedStoragePathCode b path) machine := by
    rw [checked_fixed_storage_path_run state base cursor machine path reference value represented allocator supported resolved found,if_pos fits]
  exact (append_run_eq _ _ _ machine equal).trans ran

theorem checked_fixed_storage_path_body {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    (∃ fits, CheckedFixedStoragePathBodyResult b frame path value state base cursor machine fits) ∨
      (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStoragePathCode b path) machine = .revert) := by
  by_cases fits : cursor.val + max 1 count < W
  · exact Or.inl ⟨fits,checked_fixed_storage_path_body_success state base cursor machine path reference value represented allocator supported resolved found fits⟩
  · right
    refine ⟨fits,?_⟩
    rw [checked_fixed_storage_path_run state base cursor machine path reference value represented allocator supported resolved found,if_neg fits]

theorem checked_fixed_storage_path_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (locals : b + (Γ.length + 1) ≤ frame) :
    (∃ fits, CheckedFixedStoragePathDeclarationResult L b frame frag state base cursor machine path value fits) ∨
      (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStoragePathDeclareCode b path) machine = .revert) := by
  by_cases fits : cursor.val + max 1 count < W
  · exact Or.inl ⟨fits,checked_fixed_storage_path_declaration_success state base cursor machine path reference value represented allocator positive supported resolved found fits locals⟩
  · right
    refine ⟨fits,?_⟩
    have failed : run (checkedFixedStoragePathCode b path) machine = .revert := by
      rw [checked_fixed_storage_path_run state base cursor machine path reference value represented allocator supported resolved found,if_neg fits]
    exact run_append_revert failed

theorem checked_fixed_storage_path_rebind {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    (∃ fits, CheckedFixedStoragePathRebindResult L b frame frag state base cursor machine destination path value fits) ∨
      (¬ cursor.val + max 1 count < W ∧ run (checkedFixedStoragePathRebindCode b destination path) machine = .revert) := by
  by_cases fits : cursor.val + max 1 count < W
  · exact Or.inl ⟨fits,checked_fixed_storage_path_rebind_success state base cursor machine destination path reference value represented allocator positive supported resolved found fits⟩
  · right
    refine ⟨fits,?_⟩
    have failed : run (checkedFixedStoragePathCode b path) machine = .revert := by
      rw [checked_fixed_storage_path_run state base cursor machine path reference value represented allocator supported resolved found,if_neg fits]
    exact run_append_revert failed

theorem checked_fixed_storage_path_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    (MRhs.copy path rfl).evalT state = .error .revert ∧ run (checkedFixedStoragePathCode b path) machine = .revert := by
  refine ⟨(fixed_storage_path_refusal state machine path represented supported refused).1,?_⟩
  rcases spath_sim path represented supported with ⟨actual,slot,value,source,_,_,_,_⟩ | ⟨_,failed⟩
  · rw [refused] at source
    cases source
  · exact run_append_revert failed

theorem checked_fixed_storage_path_declaration_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.declMem (.fixed (.prim primitive) count) (some (.copy path rfl)) rfl state = .error .revert ∧
    run (checkedFixedStoragePathDeclareCode b path) machine = .revert := by
  refine ⟨(fixed_storage_path_declaration_refusal state machine path represented supported refused).1,?_⟩
  exact run_append_revert (checked_fixed_storage_path_refusal state machine path represented supported refused).2

theorem checked_fixed_storage_path_rebind_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.rebindMem destination (.copy path rfl) state = .error .revert ∧
    run (checkedFixedStoragePathRebindCode b destination path) machine = .revert := by
  refine ⟨(fixed_storage_path_rebind_refusal state machine destination path represented supported refused).1,?_⟩
  exact run_append_revert (checked_fixed_storage_path_refusal state machine path represented supported refused).2

def checkedFixedStoragePath : CheckedFixedStoragePathCertificate :=
  ⟨checked_fixed_storage_path_body,checked_fixed_storage_path_declaration,checked_fixed_storage_path_rebind,checked_fixed_storage_path_refusal⟩

#print axioms checked_fixed_storage_path_run
#print axioms checked_fixed_storage_path_body_success
#print axioms checked_fixed_storage_path_declaration_success
#print axioms checked_fixed_storage_path_rebind_success
#print axioms checked_fixed_storage_path_body
#print axioms checked_fixed_storage_path_declaration
#print axioms checked_fixed_storage_path_rebind
#print axioms checked_fixed_storage_path_refusal
#print axioms checked_fixed_storage_path_declaration_refusal
#print axioms checked_fixed_storage_path_rebind_refusal
#print axioms checkedFixedStoragePath
end Solidity.Backend.MemoryCopies
