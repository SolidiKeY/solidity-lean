import Solidity.Backend.MemoryCopies.FixedStoragePathInterface

/-! The existing storage path compiler produces the actual slot and typed
value; the fixed leaf transports the actual Source copy and local bindings. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_storage_path_rhs {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (state : State C Γ) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (reference : SRef C (.ref (.fixed (.prim primitive) count))) (value : SVal (.ref (.fixed (.prim primitive) count)))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    (MRhs.copy path rfl).evalT state = .ok (state.copyStToMG value rfl) := by
  simp only [MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,State.copyStToMG,State.grow]

theorem fixed_storage_path_decl_source {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (state : State C Γ) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (reference : SRef C (.ref (.fixed (.prim primitive) count))) (value : SVal (.ref (.fixed (.prim primitive) count)))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.declMem (.fixed (.prim primitive) count) (some (.copy path rfl)) rfl state =
      .ok ⟨(state.adopt grown).1.push (t := .mem (.fixed (.prim primitive) count)) (some grown.val),grown.ext⟩ := by
  rw [TRun.declMem,fixed_storage_path_rhs state path reference value resolved found]
  rfl

theorem fixed_storage_path_body {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + max 1 count < W) :
    FixedStoragePathBodyResult b frame path value state base cursor machine fits := by
  rcases spath_sim path represented.core supported with
    ⟨actual,slot,observedValue,resolution,live,_,sourceRepr,pathRun⟩ | ⟨refused,_⟩
  · rw [resolved] at resolution
    cases resolution
    have observed : state.storage.find reference = some observedValue := Sto.find_of_findLive live
    rw [found] at observed
    cases observed
    obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps,_,_⟩ :=
      runtime_fixed_storage_success state.heap primitive count value base frame cursor machine slot L allocator sourceRepr fits
    refine ⟨base',target,?_,allocated,root,extension,shape,below,gaps⟩
    rw [fixedStoragePathCode,run_append_ok pathRun]
    exact ran
  · rw [resolved] at refused
    cases refused

theorem fixed_storage_path_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + max 1 count < W) (locals : b + (Γ.length + 1) ≤ frame) :
    FixedStoragePathDeclarationResult L b frame frag state base cursor machine path value fits := by
  obtain ⟨base',body,ran,allocated,root,extension,shape,below,_⟩ :=
    fixed_storage_path_body state base cursor machine path reference value represented allocator supported resolved found fits
  let grown := value.copyStToM state.heap rfl
  let target := writeMachine body (cell (b + Γ.length)) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,fixed_storage_path_decl_source state path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_⟩
  · rw [fixedStoragePathDeclareCode,run_append_ok ran]
    rfl
  · simpa only [grown,root,target] using adopted.consMem grown.val locals
  · exact allocated.localWrite (b + Γ.length) (by omega) (by omega) (.val cursor)
  · change body.stack = machine.stack
    rw [shape]
  · exact upd_same _ _ _
  · intro address lower upper different
    change upd body.mem (cell (b + Γ.length)) (.val cursor) address = machine.mem address
    rw [upd_other _ _ different]
    exact below address lower upper

theorem fixed_storage_path_rebind_source {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (state : State C Γ) (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.rebindMem destination (.copy path rfl) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ := by
  rw [TRun.rebindMem,fixed_storage_path_rhs state path reference value resolved found]
  rfl

theorem fixed_storage_path_rebind {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count))) (reference : SRef C (.ref (.fixed (.prim primitive) count)))
    (value : SVal (.ref (.fixed (.prim primitive) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + max 1 count < W) :
    FixedStoragePathRebindResult L b frame frag state base cursor machine destination path value fits := by
  obtain ⟨base',body,ran,allocated,root,extension,shape,below,_⟩ :=
    fixed_storage_path_body state base cursor machine path reference value represented allocator supported resolved found fits
  let grown := value.copyStToM state.heap rfl
  let target := writeMachine body (cellOf b destination) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,fixed_storage_path_rebind_source state destination path reference value resolved found,?_,?_,?_,
    extension,?_,root,?_,?_,SVal.keeps_copyStToM _ rfl state.heap,?_⟩
  · rw [fixedStoragePathRebindCode,run_append_ok ran]
    rfl
  · simpa only [grown,root,target] using adopted.setMem destination grown.val
  · exact allocated.localWrite (lvl b destination) (Nat.lt_of_lt_of_le positive (le_lvl b destination))
      (Nat.lt_of_lt_of_le (lvl_lt b destination) represented.locals) (.val cursor)
  · change body.stack = machine.stack
    rw [shape]
  · exact upd_same _ _ _
  · intro address lower upper different
    change upd body.mem (cellOf b destination) (.val cursor) address = machine.mem address
    rw [upd_other _ _ different]
    exact below address lower upper
  · intro R old
    exact Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge state.heap value rfl)

theorem fixed_storage_path_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    (MRhs.copy path rfl).evalT state = .error .revert ∧ run (fixedStoragePathCode b path) machine = .revert := by
  constructor
  · simp only [MRhs.evalT,refused,bind,Except.bind]
  · rcases spath_sim path represented supported with ⟨actual,slot,value,source,_,_,_,_⟩ | ⟨_,failed⟩
    · rw [refused] at source
      cases source
    · exact run_append_revert failed

theorem fixed_storage_path_declaration_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.declMem (.fixed (.prim primitive) count) (some (.copy path rfl)) rfl state = .error .revert ∧
    run (fixedStoragePathDeclareCode b path) machine = .revert := by
  obtain ⟨source,failed⟩ := fixed_storage_path_refusal state machine path represented supported refused
  refine ⟨?_,run_append_revert failed⟩
  simp only [TRun.declMem,source,bind,Except.bind]

theorem fixed_storage_path_rebind_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (destination : Idx Γ (.mem (.fixed (.prim primitive) count)))
    (path : SPath C Γ (.ref (.fixed (.prim primitive) count)))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.rebindMem destination (.copy path rfl) state = .error .revert ∧
    run (fixedStoragePathRebindCode b destination path) machine = .revert := by
  obtain ⟨source,failed⟩ := fixed_storage_path_refusal state machine path represented supported refused
  refine ⟨?_,run_append_revert failed⟩
  simp only [TRun.rebindMem,source,bind,Except.bind]

def fixedStoragePath : FixedStoragePathCertificate :=
  ⟨fixed_storage_path_body,fixed_storage_path_declaration,fixed_storage_path_rebind,fixed_storage_path_refusal⟩

#print axioms fixed_storage_path_rhs
#print axioms fixed_storage_path_decl_source
#print axioms fixed_storage_path_body
#print axioms fixed_storage_path_declaration
#print axioms fixed_storage_path_rebind_source
#print axioms fixed_storage_path_rebind
#print axioms fixed_storage_path_refusal
#print axioms fixed_storage_path_declaration_refusal
#print axioms fixed_storage_path_rebind_refusal
#print axioms fixedStoragePath
end Solidity.Backend.MemoryCopies
