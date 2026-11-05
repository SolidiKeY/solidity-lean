import Solidity.Backend.MemoryCopies.RuntimePathArrayInterface

/-! Existing path simulation supplies the actual represented storage operand
for runtime array copying, then existing local stores bind its fresh identity. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem runtime_path_array_body {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) :
    RuntimePathArrayBodyResult b frame path values bounded state base cursor machine fits := by
  rcases spath_sim path represented.core supported with
    ⟨actual,slot,value,resolution,live,_,sourceRepr,pathRun⟩ | ⟨refused,_⟩
  · rw [resolved] at resolution
    cases resolution
    have observed : state.storage.find reference = some value := Sto.find_of_findLive live
    rw [found] at observed
    cases observed
    obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps⟩ :=
      runtime_storage_array_success state.heap primitive values bounded base frame cursor machine slot L allocator sourceRepr fits
    refine ⟨base',target,?_,allocated,root,extension,shape,below,gaps⟩
    rw [runtimePathArrayCode,run_append_ok pathRun]
    exact ran
  · rw [resolved] at refused
    cases refused

theorem runtime_path_array_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) (locals : b + (Γ.length + 1) ≤ frame) :
    RuntimePathArrayDeclarationResult L b frame frag state base cursor machine path values bounded fits := by
  obtain ⟨base',body,ran,allocated,root,extension,shape,below,_⟩ :=
    runtime_path_array_body state base cursor machine path reference values bounded represented allocator supported resolved found fits
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  let target := writeMachine body (cell (b + Γ.length)) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,storage_array_decl state path reference values bounded resolved found,?_,?_,?_,extension,?_,root,?_,?_⟩
  · rw [runtimePathArrayDeclareCode,run_append_ok ran]
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

theorem runtime_path_array_rebind_source {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded)) :
    let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
    TRun.rebindMem destination (.copy path rfl) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ := by
  rw [TRun.rebindMem,storage_array_rhs state path reference values bounded resolved found]
  rfl

theorem runtime_path_array_rebind {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) :
    RuntimePathArrayRebindResult L b frame frag state base cursor machine destination path values bounded fits := by
  obtain ⟨base',body,ran,allocated,root,extension,shape,below,_⟩ :=
    runtime_path_array_body state base cursor machine path reference values bounded represented allocator supported resolved found fits
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  let target := writeMachine body (cellOf b destination) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,runtime_path_array_rebind_source state destination path reference values bounded resolved found,?_,?_,?_,
    extension,?_,root,?_,?_,SVal.keeps_copyStToM _ rfl state.heap,?_⟩
  · rw [runtimePathArrayRebindCode,run_append_ok ran]
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
    exact Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge state.heap (primitiveArrayValue primitive values bounded) rfl)

theorem runtime_path_array_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    (MRhs.copy path rfl).evalT state = .error .revert ∧ run (runtimePathArrayCode b path) machine = .revert := by
  constructor
  · simp only [MRhs.evalT,refused,bind,Except.bind]
  · rcases spath_sim path represented supported with ⟨actual,slot,value,source,_,_,_,_⟩ | ⟨_,failed⟩
    · rw [refused] at source
      cases source
    · exact run_append_revert failed

theorem runtime_path_array_declaration_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .error .revert ∧
    run (runtimePathArrayDeclareCode b path) machine = .revert := by
  obtain ⟨source,failed⟩ := runtime_path_array_refusal state machine path represented supported refused
  refine ⟨?_,run_append_revert failed⟩
  simp only [TRun.declMem,source,bind,Except.bind]

theorem runtime_path_array_rebind_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.rebindMem destination (.copy path rfl) state = .error .revert ∧
    run (runtimePathArrayRebindCode b destination path) machine = .revert := by
  obtain ⟨source,failed⟩ := runtime_path_array_refusal state machine path represented supported refused
  refine ⟨?_,run_append_revert failed⟩
  simp only [TRun.rebindMem,source,bind,Except.bind]

def runtimePathArray : RuntimePathArrayCertificate :=
  ⟨runtime_path_array_body,runtime_path_array_declaration,runtime_path_array_rebind,runtime_path_array_refusal⟩

#print axioms runtime_path_array_body
#print axioms runtime_path_array_declaration
#print axioms runtime_path_array_rebind_source
#print axioms runtime_path_array_rebind
#print axioms runtime_path_array_refusal
#print axioms runtime_path_array_declaration_refusal
#print axioms runtime_path_array_rebind_refusal
#print axioms runtimePathArray
end Solidity.Backend.MemoryCopies
