import Solidity.Backend.MemoryCopies.RuntimeLiveArrayInterface

/-! Actual typed storage values, including shadows, feed the existing runtime
path copy and local binding. Source evaluation uses the unchanged MRhs/TRun. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem runtime_live_array_rhs {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : SVal (.ref (.array (.prim primitive))))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    (MRhs.copy path rfl).evalT state = .ok (state.copyStToMG value rfl) := by
  simp only [MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,State.copyStToMG,State.grow]

theorem runtime_live_array_decl_source {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : SVal (.ref (.array (.prim primitive))))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state =
      .ok ⟨(state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val),grown.ext⟩ := by
  rw [TRun.declMem,runtime_live_array_rhs state path reference value resolved found]
  rfl

theorem runtime_live_array_body {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (value : SVal (.ref (.array (.prim primitive))))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + ((primitiveArrayLiveValues value).length + 1) < W) :
    RuntimeLiveArrayBodyResult b frame path value state base cursor machine fits := by
  rcases spath_sim path represented.core supported with
    ⟨actual,slot,observedValue,resolution,live,_,sourceRepr,pathRun⟩ | ⟨refused,_⟩
  · rw [resolved] at resolution
    cases resolution
    have observed : state.storage.find reference = some observedValue := Sto.find_of_findLive live
    rw [found] at observed
    cases observed
    obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps⟩ :=
      runtime_primitive_live_success state.heap primitive value base frame cursor machine slot L allocator sourceRepr fits
    refine ⟨base',target,?_,allocated,root,extension,shape,below,gaps⟩
    rw [runtimePathArrayCode,run_append_ok pathRun]
    exact ran
  · rw [resolved] at refused
    cases refused

theorem runtime_live_array_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (value : SVal (.ref (.array (.prim primitive))))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + ((primitiveArrayLiveValues value).length + 1) < W) (locals : b + (Γ.length + 1) ≤ frame) :
    RuntimeLiveArrayDeclarationResult L b frame frag state base cursor machine path value fits := by
  obtain ⟨base',body,ran,allocated,root,extension,shape,below,_⟩ :=
    runtime_live_array_body state base cursor machine path reference value represented allocator supported resolved found fits
  let grown := value.copyStToM state.heap rfl
  let target := writeMachine body (cell (b + Γ.length)) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,runtime_live_array_decl_source state path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_⟩
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

theorem runtime_live_array_rebind_source {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (value : SVal (.ref (.array (.prim primitive))))
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.rebindMem destination (.copy path rfl) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ := by
  rw [TRun.rebindMem,runtime_live_array_rhs state path reference value resolved found]
  rfl

theorem runtime_live_array_rebind {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (value : SVal (.ref (.array (.prim primitive))))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value)
    (fits : cursor.val + ((primitiveArrayLiveValues value).length + 1) < W) :
    RuntimeLiveArrayRebindResult L b frame frag state base cursor machine destination path value fits := by
  obtain ⟨base',body,ran,allocated,root,extension,shape,below,_⟩ :=
    runtime_live_array_body state base cursor machine path reference value represented allocator supported resolved found fits
  let grown := value.copyStToM state.heap rfl
  let target := writeMachine body (cellOf b destination) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,runtime_live_array_rebind_source state destination path reference value resolved found,?_,?_,?_,
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
    exact Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge state.heap value rfl)

def runtimeLiveArray : RuntimeLiveArrayCertificate :=
  ⟨runtime_live_array_body,runtime_live_array_declaration,runtime_live_array_rebind,runtime_path_array_refusal⟩

#print axioms runtime_live_array_rhs
#print axioms runtime_live_array_decl_source
#print axioms runtime_live_array_body
#print axioms runtime_live_array_declaration
#print axioms runtime_live_array_rebind_source
#print axioms runtime_live_array_rebind
#print axioms runtimeLiveArray
end Solidity.Backend.MemoryCopies
