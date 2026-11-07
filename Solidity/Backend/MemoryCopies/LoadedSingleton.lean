import Solidity.Backend.MemoryCopies.LoadedSingletonInterface

/-! Actual existing expression compilation supplies the loaded word. Whole
storage-copy source equations require an actual singleton lookup, explicitly. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem loaded_singleton_transport (loads : List Instr) (machine : Machine) (word : Word)
    (loaded : run loads machine = .ok (machine.push word) 0) :
    run (loads ++ singletonFillCode) machine = run (singletonCopyCode word) machine := by
  rw [run_append_ok loaded]
  change run singletonFillCode (machine.push word) = run ([.push word] ++ singletonFillCode) machine
  rw [run_append_ok (show run [.push word] machine = .ok (machine.push word) 0 from rfl)]

theorem loaded_singleton_success {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    {L b frame : Nat} {frag : Frag Γ} (expression : Val C Γ primitive) (value : primitive.Denote)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : valIn frag expression = true) (evaluated : expression.evalT state = .ok value)
    (fits : cursor.val + 2 < W) : LoadedSingletonBodyResult b frame expression value state base cursor machine fits := by
  rcases val_sim expression represented.core supported with ⟨actual,word,source,representation,loaded⟩ | ⟨refused,_⟩
  · rw [evaluated] at source
    cases source
    obtain ⟨base',target,ran,allocated,root,extension,shape,below,gaps⟩ :=
      singleton_copy_result state.heap primitive value word representation base frame cursor machine allocator fits
    refine ⟨word,base',target,representation,?_,allocated,root,extension,shape,below,gaps⟩
    rw [loadedSingletonCopyCode,loaded_singleton_transport _ machine word loaded]
    exact ran
  · rw [evaluated] at refused
    cases refused

theorem loaded_singleton_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    {L b : Nat} {frag : Frag Γ} (expression : Val C Γ primitive) (state : State C Γ) (machine : Machine)
    (represented : Sim C L b frag state machine) (supported : valIn frag expression = true)
    (evaluated : expression.evalT state = .error .revert) :
    run (loadedSingletonCopyCode b expression) machine = .revert := by
  rcases val_sim expression represented supported with ⟨actual,word,source,_,_⟩ | ⟨_,refused⟩
  · rw [evaluated] at source
    cases source
  · exact run_append_revert refused

def loadedSingleton : LoadedSingletonCertificate := ⟨loaded_singleton_success,loaded_singleton_refusal⟩

theorem storage_singleton_rhs {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote)
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (singletonArrayValue primitive value)) :
    (MRhs.copy path rfl).evalT state =
      .ok (state.copyStToMG (singletonArrayValue primitive value) rfl) := by
  simp only [MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,State.copyStToMG,State.grow]

theorem storage_singleton_decl {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote)
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (singletonArrayValue primitive value)) :
    let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state =
      .ok ⟨(state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val),grown.ext⟩ := by
  rw [TRun.declMem,storage_singleton_rhs state path reference value resolved found]
  rfl

def loadedSingletonDeclareCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b : Nat) (expression : Val C Γ primitive) : List Instr :=
  loadedSingletonCopyCode b expression ++ [.mstore (cell (b + Γ.length))]

theorem loaded_singleton_declare_correct {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    {L b frame : Nat} {frag : Frag Γ} (expression : Val C Γ primitive) (value : primitive.Denote)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : valIn frag expression = true) (evaluated : expression.evalT state = .ok value)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (singletonArrayValue primitive value))
    (fits : cursor.val + 2 < W) (locals : b + (Γ.length + 1) ≤ frame) :
    let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
    let after := (state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val)
    ∃ base' target, TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
      run (loadedSingletonDeclareCode b expression) machine = .ok target 0 ∧
      Objects.StateRepr L b frame (frag.push (.mem (.array (.prim primitive))) .ok) after base' target ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + 2,fits⟩ target ∧
      BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
      base' grown.val.id = cursor ∧ target.mem (cell (b + Γ.length)) = .val cursor ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) →
        target.mem address = machine.mem address) := by
  obtain ⟨word,base',body,_,ran,allocated,root,extension,shape,below,_⟩ :=
    loaded_singleton_success expression value state base cursor machine represented allocator supported evaluated fits
  let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
  let target := writeMachine body (cell (b + Γ.length)) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,storage_singleton_decl state path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_⟩
  · rw [loadedSingletonDeclareCode,run_append_ok ran]
    rfl
  · simpa only [grown,root,target] using adopted.consMem grown.val locals
  · exact allocated.localWrite (b + Γ.length) (by omega) (by omega) (.val cursor)
  · change body.stack = machine.stack
    have stack : body.stack = ({machine with mem := body.mem} : Machine).stack := congrArg Machine.stack shape
    exact stack
  · exact upd_same _ _ _
  · intro address lower upper different
    change upd body.mem (cell (b + Γ.length)) (.val cursor) address = machine.mem address
    rw [upd_other _ _ different]
    exact below address lower upper

#print axioms loaded_singleton_transport
#print axioms loaded_singleton_success
#print axioms loaded_singleton_refusal
#print axioms loadedSingleton
#print axioms storage_singleton_rhs
#print axioms storage_singleton_decl
#print axioms loaded_singleton_declare_correct
end Solidity.Backend.MemoryCopies
