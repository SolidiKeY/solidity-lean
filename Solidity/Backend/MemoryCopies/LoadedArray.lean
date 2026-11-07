import Solidity.Backend.MemoryCopies.LoadedArrayInterface

/-! Actual existing expression loads feed the finite typed copy stores.
Source storage-path linkage is retained explicitly at declaration boundaries. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem primitive_loads_run {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (expressions : List (Val C Γ primitive)) (values : List primitive.Denote)
    (inputs : PrimitiveLoadInputs frag state expressions values) (machine : Machine)
    (represented : Sim C L b frag state machine) :
    ∃ words, words.length = expressions.length ∧ PrimitiveWords primitive values words ∧
      run (primitiveLoadsCode b expressions) machine = .ok {machine with stack := words ++ machine.stack} 0 := by
  induction expressions generalizing values machine with
  | nil =>
    have evaluated : (.ok [] : TRes (List primitive.Denote)) = .ok values := inputs.evaluation
    cases evaluated
    exact ⟨[],rfl,⟨rfl,fun index value selected => by cases index <;> cases selected⟩,rfl⟩
  | cons expression expressions ih =>
    have evaluated : (expression :: expressions).mapM (fun e => e.evalT state) = .ok values := inputs.evaluation
    cases headEval : expression.evalT state with
    | error error =>
      simp only [List.mapM_cons,headEval,bind,Except.bind] at evaluated
      cases evaluated
    | ok value =>
      cases restEval : expressions.mapM (fun e => e.evalT state) with
      | error error =>
        simp only [List.mapM_cons,headEval,restEval,bind,Except.bind] at evaluated
        cases evaluated
      | ok rest =>
        simp only [List.mapM_cons,headEval,restEval,bind,Except.bind,pure,Except.pure] at evaluated
        cases evaluated
        have tailInputs : PrimitiveLoadInputs frag state expressions rest :=
          ⟨fun e member => inputs.supported e (List.mem_cons_of_mem expression member),restEval⟩
        obtain ⟨words,length,representation,loaded⟩ := ih rest tailInputs machine represented
        rcases val_sim expression (represented.stack (words ++ machine.stack))
            (inputs.supported expression (List.mem_cons_self ..)) with
          ⟨actual,word,source,wordRepr,ran⟩ | ⟨refused,_⟩
        · rw [headEval] at source
          cases source
          refine ⟨word :: words,congrArg Nat.succ length,⟨congrArg Nat.succ representation.length,?_⟩,?_⟩
          · intro index item selected
            cases index with
            | zero => cases selected; exact ⟨word,rfl,wordRepr⟩
            | succ index => exact representation.elements index item selected
          · rw [primitiveLoadsCode,run_append_ok loaded,ran]
            rfl
        · rw [headEval] at refused
          cases refused

theorem array_stack_run (cursor : Fin W) (offset : Nat) (words : List Word) (machine : Machine)
    (fits : cursor.val + offset + words.length ≤ W) :
    run (arrayStackCode offset words.length) {machine with stack := .val cursor :: words ++ machine.stack} =
      .ok ((arrayWordsMachine cursor offset words machine).push (.val cursor)) 0 := by
  induction words generalizing offset machine with
  | nil => rfl
  | cons word words ih =>
    have shuffled : run [.swap 1,.dup 2] {machine with stack := .val cursor :: (word :: words) ++ machine.stack} =
        .ok ((({machine with stack := words ++ machine.stack}).push (.val cursor)).push word |>.push (.val cursor)) 0 := rfl
    rw [List.length_cons,arrayStackCode,List.append_assoc,run_append_ok shuffled,
      run_append_ok (writeFieldWord_run _ cursor offset word (by simp only [List.length_cons] at fits; omega))]
    exact ih (offset + 1) (writeMachine machine (cursor.val + offset) word) (by simp only [List.length_cons] at fits; omega)

theorem array_fill_run (words : List Word) (machine : Machine) (cursor : Fin W)
    (bounded : words.length < W) (cell : machine.mem 0 = .val cursor)
    (fits : cursor.val + words.length + 1 < W) :
    run (arrayFillCode words.length) {machine with stack := words ++ machine.stack} =
      .ok ((arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨words.length,bounded⟩)).push (.val cursor)) 0 := by
  have length : wmod words.length = (⟨words.length,bounded⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bounded)
  have pushed : run [.push (.val (wmod words.length))] {machine with stack := words ++ machine.stack} =
      .ok (({machine with stack := words ++ machine.stack}).push (.val ⟨words.length,bounded⟩)) 0 := by
    rw [length]
    rfl
  rw [arrayFillCode,List.append_assoc,run_append_ok pushed,
    run_append_ok (allocateArray_run {machine with stack := words ++ machine.stack} cursor _ cell)]
  exact array_stack_run cursor 1 words (allocateMachine machine cursor ⟨words.length,bounded⟩) (by omega)

theorem loaded_array_transport (loads : List Instr) (words : List Word) (machine : Machine) (cursor : Fin W)
    (loaded : run loads machine = .ok {machine with stack := words ++ machine.stack} 0)
    (bounded : words.length < W) (cell : machine.mem 0 = .val cursor)
    (fits : cursor.val + words.length + 1 < W) :
    run (loads ++ arrayFillCode words.length) machine = run (primitiveArrayCode words) machine := by
  rw [run_append_ok loaded,array_fill_run words machine cursor bounded cell fits,
    primitive_array_run words machine cursor bounded cell fits]

theorem loaded_array_success {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (expressions : List (Val C Γ primitive)) (values : List primitive.Denote) (bounded : values.length < W)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (inputs : PrimitiveLoadInputs frag state expressions values)
    (fits : cursor.val + (values.length + 1) < W) :
    LoadedArrayBodyResult b frame expressions values bounded state base cursor machine fits := by
  obtain ⟨words,count,representation,loaded⟩ := primitive_loads_run state expressions values inputs machine represented.core
  obtain ⟨base',target,ran,reached,root,extension,shape,below,gaps⟩ :=
    primitive_array_result state.heap primitive values bounded words representation base frame cursor machine allocator fits
  refine ⟨words,base',target,representation,?_,reached,root,extension,shape,below,gaps⟩
  rw [loadedArrayCode,← count,loaded_array_transport _ words machine cursor loaded
    (by rw [representation.length]; exact bounded) allocator.free.cell (by rw [representation.length]; omega)]
  exact ran

def loadedArray : LoadedArrayCertificate := ⟨loaded_array_success⟩

theorem loaded_array_head_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (expression : Val C Γ primitive) (expressions : List (Val C Γ primitive))
    (values : List primitive.Denote) (machine : Machine) (represented : Sim C L b frag state machine)
    (tailInputs : PrimitiveLoadInputs frag state expressions values) (supported : valIn frag expression = true)
    (refused : expression.evalT state = .error .revert) :
    run (loadedArrayCode b (expression :: expressions)) machine = .revert := by
  obtain ⟨words,_,_,loaded⟩ := primitive_loads_run state expressions values tailInputs machine represented
  rcases val_sim expression (represented.stack (words ++ machine.stack)) supported with
    ⟨actual,word,source,_,_⟩ | ⟨_,failed⟩
  · rw [refused] at source
    cases source
  · rw [loadedArrayCode,primitiveLoadsCode,List.append_assoc,run_append_ok loaded]
    exact run_append_revert failed

theorem storage_array_rhs {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (values : List primitive.Denote)
    (bounded : values.length < W) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded)) :
    (MRhs.copy path rfl).evalT state = .ok (state.copyStToMG (primitiveArrayValue primitive values bounded) rfl) := by
  simp only [MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,State.copyStToMG,State.grow]

theorem storage_array_decl {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (values : List primitive.Denote)
    (bounded : values.length < W) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded)) :
    let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state =
      .ok ⟨(state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val),grown.ext⟩ := by
  rw [TRun.declMem,storage_array_rhs state path reference values bounded resolved found]
  rfl

def loadedArrayDeclareCode {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (b : Nat) (expressions : List (Val C Γ primitive)) : List Instr :=
  loadedArrayCode b expressions ++ [.mstore (cell (b + Γ.length))]

theorem loaded_array_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (expressions : List (Val C Γ primitive)) (values : List primitive.Denote) (bounded : values.length < W)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (inputs : PrimitiveLoadInputs frag state expressions values)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) (locals : b + (Γ.length + 1) ≤ frame) :
    let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
    let after := (state.adopt grown).1.push (t := .mem (.array (.prim primitive))) (some grown.val)
    ∃ base' target,
      TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .ok ⟨after,grown.ext⟩ ∧
      run (loadedArrayDeclareCode b expressions) machine = .ok target 0 ∧
      Objects.StateRepr L b frame (frag.push (.mem (.array (.prim primitive))) .ok) after base' target ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
      BaseExtends state.H base base' ∧ target.stack = machine.stack ∧
      base' grown.val.id = cursor ∧ target.mem (cell (b + Γ.length)) = .val cursor ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ cell (b + Γ.length) → target.mem address = machine.mem address) := by
  obtain ⟨words,base',body,_,ran,allocated,root,extension,shape,below,_⟩ :=
    loaded_array_success expressions values bounded state base cursor machine represented allocator inputs fits
  let grown := (primitiveArrayValue primitive values bounded).copyStToM state.heap rfl
  let target := writeMachine body (cell (b + Γ.length)) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,storage_array_decl state path reference values bounded resolved found,?_,?_,?_,extension,?_,root,?_,?_⟩
  · rw [loadedArrayDeclareCode,run_append_ok ran]
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

#print axioms primitive_loads_run
#print axioms array_stack_run
#print axioms array_fill_run
#print axioms loaded_array_transport
#print axioms loaded_array_success
#print axioms loadedArray
#print axioms loaded_array_head_refusal
#print axioms storage_array_rhs
#print axioms storage_array_decl
#print axioms loaded_array_declaration
end Solidity.Backend.MemoryCopies
