import Solidity.Yul.World.CallbackSuccess

namespace Solidity.Yul.World.CallbackSuccess
open Solidity.Source
open Solidity.Roadmap (Outcome Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

theorem invoke_actual (G : Glob env) (out : Outcome) :
    CallerFrame.liftInvoke (invoke G out) observed
      (enter caller CallerFrameChecks.residual parent .call CallerFrameChecks.target 0 [17,34,51,68])
      .call CallerFrameChecks.target 10000 [17,34,51,68]
      ⟨⟨caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ =
      some ((.ok out,⟨⟨after out,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),suffix out) := by
  have ran : invoke G out observed
      (enter caller CallerFrameChecks.residual parent .call CallerFrameChecks.target 0 [17,34,51,68])
      .call CallerFrameChecks.target 10000 [17,34,51,68]
      ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ =
      some ((.ok out,⟨⟨⟨Source.L0 env,(after out).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),suffix out) := by
    let src := (Source.callAddr (callbackGlob G out)
      {this:=CallerFrameChecks.owner,sender:=CallerFrameChecks.owner,value:=0,static:=false,contract:="ModifierCallback",checked:=true,depth:=0,cd:=[]} 10 CallerFrameChecks.target 0 [17,34,51,68] false).run
        (Source.L0 env,caller.2)
    change some ((src.1,(⟨⟨src.2,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ : Carrier env [])),
      (src.2.2.events.drop caller.2.events.length).map Observation.event) = _
    have actual : src=(.ok out,(Source.L0 env,(after out).2)) := source_run G out
    rw [actual]
    rfl
  exact CallerFrame.liftInvoke_exact (invoke G out) observed
    (enter caller CallerFrameChecks.residual parent .call CallerFrameChecks.target 0 [17,34,51,68])
    .call CallerFrameChecks.target 10000 [17,34,51,68]
    ⟨⟨caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ (.ok out)
    ⟨⟨⟨Source.L0 env,(after out).2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ (suffix out) ran

theorem completion (out : Outcome) :
    finish caller CallerFrameChecks.encoding observed
      (enter caller CallerFrameChecks.residual parent .call CallerFrameChecks.target 0 [17,34,51,68])
      ⟨⟨after out,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ (suffix out) out = result out := by
  cases out <;> rfl

theorem call_actual (G : Glob env) (out : Outcome) :
    call (CallerFrame.liftInvoke (invoke G out)) caller CallerFrameChecks.residual CallerFrameChecks.encoding observed rfl
      PhysicalCompletionChecks.memory parent .call CallerFrameChecks.target 10000 0 160 4 = some (.ok out,result out) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some [17,34,51,68] := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  rw [call_normal_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (invoke_actual G out),completion]

theorem frame (out : Outcome) :
    (result out).1.1.1.1=caller.1 ∧ (result out).1.1.1.2.heap=caller.2.heap ∧
    (result out).1.1.1.2.fnLocals=caller.2.fnLocals ∧ (result out).1.1.1.2.logs=caller.2.logs ∧
    (result out).1.1.1.2.events=events out ∧ (result out).1.1.2=CallerFrameChecks.residual ∧
    (result out).1.2=CallerFrameChecks.encoding ∧ (result out).2.trace=observed.trace++suffix out ∧
    (result out).2.effects.returndata=returnData out := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem receiver_balance : ((result (.success [1])).2.effects.execution.world.accounts CallerFrameChecks.receiver).balance=30 ∧
    ((result (.revert [2])).2.effects.execution.world.accounts CallerFrameChecks.receiver).balance=23 ∧
    (result (.success [1])).2.effects.execution.journal.length=3 ∧ (result (.revert [2])).2.effects.execution.journal.length=2 :=
  ⟨rfl,rfl,rfl,rfl⟩

def partialSuffix : List Observation :=
  [.event (.call CallerFrameChecks.target 0 [17,34,51,68] false),
   .event (.reenter CallerFrameChecks.receiver CallerFrameChecks.target 7 [] false)]
def partialState : Source.EMState env [.bytes .memory] :=
  ⟨caller.1,{caller.2 with ex:=credited,events:=caller.2.events++
    [.call CallerFrameChecks.target 0 [17,34,51,68] false,
     .reenter CallerFrameChecks.receiver CallerFrameChecks.target 7 [] false]}⟩
def partialResult : Result env [.bytes .memory] :=
  pending observed ⟨⟨partialState,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ partialSuffix

theorem source_timeout (G : Glob env) (out : Outcome) :
    (Source.callAddr (callbackGlob G out) {this:=CallerFrameChecks.owner,sender:=CallerFrameChecks.owner,value:=0,static:=false,contract:="ModifierCallback",checked:=true,depth:=0,cd:=[]}
      8 CallerFrameChecks.target 0 [17,34,51,68] false).run (Source.L0 env,caller.2) =
      (.error .timeout,(Source.L0 env,partialState.2)) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem prefix_invoke (G : Glob env) (out : Outcome) :
    CallerFrame.liftInvoke (prefixInvoke G out) observed
      (enter caller CallerFrameChecks.residual parent .call CallerFrameChecks.target 0 [17,34,51,68])
      .call CallerFrameChecks.target 10000 [17,34,51,68]
      ⟨⟨caller,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩ =
      some ((.error .timeout,⟨⟨partialState,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩),partialSuffix) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem prefix_call (G : Glob env) out :
    call (CallerFrame.liftInvoke (prefixInvoke G out)) caller CallerFrameChecks.residual CallerFrameChecks.encoding observed rfl
      PhysicalCompletionChecks.memory parent .call CallerFrameChecks.target 10000 0 160 4 = some (.error .timeout,partialResult) := by
  have loaded : PhysicalHeapPort.port.load PhysicalCompletionChecks.memory 160 4=some [17,34,51,68] := by
    rw [PhysicalHeapPort.load_view _ _ _ (by decide)]
    exact congrArg some (bytesObject_payload_list _ _ _ 128)
  exact call_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl loaded (prefix_invoke G out)

theorem dirty_prefix_frame : partialResult.1.1.1.1=caller.1 ∧ partialResult.1.1.1.2.heap=caller.2.heap ∧
    partialResult.1.1.1.2.fnLocals=caller.2.fnLocals ∧ partialResult.1.1.1.2.logs=caller.2.logs ∧
    (partialResult.1.1.1.2.ex.world.accounts CallerFrameChecks.receiver).balance=30 ∧
    partialResult.1.1.1.2.ex.journal.length=3 ∧ partialResult.1.1.2=CallerFrameChecks.residual ∧
    partialResult.1.2=CallerFrameChecks.encoding ∧ partialResult.2.trace=observed.trace++partialSuffix ∧
    partialResult.2.effects.returndata=observed.effects.returndata := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem output_copy : copyOutput (result (.revert [0xde,0xad,0xbe])) rfl PhysicalCompletionChecks.placement
    0 false [17,34,51,68] rfl PhysicalCompletionChecks.memory 1 2 =
      (result (.revert [0xde,0xad,0xbe]),some ((Solidity.Backend.Environment.writeBytes PhysicalCompletionChecks.memory 161 [0xde,0xad],
        withSourceHeap (after (.revert [0xde,0xad,0xbe])) (PhysicalCompletionChecks.heap.write 0 (.bytes [17,0xde,0xad,68]) rfl)),
        (CallerFrameChecks.residual,CallerFrameChecks.encoding),(result (.revert [0xde,0xad,0xbe])).2)) :=
  copyOutput_exact (result (.revert [0xde,0xad,0xbe])) rfl PhysicalCompletionChecks.placement 0 false [17,34,51,68] rfl
    PhysicalCompletionChecks.memory 1 2 (by decide) (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem nonempty_caller : caller.2.heap.next=1 ∧ caller.2.ex.journal.length=2 ∧
    CallerFrameChecks.residual.journal.length=1 ∧ CallerFrameChecks.encoding.journal.length=1 := ⟨rfl,rfl,rfl,rfl⟩

theorem static_refusal (G : Glob env) out :
    invoke G out observed
      (enter caller CallerFrameChecks.residual parent .staticcall CallerFrameChecks.target 0 [17,34,51,68])
      .staticcall CallerFrameChecks.target 10000 [17,34,51,68]
      ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem ordered_success_not_timeout : suffix (.success []) ≠ partialSuffix := by decide

theorem ordered_success_not_failure : suffix (.success []) ≠ CallbackChecks.suffix (.success []) := by decide

theorem no_fresh_timeout_buffer : partialResult.2.effects.returndata ≠ [0xde,0xad] := by decide

def unregistered : Carrier env [] :=
  ⟨⟨⟨Source.L0 env,{caller.2 with ex:=caller.2.ex.apply (.account CallerFrameChecks.receiver (fun a=>{a with code:=none}))}⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩
def overflow : Carrier env [] :=
  ⟨⟨⟨Source.L0 env,{caller.2 with ex:=caller.2.ex.apply (.account CallerFrameChecks.receiver
    (fun a=>a.withBalance ⟨2^256-1,by decide⟩))}⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩

theorem registration_refusal (G : Glob env) out : invoke G out observed
    (enter caller CallerFrameChecks.residual parent .call CallerFrameChecks.target 0 [])
    .call CallerFrameChecks.target 10000 [] unregistered=none := rfl

theorem range_refusal (G : Glob env) out : invoke G out observed
    (enter caller CallerFrameChecks.residual parent .call CallerFrameChecks.target 0 [])
    .call CallerFrameChecks.target 10000 [] overflow=none := rfl

theorem context_refusal (G : Glob env) out : invoke G out observed
    (enter caller CallerFrameChecks.residual parent .call ⟨33,by decide⟩ 0 [])
    .call CallerFrameChecks.target 10000 [] ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem precompile_refusal (G : Glob env) out : invoke G out observed
    (enter caller CallerFrameChecks.residual parent .call ⟨1,by decide⟩ 0 [])
    .call ⟨1,by decide⟩ 10000 [] ⟨⟨⟨Source.L0 env,caller.2⟩,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩=none := rfl

theorem missing_modifier (G : Glob env) :
    (Source.runMods {G with prog:={G.prog with body:=fun _=>none}}
      {this:=CallerFrameChecks.receiver,sender:=CallerFrameChecks.target,value:=7,static:=false,contract:="Finite",checked:=true,depth:=2,cd:=[]} 2 fallbackBody
      [⟨modifierDecl,[],.nil⟩] (Source.L0 env)).run (Source.L0 env,caller.2)=
      (.error (.stuck "modifier without a body"),(Source.L0 env,caller.2)) := rfl

def copiedState := withSourceHeap (after (.revert [0xde,0xad,0xbe]))
  (PhysicalCompletionChecks.heap.write 0 (.bytes [17,0xde,0xad,68]) rfl)

theorem owner_MemOK (out : Outcome) : Source.MemOK env PhysicalCompletionChecks.heap.ty (result out).1.1.1 := by
  have ok : HeapOK (E:=env) PhysicalCompletionChecks.heap := HeapOK.alloc HeapOK.empty (.bytes [17,34,51,68])
  have shaped : HeapShaped (E:=env) PhysicalCompletionChecks.heap := HeapShaped.alloc (E:=env)
    (x:=⟨.bytes .memory,.bytes [17,34,51,68]⟩) HeapShaped.empty trivial
  have inner : HeapInner (E:=env) PhysicalCompletionChecks.heap := HeapInner.alloc (E:=env)
    (x:=⟨.bytes .memory,.bytes [17,34,51,68]⟩) HeapInner.empty trivial
  cases out <;> exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩,shaped,inner⟩

theorem exact_state_copy : HeapWindow.copyStateWindow (result (.revert [0xde,0xad,0xbe])).2.effects
    (result (.revert [0xde,0xad,0xbe])).1.1.1 PhysicalCompletionChecks.placement 0 false [17,34,51,68] rfl
    PhysicalCompletionChecks.memory 1 0 2 =
      some (Solidity.Backend.Environment.writeBytes PhysicalCompletionChecks.memory 161 [0xde,0xad],copiedState) :=
  HeapWindow.copyStateWindow_exact _ _ _ _ _ _ [0xde,0xad] rfl _ 1 0 2 rfl (by decide)
    (congrArg Fin.val (bytesObject_header _ _ _ 128)) (bytesObject_payload_list _ _ _ 128)

theorem copied_owner_MemOK : Source.MemOK env PhysicalCompletionChecks.heap.ty copiedState :=
  HeapWindow.copyStateWindow_memOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ exact_state_copy (owner_MemOK (.revert [0xde,0xad,0xbe]))

theorem copied_aliases :
    (Source.bytesOfRV (E:=env) {this:=CallerFrameChecks.owner,sender:=CallerFrameChecks.sender,value:=0,static:=false,contract:="Finite",checked:=true,depth:=0,cd:=[]} 1
      (.val (copiedState.1.get .here))).run copiedState = (.ok [17,0xde,0xad,68],copiedState) ∧
    (Source.bytesOfRV (E:=env) {this:=CallerFrameChecks.owner,sender:=CallerFrameChecks.sender,value:=0,static:=false,contract:="Finite",checked:=true,depth:=0,cd:=[]} 1
      (.val (copiedState.2.fnLocals.2.get .here))).run copiedState = (.ok [17,0xde,0xad,68],copiedState) := ⟨rfl,rfl⟩

end Solidity.Yul.World.CallbackSuccess
