import tests.«internal-flow».RuntimeFrameChecks
import Solidity.Backend.InternalFlow.WorldResultEmission

namespace Solidity.Backend.InternalFlow.WorldResultEmissionChecks
open ContractWorld Backend.Failure WorldResultEmission
open RuntimeFrameChecks (world next self method context result)
open Controls (contract saved persistent transient)

def protectedLocal : Idx RuntimeFrameChecks.Final (.val .uint) := .there (.there (.there .here))

def parts : List (RevPart contract RuntimeFrameChecks.Final) :=
 [.word (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))),
  .word (.simple (.local protectedLocal)),
  .word (.read (.root "p" rfl)),.word (.read (.root "t" rfl)),.bytes [0xde,0,0xad]]
def chunks : List (List UInt8) :=
 [Semantics.wordBytes 13,Semantics.wordBytes 9,Semantics.wordBytes 23,Semantics.wordBytes 29,[0xde,0,0xad]]
def payload : List UInt8 := chunks.flatten

theorem parts_evaluate : parts.mapM (fun (part : RevPart contract RuntimeFrameChecks.Final) => part.evalT result.st) = .ok chunks := by
 have observed : (parts.mapM (fun (part : RevPart contract RuntimeFrameChecks.Final) => part.evalT result.st)).toOption = some chunks := by decide +kernel
 cases execution : parts.mapM (fun (part : RevPart contract RuntimeFrameChecks.Final) => part.evalT result.st) with
 | error halt => rw [execution] at observed; cases observed
 | ok values =>
   have same : some values = some chunks := by simpa only [execution,Except.toOption] using observed
   cases Option.some.inj same
   rfl

theorem complete_chunks : chunks.map List.length = [32,32,32,32,3] ∧ payload.length = 131 ∧
 [payload[0]!,payload[31]!,payload[32]!,payload[63]!,payload[64]!,payload[95]!,
  payload[96]!,payload[127]!,payload[128]!,payload[129]!,payload[130]!] =
 [0,13,0,9,0,23,0,29,0xde,0,0xad] := by decide +kernel

theorem actual_rejection : world.call self (rejectingEntry method parts) context =
 .error (THalt.ofData payload) :=
 world_rejection world next self method context result.st RuntimeFrameChecks.actual_world parts chunks parts_evaluate

theorem exact_class : world.call self (rejectingEntry method parts) context =
 .error (.revertWith payload) := by rw [actual_rejection];rfl

def offset : Nat := 5
def suffix : Program := [.op .ADD]
def machine : Slice.Machine :=
 ⟨[Slice.pushed [0x41],Slice.pushed [0x52],Slice.pushed [0x63]],
  fun x => if x = 4 then 0x95 else if x = 136 then 0x96 else 0x73⟩
def callerMachine : Slice.Machine := ⟨[Slice.pushed [0x10],Slice.pushed [0x11]],fun _ => 0x11⟩
def emitted : Slice.Machine := {machine with memory := Slice.putBytes machine.memory offset payload}

theorem fits : Fits offset payload := by unfold Fits;decide +kernel
theorem room : machine.stack.length + 2 ≤ 1024 := by decide +kernel

theorem checked_execution :
 checkedRuntimeRevert (world.call self (rejectingEntry method parts) context) offset suffix machine =
 some (emitted,some (.revert payload)) :=
 checked_rejection world next self method context result.st RuntimeFrameChecks.actual_world
  parts chunks parts_evaluate offset suffix machine fits room

theorem full_emitted_bytes : Slice.getBytes emitted.memory offset payload.length = payload :=
 Slice.getBytes_putBytes machine.memory offset payload

theorem protected_stack : emitted.stack = machine.stack := rfl

theorem outside_interval (x : Nat) (outside : x < offset ∨ offset + payload.length ≤ x) :
 emitted.memory x = machine.memory x := Slice.putBytes_frame machine.memory offset x payload outside

theorem complete_machine_observation :
 (checkedRuntimeRevert (world.call self (rejectingEntry method parts) context) offset suffix machine).map
 (fun output => (output.1.stack,Slice.getBytes output.1.memory offset payload.length,
  output.1.memory 4,output.1.memory 136,output.2)) =
 some (machine.stack,payload,0x95,0x96,some (.revert payload)) := by
 rw [checked_execution]
 change some (emitted.stack,Slice.getBytes emitted.memory offset payload.length,
  emitted.memory 4,emitted.memory 136,some (Roadmap.Outcome.revert payload)) = _
 rw [full_emitted_bytes,outside_interval 4 (by left;decide),
  outside_interval 136 (by right;decide +kernel)]
 rfl

def savedJournal := rootJournal persistent transient saved callerMachine
def liveJournal := rootJournal persistent transient result.st.storage machine

theorem source_snapshots :
 (savedJournal.persistent.view.1,savedJournal.transient.view.1,
  liveJournal.persistent.view.1,liveJournal.transient.view.1) = (7,9,23,29) := by
 simp only [Prod.mk.injEq]
 decide +kernel

theorem projected_local_execution :
 localRuntimeRevert (world.call self (rejectingEntry method parts) context)
  (Local.save savedJournal) offset liveJournal = some (savedJournal,.revert payload) :=
 local_rejection world next self method context result.st RuntimeFrameChecks.actual_world
  persistent transient parts chunks parts_evaluate saved callerMachine machine offset fits room

/-- A separate actual successful frame supplies the live state. Its result
handler is not a source catch or whole-world journal rollback operation. -/
theorem saved_source_is_actual : world.storage? self = some saved := RuntimeFrameChecks.stored

theorem successful_world_not_revert :
 checkedRuntimeRevert (world.call self method context) offset suffix machine = none := by
 rw [RuntimeFrameChecks.actual_call]
 rfl

def wrongOrder : List UInt8 := [0xde,0,0xad] ++ (chunks.take 4).flatten

theorem wrong_order : payload ≠ wrongOrder := by
 have first : payload[0]! ≠ wrongOrder[0]! := by decide +kernel
 intro eq
 exact first (congrArg (fun bs => bs[0]!) eq)

theorem wrong_emitted_order : Slice.getBytes emitted.memory offset payload.length ≠ wrongOrder := by
 rw [full_emitted_bytes]
 exact wrong_order

theorem rejected_capacity_premise : ¬ Fits wordLimit payload := by
 intro fit
 exact Nat.lt_irrefl _ fit.1

def overStack : Slice.Machine := {machine with stack := List.replicate 1025 (Slice.pushed [1])}

theorem rejected_stack :
 checkedRuntimeRevert (world.call self (rejectingEntry method parts) context) offset suffix overStack = none := by
 rw [actual_rejection]
 simp only [checkedRuntimeRevert,canonical_ofData,Option.bind_some]
 have bound : decide (overStack.stack.length ≤ 1024) = false := by
   change decide ((List.replicate 1025 (Slice.pushed [1])).length ≤ 1024) = false
   rw [List.length_replicate]
   rfl
 have rejected : Slice.stackSafe (emit offset (.custom payload) ++ suffix) overStack = false := by
   change (decide (overStack.stack.length ≤ 1024) && _) = false
   rw [bound]
   rfl
 simp only [Slice.checkedRun,rejected,Bool.false_eq_true,↓reduceIte]

theorem empty_rejection : world.call self (rejectingEntry method []) context = .error .revert :=
 world_rejection world next self method context result.st RuntimeFrameChecks.actual_world [] [] rfl

def panicMethod : Entry contract Unit :=
 ⟨method.locals,method.body,fun _ => .error .panic,method.payable⟩

theorem panic_frame : world.callFrame self panicMethod context = .ok (next,result.st) :=
 RuntimeFrameChecks.actual_world

theorem actual_panic : world.call self panicMethod context = .error .panic :=
 RuntimeWorld.decode_failure world next self panicMethod context result.st .panic panic_frame rfl

theorem panic_not_revert : checkedRuntimeRevert (world.call self panicMethod context) offset suffix machine = none := by
 rw [actual_panic]
 rfl

namespace InsideCallee
open Controls (arrayType)
open RuntimeFrameChecks (caller args ret body initial before decode)
private theorem actual {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by
  cases r with | error e => cases h | ok value => rfl

def arguments : TEnv contract caller.st.H [.mem arrayType] :=
 (args.evalT caller.st).toOption.get (by decide +kernel)
def callEntry := ret.enterT (caller.st.withEnv arguments)
def out : Out contract callEntry.st.H (.mem arrayType :: RuntimeFrameChecks.Input) :=
 (body.runR callEntry.st).toOption.get (by decide +kernel)
theorem args_run : args.evalT caller.st = .ok arguments := actual _ _
theorem prefix_run : body.runR callEntry.st = .ok out := actual _ _

def privateCell : Idx (.mem arrayType :: RuntimeFrameChecks.Input) (.mem arrayType) := .here
def resultCell : Idx (.mem arrayType :: RuntimeFrameChecks.Input) (.mem arrayType) := .there .here
def oldCell : Idx (.mem arrayType :: RuntimeFrameChecks.Input) (.mem arrayType) := .there (.there .here)
def parts : List (RevPart contract (.mem arrayType :: RuntimeFrameChecks.Input)) :=
 [.word (.readMem (.index .dyn (.var privateCell rfl) (.simple (.lit 1 rfl)))),
  .word (.readMem (.index .dyn (.var resultCell rfl) (.simple (.lit 0 rfl)))),
  .word (.readMem (.index .dyn (.var oldCell rfl) (.simple (.lit 1 rfl)))),
  .word (.read (.root "p" rfl)),.word (.read (.root "t" rfl)),.bytes [0xde,0,0xad]]
def chunks : List (List UInt8) :=
 [Semantics.wordBytes 17,Semantics.wordBytes 13,Semantics.wordBytes 11,
  Semantics.wordBytes 23,Semantics.wordBytes 29,[0xde,0,0xad]]
def payload : List UInt8 := chunks.flatten

theorem parts_evaluate : parts.mapM (fun (part : RevPart contract (.mem arrayType :: RuntimeFrameChecks.Input)) => part.evalT out.st) = .ok chunks := by
 have observed : (parts.mapM (fun (part : RevPart contract (.mem arrayType :: RuntimeFrameChecks.Input)) => part.evalT out.st)).toOption = some chunks := by decide +kernel
 cases execution : parts.mapM (fun (part : RevPart contract (.mem arrayType :: RuntimeFrameChecks.Input)) => part.evalT out.st) with
 | error halt => rw [execution] at observed;cases observed
 | ok values =>
   have same : some values = some chunks := by simpa only [execution,Except.toOption] using observed
   cases Option.some.inj same
   rfl

theorem frame_phases :
 (callEntry.st.H.length,callEntry.st.env.1.map HRef.id,
  AllocationFrameChecks.contents callEntry.st .here,out.st.H.length,
  out.st.env.1.map HRef.id,out.st.env.2.1.map HRef.id,out.st.env.2.2.1.map HRef.id,
  AllocationFrameChecks.contents out.st privateCell,
  AllocationFrameChecks.contents out.st resultCell,
  AllocationFrameChecks.contents out.st oldCell,
  (out.st.storage.get persistent.declared).view.1,(out.st.storage.get transient.declared).view.1) =
 (2,some 1,some [],3,some 2,some 2,some 0,some [13,17],some [13,17],some [7,11],23,29) := by
 simp only [Prod.mk.injEq]
 decide +kernel

theorem complete_chunks : chunks.map List.length = [32,32,32,32,32,3] ∧ payload.length = 163 ∧
 [payload[31]!,payload[63]!,payload[95]!,payload[127]!,payload[159]!,payload[160]!,payload[161]!,payload[162]!] =
 [17,13,11,23,29,0xde,0,0xad] := by decide +kernel

def failing := RuntimeWorld.concat body (.cons (.revertData parts) .nil)
def operation : Entry contract (Option Nat) := RuntimeWorld.entry before "insideCallee" args ret failing RuntimeFrameChecks.decode false

theorem actual_world_failure : world.call self operation context = .error (THalt.ofData payload) :=
 world_callee_rejection (k := ()) world self context before "insideCallee" args ret body parts chunks RuntimeFrameChecks.decode false
  saved initial caller arguments out rfl rfl RuntimeFrameChecks.stored RuntimeFrameChecks.entered
  RuntimeFrameChecks.prefix_run args_run prefix_run parts_evaluate

def machine : Slice.Machine :=
 {WorldResultEmissionChecks.machine with
  memory := fun x => if x = 4 then 0x95 else if x = 168 then 0x97 else 0x73}
def emitted : Slice.Machine := {machine with memory := Slice.putBytes machine.memory offset payload}
def live := rootJournal persistent transient out.st.storage machine

theorem fits : Fits offset payload := by unfold Fits;decide +kernel
theorem room : machine.stack.length + 2 ≤ 1024 := by decide +kernel

theorem checked_execution :
 checkedRuntimeRevert (world.call self operation context) offset suffix machine =
 some (emitted,some (.revert payload)) :=
 checked_runtime_revert _ _ actual_world_failure offset suffix machine fits room

theorem full_bytes : Slice.getBytes emitted.memory offset payload.length = payload :=
 Slice.getBytes_putBytes machine.memory offset payload

theorem projected_execution :
 localRuntimeRevert (world.call self operation context) (Local.save savedJournal) offset live =
 some (savedJournal,.revert payload) :=
 local_runtime_revert _ _ actual_world_failure _ offset live fits room

theorem protected_stack : emitted.stack = machine.stack := rfl

theorem outside_interval (x : Nat) (outside : x < offset ∨ offset + payload.length ≤ x) :
 emitted.memory x = machine.memory x := Slice.putBytes_frame machine.memory offset x payload outside

theorem complete_machine_observation :
 (checkedRuntimeRevert (world.call self operation context) offset suffix machine).map
 (fun output => (output.1.stack,Slice.getBytes output.1.memory offset payload.length,
  output.1.memory 4,output.1.memory 168,output.2)) =
 some (machine.stack,payload,0x95,0x97,some (.revert payload)) := by
 rw [checked_execution]
 change some (emitted.stack,Slice.getBytes emitted.memory offset payload.length,
  emitted.memory 4,emitted.memory 168,some (Roadmap.Outcome.revert payload)) = _
 rw [full_bytes,protected_stack,outside_interval 4 (by left;decide),
  outside_interval 168 (by right;decide +kernel)]
 rfl

/-- Caller-result payload131 is not this callee-local payload163. -/
theorem not_caller_payload : payload ≠ WorldResultEmissionChecks.payload := by
 have lengths : payload.length ≠ WorldResultEmissionChecks.payload.length := by decide +kernel
 intro eq
 exact lengths (congrArg List.length eq)
end InsideCallee

#print axioms Solidity.Backend.InternalFlow.WorldResultEmission.same_frame
#print axioms Solidity.Backend.InternalFlow.WorldResultEmission.world_rejection
#print axioms Solidity.Backend.InternalFlow.WorldResultEmission.checked_rejection
#print axioms Solidity.Backend.InternalFlow.WorldResultEmission.local_rejection
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.parts_evaluate
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.complete_chunks
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.actual_rejection
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.exact_class
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.checked_execution
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.full_emitted_bytes
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.protected_stack
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.outside_interval
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.complete_machine_observation
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.source_snapshots
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.projected_local_execution
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.saved_source_is_actual
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.successful_world_not_revert
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.wrong_order
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.wrong_emitted_order
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.rejected_capacity_premise
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.rejected_stack
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.empty_rejection
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.panic_frame
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.actual_panic
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.panic_not_revert
#print axioms Solidity.Backend.InternalFlow.WorldResultEmission.callee_rejection
#print axioms Solidity.Backend.InternalFlow.WorldResultEmission.frame_failure
#print axioms Solidity.Backend.InternalFlow.WorldResultEmission.world_callee_rejection
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.args_run
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.prefix_run
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.parts_evaluate
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.frame_phases
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.complete_chunks
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.actual_world_failure
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.checked_execution
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.full_bytes
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.projected_execution
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.complete_machine_observation
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.not_caller_payload
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.protected_stack
#print axioms Solidity.Backend.InternalFlow.WorldResultEmissionChecks.InsideCallee.outside_interval
end Solidity.Backend.InternalFlow.WorldResultEmissionChecks
