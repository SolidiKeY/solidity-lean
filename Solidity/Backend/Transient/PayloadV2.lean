import Solidity.Backend.Transient.Frames
import Solidity.Backend.Failure.Slice

/-! H273/H57 payload-carrying transient target evaluator. Guards the regression
where v1 refuses a real nonempty byte REVERT after transient writes. V1 remains
unchanged. Reuses its bank/journal/word machine and the existing exact byte
slice; no Source/world, gas, code-selection or call-entry adequacy is claimed. -/
namespace Solidity.Backend.Transient.PayloadV2
abbrev Memory := Failure.Slice.Memory

inductive Result where
  | ok (state : Transient.State) (memory : Memory)
  | exit (outcome : Roadmap.Outcome) (state : Transient.State) (memory : Memory)
  | error (fault : Fault) (state : Transient.State) (memory : Memory)

/-- Retain every v1 failure class, including unsupported and symbolic. -/
def lift (memory : Memory) : Transient.Result → Result
  | .ok state => .ok state memory
  | .error fault state => .error fault state memory

/-- Execute the existing byte semantics on the numeric operand prefix.
The complete older word stack is preserved, including symbolic saved words. -/
def byteStep (i : Instr) (state : Transient.State) (memory : Memory) : Result :=
  match state.machine.stack with
  | .val a :: .val b :: tail =>
    match Failure.Slice.step i ⟨[a,b],memory⟩ with
    | none => .error .unsupported state memory
    | some (next, outcome) =>
      let reached := {state with machine := {state.machine with
        stack := next.stack.map Evm.Word.val ++ tail}}
      match outcome with
      | none => .ok reached next.memory
      | some out => .exit out reached next.memory
  | [] | [_] => .error .underflow state memory
  | _ => .error .symbolic state memory

def step (owner : Roadmap.Address) (static : Bool) (i : Instr)
    (state : Transient.State) (memory : Memory) : Result :=
  match i with
  | .op .MSTORE8 | .op .REVERT => byteStep i state memory
  | _ => lift memory (Transient.step owner static i state)

def run (owner : Roadmap.Address) (static : Bool) : Program → Transient.State → Memory → Result
  | [], state, memory => .ok state memory
  | i::code, state, memory => match step owner static i state memory with
    | .ok reached bytes => run owner static code reached bytes
    | .exit out reached bytes => .exit out reached bytes
    | .error fault reached bytes => .error fault reached bytes

/-- A real nonempty read is retained in full; no payload is supplied as outcome. -/
theorem revert_actual (owner : Roadmap.Address) (static : Bool)
    (state : Transient.State) (memory : Memory) (offset size : Word) (tail : List Evm.Word)
    (stack : state.machine.stack = .val offset :: .val size :: tail) :
    step owner static (.op .REVERT) state memory =
      .exit (.revert (Failure.Slice.getBytes memory offset.val size.val))
        {state with machine := {state.machine with stack := tail}} memory := by
  first | rfl | simp only [step,byteStep,stack,Failure.Slice.step,List.map_nil,List.nil_append]

theorem store_byte_actual (owner : Roadmap.Address) (static : Bool)
    (state : Transient.State) (memory : Memory) (offset value : Word) (tail : List Evm.Word)
    (stack : state.machine.stack = .val offset :: .val value :: tail) :
    step owner static (.op .MSTORE8) state memory =
      .ok {state with machine := {state.machine with stack := tail}}
        (Failure.Slice.putByte memory offset.val (UInt8.ofNat value.val)) := by
  first | rfl | simp only [step,byteStep,stack,Failure.Slice.step,List.map_nil,List.nil_append]

theorem push_actual (owner : Roadmap.Address) (static : Bool)
    (state : Transient.State) (memory : Memory) (value : Word) :
    step owner static (pushWord value) state memory =
      .ok {state with machine := state.machine.push (.val value)} memory := by
  change lift memory (Transient.step owner static (pushWord value) state) = _
  rw [push_exact]
  rfl

/-- V1 TSTORE's real static refusal remains an error, never a payload exit. -/
theorem static_store (owner : Roadmap.Address) (state : Transient.State) (memory : Memory)
    (key value : Word) (tail : List Evm.Word)
    (stack : state.machine.stack = .val key :: .val value :: tail) :
    step owner true (.op .TSTORE) state memory = .error .staticWrite state memory := by
  change lift memory (Transient.step owner true (.op .TSTORE) state) = _
  rw [static_refusal owner state key value tail stack]
  rfl

/-- General composition, retaining actual payload exits and all fault classes. -/
theorem run_append (owner : Roadmap.Address) (static : Bool) (first second : Program)
    (state : Transient.State) (memory : Memory) :
    run owner static (first++second) state memory =
      match run owner static first state memory with
      | .ok reached bytes => run owner static second reached bytes
      | .exit out reached bytes => .exit out reached bytes
      | .error fault reached bytes => .error fault reached bytes := by
  induction first generalizing state memory with
  | nil => rfl
  | cons i code ih =>
    simp only [List.cons_append,run]
    cases step owner static i state memory with
    | ok reached bytes => exact ih reached bytes
    | exit out reached bytes => rfl
    | error fault reached bytes => rfl

/-- Caller memory is frame-local. Unsupported/symbolic adapter failures retain
reached state; completed revert restores the full caller machine/bank/journal. -/
def finish (entry : Transient.State) (callerMemory : Memory) : Result → Result
  | .ok child _ => .ok {child with machine := entry.machine} callerMemory
  | .exit (.success data) child _ =>
    .exit (.success data) {child with machine := entry.machine} callerMemory
  | .exit (.revert data) dirty _ =>
    .exit (.revert data) {rollback entry.journal.length dirty with machine := entry.machine} callerMemory
  | .error .unsupported dirty bytes => .error .unsupported dirty bytes
  | .error .symbolic dirty bytes => .error .symbolic dirty bytes
  | .error why dirty _ =>
    .error why {rollback entry.journal.length dirty with machine := entry.machine} callerMemory

def callback (owner : Roadmap.Address) (static : Bool) (code : Program)
    (entry : Transient.State) (memory : Memory) : Result :=
  finish entry memory (run owner static code
    {entry with machine := {entry.machine with stack := []}} memory)

/-- Complete arbitrary-history rollback; not a reachability assumption. -/
theorem finish_writes_revert (entry : Transient.State) (prior : List Write)
    (callerMemory dirtyMemory : Memory) (payload : Roadmap.Bytes) :
    finish entry callerMemory (.exit (.revert payload) (writes entry prior) dirtyMemory) =
      .exit (.revert payload) entry callerMemory := by
  simp only [finish,rollback_writes]

/-- Existing TSTORE program is actually executed in the new evaluator. -/
theorem store_code (owner : Roadmap.Address) (state : Transient.State) (memory : Memory)
    (key value : Word) :
    run owner false (Transient.storeCode key value) state memory =
      .ok (write state owner key value) memory := by
  simp only [Transient.storeCode,run,push_actual]
  simp only [step,lift,Transient.step,Evm.Machine.push,Bool.false_eq_true,if_false]
  rfl

theorem byte_store_pushed (owner : Roadmap.Address) (static : Bool)
    (state : Transient.State) (memory : Memory) (offset value : Word) :
    step owner static (.op .MSTORE8)
      {state with machine := (state.machine.push (.val value)).push (.val offset)} memory =
      .ok state (Failure.Slice.putByte memory offset.val (UInt8.ofNat value.val)) := by
  exact store_byte_actual owner static _ memory offset value state.machine.stack rfl

theorem revert_pushed (owner : Roadmap.Address) (static : Bool)
    (state : Transient.State) (memory : Memory) (offset size : Word) :
    step owner static (.op .REVERT)
      {state with machine := (state.machine.push (.val size)).push (.val offset)} memory =
      .exit (.revert (Failure.Slice.getBytes memory offset.val size.val)) state memory := by
  exact revert_actual owner static _ memory offset size state.machine.stack rfl

/-- Fixed-width existing Backend PUSHes, actual byte store, and actual REVERT. -/
def byteRevertCode (offset value : Word) : Program :=
  [pushWord value,pushWord offset,.op .MSTORE8,pushWord ⟨1,by decide⟩,
    pushWord offset,.op .REVERT]

theorem byte_revert_run (owner : Roadmap.Address) (static : Bool)
    (state : Transient.State) (memory : Memory) (offset value : Word) :
    run owner static (byteRevertCode offset value) state memory =
      .exit (.revert [UInt8.ofNat value.val]) state
        (Failure.Slice.putByte memory offset.val (UInt8.ofNat value.val)) := by
  simp only [byteRevertCode,run,push_actual]
  rw [byte_store_pushed]
  dsimp only
  rw [revert_pushed]
  simp only [Failure.Slice.getBytes,Failure.Slice.putByte]
  rfl

/-- Actual TSTORE followed by an executed nonempty byte REVERT restores the
entire original caller machine, bank, journal and byte memory. Entry may have
an arbitrary nonempty caller prefix; no successful/reverted run is a premise. -/
theorem callback_store_byte_revert (owner : Roadmap.Address) (entry : Transient.State)
    (memory : Memory) (key stored offset byteValue : Word) :
    callback owner false (Transient.storeCode key stored ++ byteRevertCode offset byteValue)
      entry memory = .exit (.revert [UInt8.ofNat byteValue.val]) entry memory := by
  have restored : rollback entry.journal.length
      (write {entry with machine := {entry.machine with stack := []}} owner key stored) =
      {entry with machine := {entry.machine with stack := []}} :=
    rollback_write _ owner key stored
  simp only [callback,run_append,store_code,byte_revert_run,finish]
  rw [restored]

/-- Existing caller journal prefixes are preserved verbatim by the actual
reverting child, rather than projected to bank-value equality. -/
theorem callback_preserves_prefix (owner : Roadmap.Address) (entry : Transient.State)
    (callerPrefix : List Write) (memory : Memory) (key stored offset byteValue : Word) :
    callback owner false (Transient.storeCode key stored ++ byteRevertCode offset byteValue)
      (writes entry callerPrefix) memory =
      .exit (.revert [UInt8.ofNat byteValue.val]) (writes entry callerPrefix) memory := by
  exact callback_store_byte_revert owner (writes entry callerPrefix) memory key stored offset byteValue

/-- info: 'Solidity.Backend.Transient.PayloadV2.callback_store_byte_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms callback_store_byte_revert
/-- info: 'Solidity.Backend.Transient.PayloadV2.callback_preserves_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms callback_preserves_prefix

/-- info: 'Solidity.Backend.Transient.PayloadV2.run_append' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms run_append
/-- info: 'Solidity.Backend.Transient.PayloadV2.finish_writes_revert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finish_writes_revert
/-- info: 'Solidity.Backend.Transient.PayloadV2.store_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_code
/-- info: 'Solidity.Backend.Transient.PayloadV2.byte_revert_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byte_revert_run

/-- info: 'Solidity.Backend.Transient.PayloadV2.revert_actual' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms revert_actual
/-- info: 'Solidity.Backend.Transient.PayloadV2.store_byte_actual' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms store_byte_actual
/-- info: 'Solidity.Backend.Transient.PayloadV2.push_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms push_actual
/-- info: 'Solidity.Backend.Transient.PayloadV2.static_store' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms static_store
end Solidity.Backend.Transient.PayloadV2
