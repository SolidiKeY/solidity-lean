import Solidity.Yul.World.Adapters

/-! # Creation caller/constructor boundary
Concrete journal preparation and raw initialization/return-buffer plumbing.
This is not full CREATE execution: funding/depth/resource admission, late collision failure,
created-account initialization, code deposit and lifecycle metadata remain
producer obligations. Initcode is code bytes, never constructor calldata.
-/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
variable {D : Layout} {L T : Address → SPath → STy}

/-- Existing typed account operation; no alternate account state. -/
def creationNonceOp (creator : Address) : Op D L T :=
  .account creator (fun account => { account with nonce := account.nonce + 1 })

/-- Caller preparation AFTER the producer's upfront admission checks. EIP-2681's
nonce cap is checked here; other CREATE checks are not inferred from success.
Collision is a LATER failure after increment, not an upfront admission check. -/
def prepareCreation (entry : ObservedEffects D L T) (creator : Address) :
    Option (ObservedEffects D L T) :=
  if (entry.effects.execution.world.accounts creator).nonce < 2^64-1 then
    some { entry with effects := { entry.effects with
      execution := entry.effects.execution.apply (creationNonceOp creator), returndata := [] } }
  else none

/-- Exact account/trace preparation under the real nonce bound. -/
theorem prepareCreation_exact (entry : ObservedEffects D L T) (creator : Address)
    (h : (entry.effects.execution.world.accounts creator).nonce < 2^64-1) :
    prepareCreation entry creator = some { entry with effects := { entry.effects with
      execution := entry.effects.execution.apply (creationNonceOp creator), returndata := [] } } := by
  simp only [prepareCreation, h, ↓reduceIte]

theorem prepareCreation_refused (entry : ObservedEffects D L T) (creator : Address)
    (h : ¬ (entry.effects.execution.world.accounts creator).nonce < 2^64-1) :
    prepareCreation entry creator = none := by
  simp only [prepareCreation, h, ↓reduceIte]

theorem creationNonce_account (entry : ExecState D L T) (creator : Address) :
    ((entry.apply (creationNonceOp creator)).world.accounts creator) =
      { entry.world.accounts creator with nonce := (entry.world.accounts creator).nonce + 1 } :=
  World.set_get _ _ _

theorem creationNonce_other (entry : ExecState D L T) (creator other : Address) (h : other ≠ creator) :
    (entry.apply (creationNonceOp creator)).world.accounts other = entry.world.accounts other :=
  World.set_other _ h _

/-- Constructor input context is EMPTY calldata, independently of raw initcode.
The actual allocated address and creation value are explicit producer inputs. -/
def constructorFrame (entry : ExecState D L T) (parent : CallFrame) (allocated : Address)
    (value : Word) : CallFrame := entry.enter allocated parent.this value [] false

theorem constructor_context (entry : ExecState D L T) (parent : CallFrame) (allocated : Address)
    (value : Word) :
    (constructorFrame entry parent allocated value).this = allocated ∧
    (constructorFrame entry parent allocated value).caller = parent.this ∧
    (constructorFrame entry parent allocated value).value = value ∧
    (constructorFrame entry parent allocated value).input = [] := ⟨rfl,rfl,rfl,rfl⟩

/-- Constructor completion uses the existing full ordered/journal completion.
Successful initcode bytes are runtime CODE output, so the caller's returndata is
empty. Failed initialization retains revert bytes. Code installation and actual
outcome reachability are not assumed by this helper. -/
def finishCreation (prepared : ObservedEffects D L T) (frame : CallFrame)
    (answer : FrameAnswer D L T) : ObservedEffects D L T :=
  let completed := finishObserved prepared frame answer
  { completed with effects := { completed.effects with returndata := createReturnData answer.outcome } }

theorem finishCreation_data (prepared : ObservedEffects D L T) (frame : CallFrame)
    (answer : FrameAnswer D L T) :
    (finishCreation prepared frame answer).effects.returndata = createReturnData answer.outcome := rfl

theorem finishCreation_success (prepared : ObservedEffects D L T) (frame : CallFrame)
    (operations : List (Op D L T)) (trace : List Observation) (runtime : Bytes) :
    (finishCreation prepared frame ⟨operations,trace,.success runtime⟩).effects.execution =
      prepared.effects.execution.run operations ∧
    (finishCreation prepared frame ⟨operations,trace,.success runtime⟩).trace = prepared.trace ++ trace ∧
    (finishCreation prepared frame ⟨operations,trace,.success runtime⟩).effects.returndata = [] :=
  ⟨rfl,rfl,rfl⟩

theorem finishCreation_revert (prepared : ObservedEffects D L T) (frame : CallFrame)
    (operations : List (Op D L T)) (trace : List Observation) (data : Bytes) :
    (finishCreation prepared frame ⟨operations,trace,.revert data⟩).effects.execution =
      prepared.effects.execution ∧
    (finishCreation prepared frame ⟨operations,trace,.revert data⟩).trace = rollbackTrace prepared.trace trace ∧
    (finishCreation prepared frame ⟨operations,trace,.revert data⟩).effects.returndata = data := by
  refine ⟨?_,rfl,rfl⟩
  change (finishObserved prepared frame ⟨operations,trace,.revert data⟩).effects.execution = _
  have he := congrArg (fun e : Effects D L T => e.execution)
    (finishObserved_revert prepared frame operations trace data).1
  exact he

/-- Constructor failure restores the post-nonce entry; it must not roll back
caller preparation. This conclusion retains the entire ordered trace. -/
theorem failedCreation_keeps_nonce (entry : ObservedEffects D L T) (creator : Address)
    (h : (entry.effects.execution.world.accounts creator).nonce < 2^64-1)
    (prepared : ObservedEffects D L T) (hp : prepareCreation entry creator = some prepared)
    (frame : CallFrame) (operations : List (Op D L T)) (trace : List Observation) (data : Bytes) :
    (finishCreation prepared frame ⟨operations,trace,.revert data⟩).effects.execution =
      entry.effects.execution.apply (creationNonceOp creator) ∧
    (finishCreation prepared frame ⟨operations,trace,.revert data⟩).trace = rollbackTrace entry.trace trace := by
  rw [prepareCreation_exact entry creator h, Option.some.injEq] at hp
  cases hp
  exact ⟨(finishCreation_revert _ _ _ _ _).1,rfl⟩

/-- An enclosing revert DOES undo caller preparation and a successful child,
including caller operations before/after it, at the actual outer entry mark. -/
theorem creation_outer_rollback (entry : ExecState D L T) (prior child later : List (Op D L T))
    (creator a c : Address) (value : Word) (input : Bytes) (static : Bool) :
    (entry.enter a c value input static).rollback
      ((((entry.run prior).apply (creationNonceOp creator)).run child).run later) = entry := by
  have h := rollback_run entry (prior ++ [creationNonceOp creator] ++ child ++ later) a c value input static
  simpa only [run_append, ExecState.run, List.append_nil] using h

/-- Initialization producer consumes raw CODE separately from the empty
constructor calldata. No function law is assumed; concrete execution adequacy
and account/lifecycle initialization must be proved for a real producer. -/
abbrev InitcodePort (D : Layout) (L T : Address → SPath → STy) :=
  ObservedEffects D L T → Word → CallFrame → Bytes → Option (FrameAnswer D L T)

structure CompletedCreation (D : Layout) (L T : Address → SPath → STy) where
  initialization : Outcome
  observed : ObservedEffects D L T
  returndata_eq : observed.effects.returndata = createReturnData initialization

/-- Execute a constructor after caller preparation/admission, at the allocated
address supplied by the creation producer. This is not the complete CREATE
opcode: early funding/depth/resource checks, address selection, late collision failure,
child allocation, lifecycle and code
deposit are not silently delegated to assumptions. A missing producer result is
an adapter refusal, not an EVM failure verdict. -/
def initcodeAdapter {Memory : Type} (port : BytePort Memory) (invoke : InitcodePort D L T)
    (prepared : ObservedEffects D L T) (memory : Memory) (parent : CallFrame)
    (allocated : Address) (gas value offset size : Word) : Option (CompletedCreation D L T) :=
  if parent.static then none else do
    let initcode ← port.load memory offset size
    let frame := constructorFrame prepared.effects.execution parent allocated value
    let answer ← invoke prepared gas frame initcode
    pure ⟨answer.outcome,finishCreation prepared frame answer,rfl⟩

theorem initcodeAdapter_static {Memory : Type} (port : BytePort Memory) (invoke : InitcodePort D L T)
    (prepared : ObservedEffects D L T) (memory : Memory) (parent : CallFrame)
    (allocated : Address) (gas value offset size : Word) (h : parent.static = true) :
    initcodeAdapter port invoke prepared memory parent allocated gas value offset size = none := by
  simp only [initcodeAdapter,h,↓reduceIte]

theorem initcodeAdapter_exact {Memory : Type} (port : BytePort Memory) (invoke : InitcodePort D L T)
    (prepared : ObservedEffects D L T) (memory : Memory) (parent : CallFrame)
    (allocated : Address) (gas value offset size : Word) (code : Bytes) (answer : FrameAnswer D L T)
    (hs : parent.static = false) (hl : port.load memory offset size = some code)
    (hi : invoke prepared gas (constructorFrame prepared.effects.execution parent allocated value) code = some answer) :
    initcodeAdapter port invoke prepared memory parent allocated gas value offset size =
      some ⟨answer.outcome,finishCreation prepared
        (constructorFrame prepared.effects.execution parent allocated value) answer,rfl⟩ := by
  simp only [initcodeAdapter,hs,Bool.false_eq_true,↓reduceIte,hl,hi,bind,Option.bind_some,pure]

end Solidity.Yul.World
