import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3
import Solidity.Evm.Machine
import Solidity.Lowering.Readonly.InvocationFrame

/-! Conditional G42 producer interfaces, NOT an implementation of world CALL.
All state types and executions are existing Source/Evm types. No observation,
frame, source-run or fetched-execution field is automatically inhabited. -/
namespace Solidity.Backend.WorldCalls
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Pipeline Outcome)
open Solidity.Lowering.Readonly

structure Identity where
  profile : Pipeline
  declaration : DeclName
  parameters : List STy
  returns : List STy
  receiver : Address
  sender : Address
  value : Word
  input : Bytes
  static : Bool
  depth : Nat
  horizon : Nat

def identity (i : InvocationFrame.Invocation E Γ dn ps rs) : Identity :=
  ⟨i.global.pipeline, ⟨i.declaration.scope, i.declaration.name⟩, ps, rs,
    i.captured.receiver, i.frame.this, i.captured.value, i.captured.input,
    i.mode, i.frame.depth + 1, i.horizon⟩

structure Code where
  push : List Evm.Instr
  body : List Evm.Instr
  pop : List Evm.Instr

def Code.full (code : Code) : List Evm.Instr := code.push ++ (code.body ++ code.pop)

/-- Control-only view trace, NOT the frozen P1 physical-frame contract.
Production consumers take InterfaceV3.Pending* parameters separately. -/
structure ReturnedFrame (code : Code) (view : Evm.Machine → List Identity)
    (key : Identity) (initial final : Evm.Machine) where
  pushed : Evm.Machine
  returned : Evm.Machine
  pushRun : Evm.run code.push initial = .ok pushed 0
  bodyRun : Evm.run code.body pushed = .ok returned 0
  popRun : Evm.run code.pop returned = .ok final 0
  pushView : view pushed = key :: view initial
  bodyView : view returned = view pushed
  popView : view final = (view returned).tail

/-- Per-invocation execution/P2/P3 boundary. Actual P1 producers are the frozen
InterfaceV3.Pending* parameters of compiler consumers, not a view equality. The Invocation index retains actual
capture, arguments, declaration/signature and evaluation position. Step and
Observed are chosen by the producer and not tied to the source state here
(`Step := False` inhabits the structure); consumers only project them. No
completeness or native adequacy is inferred from these signatures. -/
structure Premises (i : InvocationFrame.Invocation E Γ dn ps rs) where
  code : Code
  Observed : Identity → Evm.Machine → Evm.Out → Except Halt Outcome → Prop
  Step : Identity → Evm.Machine → Except Halt Outcome → St E → Evm.Out → Prop
  bound : ∀ key initial raw final target, Step key initial raw final target → key = identity i
  execution : ∀ key initial raw final target, Step key initial raw final target →
    Evm.run code.full initial = target
  observed : ∀ key initial raw final target, Step key initial raw final target → Observed key initial target raw
  sourceRaw : ∀ key initial raw final target, Step key initial raw final target → i.RawAt raw final
  p2History : ∀ key initial raw final target, Step key initial raw final target →
    StaticJournal.History i.after.2.ex i.mode final.ex

/-- An actually reached/fetched CALL in the existing EVM interpreter. This
certificate alone says nothing about returndata or recipient execution. -/
structure FetchedCall (code : List Evm.Instr) (initial : Evm.Machine) where
  pc : Nat
  reached : Evm.Machine
  result : Evm.Out
  instruction : code[pc]? = some Evm.Instr.call
  prefixRun : Evm.run (code.take pc) initial = .ok reached 0
  execute : Evm.Instr.step .call reached = result

/-- P10's actual fetched CALL/RETURNDATA relation remains a typed producer
input. `Returndata` is an unconstrained `Prop` here (nothing enforces the
validated upstream relation; no instance exists yet). Its witness is tied to the reached CALL and SAME
Step/identity. No general returndata relation is implemented here. -/
structure FetchedPremises (i : InvocationFrame.Invocation E Γ dn ps rs) (p : Premises i) where
  Returndata : Identity → {initial : Evm.Machine} → FetchedCall p.code.full initial →
    Evm.Out → Except Halt Outcome → Prop
  Fetched : Evm.Machine → Except Halt Outcome → St E → Evm.Out → Prop
  fetch : ∀ initial raw final target, Fetched initial raw final target → FetchedCall p.code.full initial
  returndata : ∀ initial raw final target (h : Fetched initial raw final target),
    Returndata (identity i) (fetch initial raw final target h) target raw
  step : ∀ initial raw final target, Fetched initial raw final target →
    p.Step (identity i) initial raw final target

end Solidity.Backend.WorldCalls
