import Solidity.Backend.Transient.State
import Solidity.Backend.Assembler

/-! TLOAD/TSTORE instruction slices (not yet related to the Bridge EVM). Stack head is top; static
writes, underflow, symbolic (non-numeric) slots and unsupported opcodes retain
separate failures. REVERT is supported only at zero length; nonempty return
windows are refused, not erased. No gas/1024-stack/call-depth correspondence is asserted. -/
namespace Solidity.Backend.Transient

inductive Fault where
  | underflow | symbolic | staticWrite | reverted | unsupported
  deriving DecidableEq, Repr
inductive Result where
  | ok (state : State)
  | error (fault : Fault) (state : State)

def step (owner : Roadmap.Address) (static : Bool) (i : Backend.Instr) (s : State) : Result :=
  match i with
  | .push _ imm => .ok {s with machine := s.machine.push (.val (Evm.wmod (ofBytesBE imm.toList)))}
  | .op .TLOAD =>
    match s.machine.stack with
    | [] => .error .underflow s
    | .slot _::_ => .error .symbolic s
    | .val key::tail => .ok {s with machine := {s.machine with stack := .val (s.bank owner key)::tail}}
  | .op .TSTORE =>
    match s.machine.stack with
    | .val key::.val value::tail =>
      if static then .error .staticWrite s
      else .ok {write s owner key value with machine := {s.machine with stack := tail}}
    | [] | [_] => .error .underflow s
    | _ => .error .symbolic s
  | .op .REVERT =>
    match s.machine.stack with
    | .val _::.val size::tail =>
      if size.val=0 then .error .reverted {s with machine := {s.machine with stack := tail}}
      else .error .unsupported s
    | [] | [_] => .error .underflow s
    | _ => .error .symbolic s
  | _ => .error .unsupported s

def run (owner : Roadmap.Address) (static : Bool) : List Backend.Instr → State → Result
  | [],s => .ok s
  | i::code,s => match step owner static i s with
    | .ok next => run owner static code next
    | .error why dirty => .error why dirty

theorem tload (a : Roadmap.Address) (st : Bool) (s : State) (k : Word) (tail : List Evm.Word)
    (stack : s.machine.stack=.val k::tail) :
    step a st (.op .TLOAD) s=
      .ok {s with machine := {s.machine with stack := .val (s.bank a k)::tail}} := by
  simp only [step,stack]

theorem tstore (a : Roadmap.Address) (s : State) (k v : Word) (tail : List Evm.Word)
    (stack : s.machine.stack=.val k::.val v::tail) :
    step a false (.op .TSTORE) s=
      .ok {write s a k v with machine := {s.machine with stack := tail}} := by
  simp only [step,stack,Bool.false_eq_true,↓reduceIte]

theorem static_refusal (a : Roadmap.Address) (s : State) (k v : Word) (tail : List Evm.Word)
    (stack : s.machine.stack=.val k::.val v::tail) :
    step a true (.op .TSTORE) s=.error .staticWrite s := by
  simp only [step,stack,↓reduceIte]

/-- The existing machine executes the ordinary fragment. No ordinary opcode is
redefined, and its full result (including skip, fault and revert) is retained. -/
def ordinary (code : List Evm.Instr) (s : State) : Evm.Out := Evm.exec code 0 s.machine

theorem ordinary_exact (code : List Evm.Instr) (s : State) :
    ordinary code s=Evm.exec code 0 s.machine := rfl

/-- Only a genuine successful zero-skip ordinary execution may be installed.
The transient bank and its journal are unchanged even if persistent/memory
machine fields changed. This is not Source/world adequacy. -/
def resumeOrdinary (s : State) (out : Evm.Out) : Option State :=
  match out with
  | .ok machine 0 => some {s with machine := machine}
  | _ => none

theorem ordinary_frame (s : State) (m : Evm.Machine) :
    resumeOrdinary s (.ok m 0)=some ⟨m,s.bank,s.journal⟩ := rfl
end Solidity.Backend.Transient
