import Solidity.Yul.Builtins
import Solidity.Yul.World.Adapters

/-! Arity-indexed LOG leaf over already evaluated operands. This uses the
producer AST, existing world observations and memory port unchanged. `none`
for other constructors means this leaf does not handle them; it is not an
admission refusal or an EVM exception certificate. Argument evaluation, gas,
Source/G01 correspondence and the full Yul runner remain separate obligations. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word)
variable {D : Layout} {L T : Address → Solidity.Source.SPath → STy} {Memory : Type}

def logBuiltin {a : Nat} (builtin : Solidity.Yul.Builtin a 0)
    (port : BytePort Memory) (entry : ObservedEffects D L T) (memory : Memory)
    (frame : CallFrame) (args : Fin a → Word) : Option (ObservedEffects D L T) :=
  match builtin with
  | .log0 => logAdapter port entry memory frame.static frame.this ⟨0,by decide⟩ #v[] (args 0) (args 1)
  | .log1 => logAdapter port entry memory frame.static frame.this ⟨1,by decide⟩ #v[args 2] (args 0) (args 1)
  | .log2 => logAdapter port entry memory frame.static frame.this ⟨2,by decide⟩ #v[args 2,args 3] (args 0) (args 1)
  | .log3 => logAdapter port entry memory frame.static frame.this ⟨3,by decide⟩ #v[args 2,args 3,args 4] (args 0) (args 1)
  | .log4 => logAdapter port entry memory frame.static frame.this ⟨4,by decide⟩ #v[args 2,args 3,args 4,args 5] (args 0) (args 1)
  | _ => none

open Solidity.Roadmap (Bytes)
theorem log0_binding (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (frame : CallFrame) (args : Fin 2 → Word) (bytes : Bytes)
    (hs : frame.static = false) (h : port.load memory (args 0) (args 1) = some bytes) :
    logBuiltin .log0 port entry memory frame args =
      some (emitObserved entry ⟨frame.this,⟨0,by decide⟩,#v[],bytes⟩) := by
  simp only [logBuiltin,logAdapter,hs,Bool.false_eq_true,↓reduceIte,h,bind,Option.bind_some,pure]

theorem log1_binding (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (frame : CallFrame) (args : Fin 3 → Word) (bytes : Bytes)
    (hs : frame.static = false) (h : port.load memory (args 0) (args 1) = some bytes) :
    logBuiltin .log1 port entry memory frame args =
      some (emitObserved entry ⟨frame.this,⟨1,by decide⟩,#v[args 2],bytes⟩) := by
  simp only [logBuiltin,logAdapter,hs,Bool.false_eq_true,↓reduceIte,h,bind,Option.bind_some,pure]

theorem log2_binding (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (frame : CallFrame) (args : Fin 4 → Word) (bytes : Bytes)
    (hs : frame.static = false) (h : port.load memory (args 0) (args 1) = some bytes) :
    logBuiltin .log2 port entry memory frame args =
      some (emitObserved entry ⟨frame.this,⟨2,by decide⟩,#v[args 2,args 3],bytes⟩) := by
  simp only [logBuiltin,logAdapter,hs,Bool.false_eq_true,↓reduceIte,h,bind,Option.bind_some,pure]

theorem log3_binding (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (frame : CallFrame) (args : Fin 5 → Word) (bytes : Bytes)
    (hs : frame.static = false) (h : port.load memory (args 0) (args 1) = some bytes) :
    logBuiltin .log3 port entry memory frame args =
      some (emitObserved entry ⟨frame.this,⟨3,by decide⟩,#v[args 2,args 3,args 4],bytes⟩) := by
  simp only [logBuiltin,logAdapter,hs,Bool.false_eq_true,↓reduceIte,h,bind,Option.bind_some,pure]

theorem log4_binding (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (frame : CallFrame) (args : Fin 6 → Word) (bytes : Bytes)
    (hs : frame.static = false) (h : port.load memory (args 0) (args 1) = some bytes) :
    logBuiltin .log4 port entry memory frame args =
      some (emitObserved entry ⟨frame.this,⟨4,by decide⟩,#v[args 2,args 3,args 4,args 5],bytes⟩) := by
  simp only [logBuiltin,logAdapter,hs,Bool.false_eq_true,↓reduceIte,h,bind,Option.bind_some,pure]

theorem logBuiltin_static {a : Nat} (builtin : Solidity.Yul.Builtin a 0)
    (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (frame : CallFrame) (args : Fin a → Word) :
    logBuiltin builtin port entry memory {frame with static:=true} args = none := by
  cases builtin <;> rfl

end Solidity.Yul.World
