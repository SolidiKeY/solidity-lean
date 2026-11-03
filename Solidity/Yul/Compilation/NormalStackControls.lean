import Solidity.Yul.Compilation.NormalStackTransport
import Solidity.Yul.Compilation.NormalControlControls
/-! Concrete witnesses for the stack-only whole-block consumer; original
WordControl controls remain imported unchanged. These are model/kernel controls,
not native charged/resource or Source/G24 validation. -/
namespace Solidity.Yul.Compilation.NormalStackTransport.Controls
open Backend Scalar Solidity.Yul.Closed MachineAdapter
open NormalControl.Controls (compiled program dirty highOnly root)

def block : Backend.Block := (compiled.emit 2).get (by rfl)
def code : List Evm.Instr := (blockCode block).get (by rfl)
#check fun (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) =>
  machine compiled 2 block code rfl rfl locals #v[91,92] m caller

def result (a b : Scalar.Word) (caller : List Evm.Word) : Option (List Evm.Word × Nat) :=
  match Evm.run code {Evm.Machine.init with stack := [91,92,a,b].map coreWord ++ caller} with
  | .ok out skip => some (out.stack,skip)
  | _ => none
#guard result 0 1 [.slot (.root 77)] = some ([91,92,0,1].map coreWord ++ [.slot (.root 77)],0)
#guard result 3 0 [.slot (.root 77)] = some ([91,92,3,dirty].map coreWord ++ [.slot (.root 77)],0)
#guard result 3 1 [.slot (.root 77)] = some ([91,92,0,1].map coreWord ++ [.slot (.root 77)],0)
#guard result highOnly 0 [.slot (.root 77)] = some ([91,92,highOnly,dirty].map coreWord ++ [.slot (.root 77)],0)
#guard result dirty 0 [.slot (.root 77)] = some ([91,92,dirty,dirty].map coreWord ++ [.slot (.root 77)],0)
#guard (result 0 1 (List.replicate 1021 (coreWord 0))).map (fun out => out.1.length) = some 1025
#guard match Evm.run code Evm.Machine.init with | .fault => true | _ => false
#guard ((compiled.emit 15).bind blockCode).isNone
#guard (blockCode (.loop [] (.code []))).isNone
-- The general word compiler accepts this arithmetic condition, but this
-- deliberately stack-only target consumer does not widen its selected opcodes.
def arithmetic := (NormalControl.compile 3 (.if_
  (.builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .literal (word 1))))
  (.skip : Stmt [] [] root 2))).get (by rfl)
#guard ((arithmetic.emit 2).bind WordControl.blockCode).isSome
#guard ((arithmetic.emit 2).bind blockCode).isNone
#print axioms machine
end Solidity.Yul.Compilation.NormalStackTransport.Controls
