import Solidity.Yul.Compilation.UnaryMachine
import Solidity.Backend.Scalar.Heights
/-! Full-word unary and resource-boundary controls, not native execution. -/
namespace Solidity.Yul.Compilation.UnaryMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def largest : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false

#check iszeroCompiled.source #v[dirty]
#check iszero_run dirty Evm.Machine.init caller
#guard (PureExpressions.compile 0 iszeroExpr).isNone
#guard (iszeroCompiled.lowered.code 15).isSome
#guard (iszeroCompiled.lowered.code 16).isNone
#guard Scalar.run iszeroProgram [] = none
#guard stackBound iszeroProgram 1023
#guard !(stackBound iszeroProgram 1024)
#guard isFault (Evm.run [.dup 1,.iszero] Evm.Machine.init)
#guard isFault (Evm.run [.iszero]
  {Evm.Machine.init with stack := [.slot (.root 17)]})

#check notCompiled.source #v[dirty]
#check not_run dirty Evm.Machine.init caller
#guard (PureExpressions.compile 0 notExpr).isNone
#guard (notCompiled.lowered.code 15).isSome
#guard (notCompiled.lowered.code 16).isNone
#guard Scalar.run notProgram [] = none
#guard stackBound notProgram 1023
#guard !(stackBound notProgram 1024)
#guard isFault (Evm.run [.dup 1,.not] Evm.Machine.init)
#guard isFault (Evm.run [.not]
  {Evm.Machine.init with stack := [.slot (.root 17)]})

#guard Scalar.run iszeroProgram [0] = some [1,0]
#guard Scalar.run iszeroProgram [1] = some [0,1]
#guard Scalar.run iszeroProgram [dirty] = some [0,dirty]
#guard Scalar.run iszeroProgram [highOnly] = some [0,highOnly]
#guard Scalar.run notProgram [0] = some [largest,0]
#guard Scalar.run notProgram [largest] = some [0,largest]
#guard Scalar.run notProgram [dirty] = some [~~~dirty,dirty]
#guard Scalar.run notProgram [highOnly] = some [~~~highOnly,highOnly]
#guard (WordMachine.selectCode [.op .SSTORE]).isNone
example (m : Evm.Machine) :
    Evm.run [.dup 1,.iszero] {m with stack := coreWord highOnly::caller} =
      .ok {m with stack := coreWord ((Scalar.unary .ISZERO).getD (fun _ => 0) highOnly)::coreWord highOnly::caller} 0 :=
  iszero_run highOnly m caller
-- Uncapped model success is independent of native capacity.
example (m : Evm.Machine) :
    Evm.run [.dup 1,.not]
      {m with stack := coreWord dirty::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord ((Scalar.unary .NOT).getD (fun _ => 0) dirty)::coreWord dirty::List.replicate 1025 (.slot (.root 17))} 0 :=
  not_run dirty m _
end Solidity.Yul.Compilation.UnaryMachine.Controls
