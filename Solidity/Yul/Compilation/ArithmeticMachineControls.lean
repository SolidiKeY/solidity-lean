import Solidity.Yul.Compilation.ArithmeticMachine
import Solidity.Backend.Scalar.Heights
/-! Actual source compiler/model controls, not charged EVM or G24 closure. -/
namespace Solidity.Yul.Compilation.ArithmeticMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
#check addCompiled.source #v[dirty,7]
#check mulCompiled.source #v[dirty,7]
#check add_run dirty 7 Evm.Machine.init caller
#check mul_run dirty 7 Evm.Machine.init caller
#guard (ProducerExpressions.compile 0 addExpr).isNone
#guard addCompiled.lowered.code 15 = none
#guard (NumericMachine.selectCode [.op .SSTORE]).isNone
#guard Scalar.run addProgram [dirty,7,88] = some ((dirty+7) :: [dirty,7,88])
#guard Scalar.run mulProgram [dirty,7,88] = some ((dirty*7) :: [dirty,7,88])
#guard Scalar.run addProgram [dirty] = none
#guard Scalar.run mulProgram [] = none
#guard Scalar.run addProgram [BitVec.ofNat 256 (2^256-1),1] =
  some [0,BitVec.ofNat 256 (2^256-1),1]
#guard Scalar.run mulProgram [BitVec.ofNat 256 (2^255),2] =
  some [0,BitVec.ofNat 256 (2^255),2]
#guard stackBound addProgram 1022
#guard !(stackBound addProgram 1023)
#guard stackBound mulProgram 1022
#guard !(stackBound mulProgram 1023)
def isFault : Evm.Out → Bool
  | .fault => true
  | _ => false
#guard isFault (Evm.run [.dup 2,.dup 2,.add] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.mul] {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.add] {m with stack := coreWord dirty::coreWord 7::caller} =
      .ok {m with stack := coreWord (dirty+7)::coreWord dirty::coreWord 7::caller} 0 :=
  add_run dirty 7 m caller
-- Model success does not imply the actual 1024-word native capacity.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.mul]
      {m with stack := coreWord dirty::coreWord 7::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord (dirty*7)::coreWord dirty::coreWord 7::
        List.replicate 1025 (.slot (.root 17))} 0 :=
  mul_run dirty 7 m _
#print axioms add_run
#print axioms mul_run
end Solidity.Yul.Compilation.ArithmeticMachine.Controls
