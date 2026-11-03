import Solidity.Yul.Compilation.BitMachineExecution
import Solidity.Backend.Scalar.Heights
/-! Concrete source/compiler and numeric model controls, not native/G24 gates. -/
namespace Solidity.Yul.Compilation.BitMachineExecution.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def allOnes : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false

#check andCompiled.source #v[dirty,allOnes]
#check and_run dirty allOnes Evm.Machine.init caller
#guard Scalar.run andProgram [dirty,allOnes,88] =
  some [(dirty &&& allOnes),dirty,allOnes,88]
#guard Scalar.run andProgram [dirty] = none
#guard (PureExpressions.compile 0 andExpr).isNone
#guard andCompiled.lowered.code 15 = none
#guard stackBound andProgram 1022
#guard !(stackBound andProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.and]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.and]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.and] {m with stack := coreWord dirty::coreWord allOnes::caller} =
      .ok {m with stack := coreWord (dirty &&& allOnes)::coreWord dirty::coreWord allOnes::caller} 0 :=
  and_run dirty allOnes m caller

#check orCompiled.source #v[dirty,allOnes]
#check or_run dirty allOnes Evm.Machine.init caller
#guard Scalar.run orProgram [dirty,allOnes,88] =
  some [(dirty ||| allOnes),dirty,allOnes,88]
#guard Scalar.run orProgram [dirty] = none
#guard (PureExpressions.compile 0 orExpr).isNone
#guard orCompiled.lowered.code 15 = none
#guard stackBound orProgram 1022
#guard !(stackBound orProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.or]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.or]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.or] {m with stack := coreWord dirty::coreWord allOnes::caller} =
      .ok {m with stack := coreWord (dirty ||| allOnes)::coreWord dirty::coreWord allOnes::caller} 0 :=
  or_run dirty allOnes m caller

#check xorCompiled.source #v[dirty,allOnes]
#check xor_run dirty allOnes Evm.Machine.init caller
#guard Scalar.run xorProgram [dirty,allOnes,88] =
  some [(dirty ^^^ allOnes),dirty,allOnes,88]
#guard Scalar.run xorProgram [dirty] = none
#guard (PureExpressions.compile 0 xorExpr).isNone
#guard xorCompiled.lowered.code 15 = none
#guard stackBound xorProgram 1022
#guard !(stackBound xorProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.xor]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.xor]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.xor] {m with stack := coreWord dirty::coreWord allOnes::caller} =
      .ok {m with stack := coreWord (dirty ^^^ allOnes)::coreWord dirty::coreWord allOnes::caller} 0 :=
  xor_run dirty allOnes m caller

#guard Scalar.run andProgram [dirty,allOnes] = some [dirty,dirty,allOnes]
#guard Scalar.run orProgram [dirty,0] = some [dirty,dirty,0]
#guard Scalar.run xorProgram [dirty,dirty] = some [0,dirty,dirty]
#guard (NumericMachine.selectCode [.op .SSTORE]).isNone
-- Explicitly separate uncapped model success from stackBound/native capacity.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.xor]
      {m with stack := coreWord dirty::coreWord dirty::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord (dirty ^^^ dirty)::coreWord dirty::coreWord dirty::
        List.replicate 1025 (.slot (.root 17))} 0 :=
  xor_run dirty dirty m _
end Solidity.Yul.Compilation.BitMachineExecution.Controls
