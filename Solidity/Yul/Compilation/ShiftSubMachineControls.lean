import Solidity.Yul.Compilation.ShiftSubMachine
import Solidity.Backend.Scalar.Heights
/-! Dirty/count/operand/resource separation controls for the numeric model. -/
namespace Solidity.Yul.Compilation.ShiftSubMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false

#check subCompiled.source #v[dirty,7]
#check sub_run dirty 7 Evm.Machine.init caller
#guard (PureExpressions.compile 0 subExpr).isNone
#guard subCompiled.lowered.code 15 = none
#guard Scalar.run subProgram [dirty] = none
#guard stackBound subProgram 1022
#guard !(stackBound subProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.sub]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.sub]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#check shlCompiled.source #v[dirty,7]
#check shl_run dirty 7 Evm.Machine.init caller
#guard (PureExpressions.compile 0 shlExpr).isNone
#guard shlCompiled.lowered.code 15 = none
#guard Scalar.run shlProgram [dirty] = none
#guard stackBound shlProgram 1022
#guard !(stackBound shlProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.shl]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.shl]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#check shrCompiled.source #v[dirty,7]
#check shr_run dirty 7 Evm.Machine.init caller
#guard (PureExpressions.compile 0 shrExpr).isNone
#guard shrCompiled.lowered.code 15 = none
#guard Scalar.run shrProgram [dirty] = none
#guard stackBound shrProgram 1022
#guard !(stackBound shrProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.shr]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.shr]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#guard Scalar.run subProgram [3,7] = some [BitVec.ofNat 256 (2^256-4),3,7]
#guard Scalar.run subProgram [7,3] = some [4,7,3]
#guard Scalar.run subProgram [dirty,7] = some [dirty-7,dirty,7]
#guard Scalar.run shlProgram [0,dirty] = some [dirty,0,dirty]
#guard Scalar.run shrProgram [0,dirty] = some [dirty,0,dirty]
#guard Scalar.run shlProgram [255,1] = some [BitVec.ofNat 256 (2^255),255,1]
#guard Scalar.run shrProgram [255,BitVec.ofNat 256 (2^255)] =
  some [1,255,BitVec.ofNat 256 (2^255)]
#guard Scalar.run shlProgram [256,dirty] = some [0,256,dirty]
#guard Scalar.run shrProgram [256,dirty] = some [0,256,dirty]
#guard Scalar.run shlProgram [dirty,7] = some [0,dirty,7]
#guard Scalar.run shrProgram [dirty,7] = some [0,dirty,7]
#guard Scalar.run shlProgram [1,dirty] = some [dirty <<< 1,1,dirty]
#guard Scalar.run shrProgram [1,dirty] = some [dirty >>> 1,1,dirty]
-- Count on top, data underneath; reversing operands gives another result.
#guard Scalar.run shlProgram [1,3] = some [6,1,3]
#guard Scalar.run shlProgram [3,1] = some [8,3,1]
#guard (NumericMachine.selectCode [.op .SSTORE]).isNone
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.sub] {m with stack := coreWord dirty::coreWord 7::caller} =
      .ok {m with stack := coreWord (dirty-7)::coreWord dirty::coreWord 7::caller} 0 :=
  sub_run dirty 7 m caller
-- Model success does not enforce the actual native1024 capacity.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.shr]
      {m with stack := coreWord 1::coreWord dirty::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord ((Scalar.binary .SHR).getD (fun _ _ => 0) 1 dirty)::coreWord 1::coreWord dirty::List.replicate 1025 (.slot (.root 17))} 0 :=
  shr_run 1 dirty m _
end Solidity.Yul.Compilation.ShiftSubMachine.Controls
