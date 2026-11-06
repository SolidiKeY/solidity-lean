import Solidity.Yul.Compilation.SignedComparisonMachine
import Solidity.Backend.Scalar.Heights
/-! Signed full-word boundary/control witnesses, not native/G24 closure. -/
namespace Solidity.Yul.Compilation.SignedComparisonMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
def maximum : Scalar.Word := BitVec.ofNat 256 (2^255-1)
def negativeOne : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def dirtyNegative : Scalar.Word := BitVec.ofNat 256 (2^255+257)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false

#check sltCompiled.source #v[dirtyNegative,257]
#check slt_run dirtyNegative 257 Evm.Machine.init caller
#guard (PureExpressions.compile 0 sltExpr).isNone
#guard sltCompiled.lowered.code 15 = none
#guard Scalar.run sltProgram [dirty] = none
#guard stackBound sltProgram 1022
#guard !(stackBound sltProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.slt] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.slt] {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#check sgtCompiled.source #v[dirtyNegative,257]
#check sgt_run dirtyNegative 257 Evm.Machine.init caller
#guard (PureExpressions.compile 0 sgtExpr).isNone
#guard sgtCompiled.lowered.code 15 = none
#guard Scalar.run sgtProgram [dirty] = none
#guard stackBound sgtProgram 1022
#guard !(stackBound sgtProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.sgt] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.sgt] {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#guard Scalar.run sltProgram [negativeOne,0] = some [1,negativeOne,0]
#guard Scalar.run sgtProgram [negativeOne,0] = some [0,negativeOne,0]
#guard Scalar.run sltProgram [minimum,maximum] = some [1,minimum,maximum]
#guard Scalar.run sgtProgram [maximum,minimum] = some [1,maximum,minimum]
#guard Scalar.run sltProgram [minimum,minimum] = some [0,minimum,minimum]
#guard Scalar.run sgtProgram [minimum,minimum] = some [0,minimum,minimum]
#guard Scalar.run sltProgram [dirtyNegative,257] = some [1,dirtyNegative,257]
#guard Scalar.run sgtProgram [dirty,257] = some [1,dirty,257]
#guard Scalar.run sltProgram [257,dirtyNegative] = some [0,257,dirtyNegative]
#guard (SignedMachine.selectCode [.op .SAR]).isNone
#guard (SignedMachine.selectCode [.op .SSTORE]).isNone
-- Uncapped model success does not certify native capacity.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.slt]
      {m with stack := coreWord dirtyNegative::coreWord 257::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord ((Scalar.binary .SLT).getD (fun _ _ => 0) dirtyNegative 257)::coreWord dirtyNegative::coreWord 257::List.replicate 1025 (.slot (.root 17))} 0 :=
  slt_run dirtyNegative 257 m _
end Solidity.Yul.Compilation.SignedComparisonMachine.Controls
