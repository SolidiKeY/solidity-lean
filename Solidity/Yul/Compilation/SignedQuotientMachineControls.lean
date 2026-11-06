import Solidity.Yul.Compilation.SignedQuotientMachine
import Solidity.Backend.Scalar.Heights
/-! Signed quotient zero, overflow, sign, dirty and framing controls. -/
namespace Solidity.Yul.Compilation.SignedQuotientMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
def negativeOne : Scalar.Word := BitVec.ofInt 256 (-1)
def negativeTwo : Scalar.Word := BitVec.ofInt 256 (-2)
def negativeThree : Scalar.Word := BitVec.ofInt 256 (-3)
def negativeSeven : Scalar.Word := BitVec.ofInt 256 (-7)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def dirtyNegative : Scalar.Word := BitVec.ofNat 256 (2^255+257)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false

#check sdivCompiled.source #v[minimum,negativeOne]
#check sdiv_run minimum negativeOne Evm.Machine.init caller
#guard (PureExpressions.compile 0 sdivExpr).isNone
#guard sdivCompiled.lowered.code 15 = none
#guard Scalar.run sdivProgram [dirty] = none
#guard Scalar.run sdivProgram [dirtyNegative,0] = some [0,dirtyNegative,0]
#guard stackBound sdivProgram 1022
#guard !(stackBound sdivProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.sdiv] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.sdiv] {Evm.Machine.init with stack := [.slot (.root 17),coreWord 1]})

#check smodCompiled.source #v[minimum,negativeOne]
#check smod_run minimum negativeOne Evm.Machine.init caller
#guard (PureExpressions.compile 0 smodExpr).isNone
#guard smodCompiled.lowered.code 15 = none
#guard Scalar.run smodProgram [dirty] = none
#guard Scalar.run smodProgram [dirtyNegative,0] = some [0,dirtyNegative,0]
#guard stackBound smodProgram 1022
#guard !(stackBound smodProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.smod] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.smod] {Evm.Machine.init with stack := [.slot (.root 17),coreWord 1]})

#guard Scalar.run sdivProgram [minimum,negativeOne] = some [minimum,minimum,negativeOne]
#guard Scalar.run smodProgram [minimum,negativeOne] = some [0,minimum,negativeOne]
#guard Scalar.run sdivProgram [negativeSeven,3] = some [negativeTwo,negativeSeven,3]
#guard Scalar.run sdivProgram [7,negativeThree] = some [negativeTwo,7,negativeThree]
#guard Scalar.run sdivProgram [negativeSeven,negativeThree] = some [2,negativeSeven,negativeThree]
#guard Scalar.run smodProgram [negativeSeven,3] = some [negativeOne,negativeSeven,3]
#guard Scalar.run smodProgram [7,negativeThree] = some [1,7,negativeThree]
#guard Scalar.run smodProgram [negativeSeven,negativeThree] = some [negativeOne,negativeSeven,negativeThree]
#guard Scalar.run sdivProgram [dirtyNegative,1] = some [dirtyNegative,dirtyNegative,1]
#guard Scalar.run smodProgram [dirtyNegative,1] = some [0,dirtyNegative,1]
#guard (SignedMachine.selectCode [.op .SAR]).isNone
#guard (SignedMachine.selectCode [.op .SSTORE]).isNone
-- Actual model success remains separate from native1024 capacity.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.sdiv]
      {m with stack := coreWord minimum::coreWord negativeOne::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord ((Scalar.binary .SDIV).getD (fun _ _ => 0) minimum negativeOne)::coreWord minimum::coreWord negativeOne::List.replicate 1025 (.slot (.root 17))} 0 :=
  sdiv_run minimum negativeOne m _
end Solidity.Yul.Compilation.SignedQuotientMachine.Controls
