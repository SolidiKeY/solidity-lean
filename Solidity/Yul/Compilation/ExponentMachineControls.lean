import Solidity.Yul.Compilation.ExponentMachine
import Solidity.Backend.Scalar.Heights
/-! Exponent order/zero/wrap/dirty and resource separation controls. Finite
examples deliberately use bounded arithmetic work; the theorem quantifies all words. -/
namespace Solidity.Yul.Compilation.ExponentMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def largest : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false
#check compiled.source #v[dirty,1]
#check model_run dirty 1 Evm.Machine.init caller
#guard Scalar.run program [0,0] = some [1,0,0]
#guard Scalar.run program [0,7] = some [0,0,7]
#guard Scalar.run program [dirty,0] = some [1,dirty,0]
#guard Scalar.run program [dirty,1] = some [dirty,dirty,1]
#guard Scalar.run program [largest,1] = some [largest,largest,1]
#guard Scalar.run program [2,8] = some [256,2,8]
#guard Scalar.run program [8,2] = some [64,8,2]
#guard Scalar.run program [2,256] = some [0,2,256]
#guard Scalar.run program [dirty] = none
#guard (PureExpressions.compile 0 expr).isNone
#guard compiled.lowered.code 15 = none
#guard stackBound program 1022
#guard !(stackBound program 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.exp] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.exp] {Evm.Machine.init with stack := [.slot (.root 17),coreWord 1]})
#guard (WordMachine.selectCode [.op .SSTORE]).isNone
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.exp] {m with stack := coreWord dirty::coreWord 1::caller} =
      .ok {m with stack := coreWord ((Scalar.binary .EXP).getD (fun _ _ => 0) dirty 1)::coreWord dirty::coreWord 1::caller} 0 :=
  model_run dirty 1 m caller
-- Uncapped model execution is not actual native1024-capacity evidence.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.exp]
      {m with stack := coreWord dirty::coreWord 1::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord ((Scalar.binary .EXP).getD (fun _ _ => 0) dirty 1)::coreWord dirty::coreWord 1::List.replicate 1025 (.slot (.root 17))} 0 :=
  model_run dirty 1 m _
end Solidity.Yul.Compilation.ExponentMachine.Controls
