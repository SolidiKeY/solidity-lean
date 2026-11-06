import Solidity.Yul.Compilation.ComparisonMachine
import Solidity.Backend.Scalar.Heights
/-! Unsigned/full-word/order and resource separation controls. -/
namespace Solidity.Yul.Compilation.ComparisonMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def largest : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false

#check ltCompiled.source #v[dirty,7]
#check lt_run dirty 7 Evm.Machine.init caller
#guard (PureExpressions.compile 0 ltExpr).isNone
#guard ltCompiled.lowered.code 15 = none
#guard Scalar.run ltProgram [dirty] = none
#guard stackBound ltProgram 1022
#guard !(stackBound ltProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.lt] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.lt] {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#check gtCompiled.source #v[dirty,7]
#check gt_run dirty 7 Evm.Machine.init caller
#guard (PureExpressions.compile 0 gtExpr).isNone
#guard gtCompiled.lowered.code 15 = none
#guard Scalar.run gtProgram [dirty] = none
#guard stackBound gtProgram 1022
#guard !(stackBound gtProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.gt] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.gt] {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#check eqCompiled.source #v[dirty,7]
#check eq_run dirty 7 Evm.Machine.init caller
#guard (PureExpressions.compile 0 eqExpr).isNone
#guard eqCompiled.lowered.code 15 = none
#guard Scalar.run eqProgram [dirty] = none
#guard stackBound eqProgram 1022
#guard !(stackBound eqProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.eq] {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.eq] {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})

#guard Scalar.run ltProgram [1,3] = some [1,1,3]
#guard Scalar.run ltProgram [3,1] = some [0,3,1]
#guard Scalar.run gtProgram [1,3] = some [0,1,3]
#guard Scalar.run gtProgram [3,1] = some [1,3,1]
#guard Scalar.run ltProgram [largest,0] = some [0,largest,0]
#guard Scalar.run gtProgram [largest,0] = some [1,largest,0]
#guard Scalar.run ltProgram [highOnly,1] = some [0,highOnly,1]
#guard Scalar.run gtProgram [highOnly,1] = some [1,highOnly,1]
#guard Scalar.run eqProgram [highOnly,0] = some [0,highOnly,0]
#guard Scalar.run eqProgram [dirty,257] = some [0,dirty,257]
#guard Scalar.run eqProgram [dirty,dirty] = some [1,dirty,dirty]
#guard (WordMachine.selectCode [.op .SSTORE]).isNone
-- Uncapped model success is not native capacity evidence.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.eq]
      {m with stack := coreWord dirty::coreWord dirty::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord ((Scalar.binary .EQ).getD (fun _ _ => 0) dirty dirty)::coreWord dirty::coreWord dirty::List.replicate 1025 (.slot (.root 17))} 0 :=
  eq_run dirty dirty m _
end Solidity.Yul.Compilation.ComparisonMachine.Controls
