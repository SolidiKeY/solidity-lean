import Solidity.Yul.Compilation.QuotientMachine
import Solidity.Backend.Scalar.Heights
/-! Zero/nonzero/order/dirty/caller controls for the existing uncapped model. -/
namespace Solidity.Yul.Compilation.QuotientMachine.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def largest : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def caller : List Evm.Word := [.slot (.root 17),coreWord 88]
def isFault : Evm.Out → Bool | .fault => true | _ => false

#check divCompiled.source #v[dirty,7]
#check div_run dirty 7 Evm.Machine.init caller
#check div_run dirty 0 Evm.Machine.init caller
#guard (PureExpressions.compile 0 divExpr).isNone
#guard divCompiled.lowered.code 15 = none
#guard Scalar.run divProgram [dirty] = none
#guard Scalar.run divProgram [dirty,0] = some [0,dirty,0]
#guard Scalar.run divProgram [0,7] = some [0,0,7]
#guard stackBound divProgram 1022
#guard !(stackBound divProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.div]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.div]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.div] {m with stack := coreWord dirty::coreWord 0::caller} =
      .ok {m with stack := coreWord ((Scalar.binary .DIV).getD (fun _ _ => 0) dirty 0)::coreWord dirty::coreWord 0::caller} 0 :=
  div_run dirty 0 m caller

#check modCompiled.source #v[dirty,7]
#check mod_run dirty 7 Evm.Machine.init caller
#check mod_run dirty 0 Evm.Machine.init caller
#guard (PureExpressions.compile 0 modExpr).isNone
#guard modCompiled.lowered.code 15 = none
#guard Scalar.run modProgram [dirty] = none
#guard Scalar.run modProgram [dirty,0] = some [0,dirty,0]
#guard Scalar.run modProgram [0,7] = some [0,0,7]
#guard stackBound modProgram 1022
#guard !(stackBound modProgram 1023)
#guard isFault (Evm.run [.dup 2,.dup 2,.mod]
  {Evm.Machine.init with stack := [coreWord dirty]})
#guard isFault (Evm.run [.mod]
  {Evm.Machine.init with stack := [.slot (.root 17),coreWord dirty]})
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.mod] {m with stack := coreWord dirty::coreWord 0::caller} =
      .ok {m with stack := coreWord ((Scalar.binary .MOD).getD (fun _ _ => 0) dirty 0)::coreWord dirty::coreWord 0::caller} 0 :=
  mod_run dirty 0 m caller

#guard Scalar.run divProgram [17,3] = some [5,17,3]
#guard Scalar.run divProgram [3,17] = some [0,3,17]
#guard Scalar.run modProgram [17,3] = some [2,17,3]
#guard Scalar.run modProgram [3,17] = some [3,3,17]
#guard Scalar.run divProgram [largest,1] = some [largest,largest,1]
#guard Scalar.run modProgram [largest,1] = some [0,largest,1]
#guard Scalar.run divProgram [dirty,7] =
  some [BitVec.ofNat 256 (dirty.toNat/7),dirty,7]
#guard Scalar.run modProgram [dirty,7] =
  some [BitVec.ofNat 256 (dirty.toNat%7),dirty,7]
#guard (NumericMachine.selectCode [.op .SSTORE]).isNone
-- Model execution success is not native1024-capacity evidence.
example (m : Evm.Machine) :
    Evm.run [.dup 2,.dup 2,.div]
      {m with stack := coreWord largest::coreWord 1::List.replicate 1025 (.slot (.root 17))} =
      .ok {m with stack := coreWord ((Scalar.binary .DIV).getD (fun _ _ => 0) largest 1)::coreWord largest::coreWord 1::List.replicate 1025 (.slot (.root 17))} 0 :=
  div_run largest 1 m _
end Solidity.Yul.Compilation.QuotientMachine.Controls
