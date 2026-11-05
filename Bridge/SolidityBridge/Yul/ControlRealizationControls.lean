import SolidityBridge.Yul.ControlRealization
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.ControlRealization.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
#check branch_model #v[highOnly,17] #v[] [dirty,77] (machine [highOnly,17,dirty,77]) rfl
#check sequence_model #v[dirty,0] #v[] [77] (machine [dirty,0,77]) rfl
#check nested_model #v[highOnly,maximum] #v[] [dirty,77] (machine [highOnly,maximum,dirty,77]) rfl
#check prefixed_model #v[highOnly,17] #v[dirty,99] [77] (machine [dirty,99,highOnly,17,77]) rfl
#guard observe (Evm.run prefixedSelected.ir (machine [dirty,99,highOnly,17,77])) ==
  some ([some dirty.toNat,some 99,some highOnly.toNat,some 18,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run sequenceSelected.ir (machine [dirty,0,77]))).map (fun s => s.1) == some [some 0,some 0,some 77]
#guard (observe (Evm.run sequenceSelected.ir (machine [0,dirty,77]))).map (fun s => s.1) == some [some dirty.toNat,some (dirty+1).toNat,some 77]
#guard (observe (Evm.run nestedSelected.ir (machine [highOnly,maximum,77]))).map (fun s => s.1) == some [some highOnly.toNat,some 0,some 77]
#guard (observe (Evm.run nestedSelected.ir (machine [0,maximum,77]))).map (fun s => s.1) == some [some 0,some maximum.toNat,some 77]
#guard (observe (Evm.run nestedSelected.ir (machine [highOnly,0,77]))).map (fun s => s.1) == some [some highOnly.toNat,some 0,some 77]
#guard match Evm.run nestedSelected.ir (machine []) with | .fault => true | _ => false
#guard match Evm.run nestedSelected.ir (machine [1]) with | .fault => true | _ => false
-- Selected-path success requires no run of an inactive ADD on the empty stack.
def inactiveBlock : Backend.Block := .ite [pushWord 0] (.code [.op .ADD]) (.code [])
def activeBlock : Backend.Block := .ite [pushWord 1] (.code [.op .ADD]) (.code [])
def inactive := (selectBlock inactiveBlock).get (by rfl)
def active := (selectBlock activeBlock).get (by rfl)
#guard (observe (Evm.run inactive.ir (machine []))).isSome
#guard match Evm.run active.ir (machine []) with | .fault => true | _ => false
#guard (selectBlock (.loop [] (.code []))).isNone
-- Numeric selection supports SUB, but no SUB instruction certificate is assumed.
#guard (NumericMachine.selectCode [.op .SUB]).isSome
#guard (selectSlice [.op .SUB]).isNone
#guard (selectSlice [.op .STOP]).isNone
#guard (selectSlice [.push 1 #v[1]]).isNone
#guard (selectSlice [pushWord dirty]).isSome
#guard (selectSlice [.op (.DUP 15),.op (.SWAP 15),.op .POP]).isSome
#guard (LiteralSelection.select (.dup 17)).isNone
#guard (LiteralSelection.select (.swap 17)).isNone
#guard (LiteralSelection.select (.dup 0)).isNone
#guard (LiteralSelection.select (.swap 0)).isNone
#guard Scalar.stackBound [pushWord dirty] 1023
#guard !(Scalar.stackBound [pushWord dirty] 1024)
-- Successful uncapped model execution is not a native expansion/capacity claim.
#guard (observe (Evm.run nestedSelected.ir (machine (highOnly::17::List.replicate 1021 77)))).isSome
def addSlice := (selectSlice [.op .ADD]).get (by rfl)
#check addSlice.lowering
#check addSlice.lowering.success [dirty,1,77] [dirty+1,77] (machine [dirty,1,77]) rfl
#check addSlice.lowering.success [dirty] [] (machine [dirty]) rfl
end SolidityBridge.Yul.ControlRealization.Controls
