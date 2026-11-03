import SolidityBridge.Yul.SelectionSequence
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.SelectionSequence.Controls
open Solidity Backend Scalar Selection
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
def program := emit [.add,.mul] addMulCertificates
#guard program = [.op .ADD,.op .MUL]
#check execute [.add,.mul] addMulCertificates [dirty,255,2,77] (machine [dirty,255,2,77]) rfl
#check execute [.add,.mul] addMulCertificates [dirty,255] (machine [dirty,255]) rfl
#check execute [.add,.mul] addMulCertificates [dirty] (machine [dirty]) rfl
#guard Scalar.run program [dirty,255,2,77] = some [(dirty+255)*2,77]
#guard observe (Evm.run [.add,.mul] (machine [dirty,255,2,77])) ==
  some ([some (2^201+1024),some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.run program [maximum,1,2,77] = some [0,77]
#guard (observe (Evm.run [.add,.mul] (machine [maximum,1,2,77]))).map (fun s => s.1) ==
  some [some 0,some 77]
-- Failure in the second instruction, after an actual successful ADD.
#guard Scalar.run ArithmeticSelection.add.code [dirty,255] = some [dirty+255]
#guard Scalar.run program [dirty,255] = none
#guard match Evm.run [.add,.mul] (machine [dirty,255]) with | .fault => true | _ => false
-- Failure in the first instruction.
#guard Scalar.run program [dirty] = none
#guard match Evm.run [.add,.mul] (machine [dirty]) with | .fault => true | _ => false
#guard Scalar.run program [] = none
#guard match Evm.run [.add,.mul] (machine []) with | .fault => true | _ => false
#guard Scalar.stackBound program 1024
#guard !(Scalar.stackBound program 1025)
#guard (Scalar.run program (dirty::255::2::List.replicate 1022 77)).isSome
#guard (observe (Evm.run [.add,.mul] (machine (dirty::255::2::List.replicate 1022 77)))).isSome
-- Arbitrary numeric caller tail is preserved by the concrete two-op update.
#guard Scalar.run program [35,64,17,dirty,77] = some [1683,dirty,77]
#print axioms execute
#print axioms addMulCertificates
end SolidityBridge.Yul.SelectionSequence.Controls
