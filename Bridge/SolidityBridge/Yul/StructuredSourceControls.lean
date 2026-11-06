import SolidityBridge.Yul.StructuredSource
import SolidityBridge.Yul.ArithmeticSelectionControls
namespace SolidityBridge.Yul.StructuredSource.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev maximum := ArithmeticSelection.Controls.maximum
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def result {fuel : Nat} {stmt : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2}
    (producer : NormalControl.Derivation fuel stmt) (a b : Scalar.Word) :=
  (Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt producer.profile
    (ProducerExpressions.sourceLocals #v[a,b])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal))
#check branch_execution #v[0,17] #v[] [dirty,77]
#check branch_execution #v[highOnly,17] #v[] [dirty,77]
#check sequence_execution #v[dirty,0] #v[] [77]
#check nested_execution #v[highOnly,17] #v[] [77]
#check prefixed_execution #v[highOnly,17] #v[dirty,99] [77]
#check compiled.source #v[highOnly,17]
#check sequenceCompiled.source #v[dirty,0]
#guard result compiled 0 17 == some (0,17,true)
#guard result compiled highOnly 17 == some (highOnly.toNat,18,true)
#guard result compiled dirty maximum == some (dirty.toNat,0,true)
-- The test reads the updated local; a stale old condition would take the arm.
#guard result sequenceCompiled dirty 0 == some (0,0,true)
#guard result sequenceCompiled 0 dirty == some (dirty.toNat,dirty.toNat+1,true)
#guard result nestedCompiled 0 17 == some (0,17,true)
#guard result nestedCompiled highOnly 0 == some (highOnly.toNat,0,true)
#guard result nestedCompiled highOnly 17 == some (highOnly.toNat,18,true)
#guard (NormalControl.compile 3 statement).isNone
#guard (NormalControl.compile 4 sequenceStatement).isNone
#guard (compiled.emit 16).isNone
#guard (compiled.emit 0).isSome
#guard (MachineControl.blockCode block).isSome
-- Finite model regressions only: structured is NOT a generic model/native run theorem.
def target := (MachineControl.blockCode block).get (by rfl)
def sequenceTarget := (MachineControl.blockCode sequenceBlock).get (by rfl)
def prefixedTarget := (MachineControl.blockCode prefixedBlock).get (by rfl)
#guard observe (Evm.run target (machine [highOnly,17,77])) ==
  some ([some highOnly.toNat,some 18,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run target (machine [0,17,77]))).map (fun s => s.1) == some [some 0,some 17,some 77]
#guard (observe (Evm.run sequenceTarget (machine [dirty,0,77]))).map (fun s => s.1) == some [some 0,some 0,some 77]
#guard (observe (Evm.run prefixedTarget (machine [dirty,99,highOnly,17,77]))).map (fun s => s.1) ==
  some [some dirty.toNat,some 99,some highOnly.toNat,some 18,some 77]
#guard match Evm.run target (machine []) with | .fault => true | _ => false
#guard (observe (Evm.run target (machine (highOnly::17::List.replicate 1021 77)))).isSome
#print axioms structured
#print axioms branch_execution
#print axioms sequence_execution
#print axioms nested_execution
end SolidityBridge.Yul.StructuredSource.Controls
