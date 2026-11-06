import SolidityBridge.Yul.SwitchControl
import SolidityBridge.Yul.SwitchCompilationControls
/-! Actual source/model controls for ordered switch composition. No native
or admission claim; capacity remains distinct from mathematical execution. -/
namespace SolidityBridge.Yul.SwitchControl.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
abbrev root := SwitchCompilation.Controls.root
abbrev dirty := SwitchCompilation.Controls.dirty
abbrev machine := SwitchCompilation.Controls.machine
abbrev observe := SwitchCompilation.Controls.observe
abbrev one := SwitchCompilation.Controls.statement

-- The second switch must read the selector/accumulator changed by the first.
def statement : Stmt [] [] root 3 := .seq one (.if_ (.local 2) one)
def compiled := (compile 9 statement).get (by rfl)
def block := compiled.emit.get (by rfl)
def selected := (LoopSelection.selectBlock block).get (by decide)
#check compiled.source #v[1,11,23]
#check compiled.structured block rfl #v[1,11,23] [dirty,77]
#guard (compiled.update #v[1,11,23]).toList == [3,147,23]
#guard (compiled.update #v[1,11,0]).toList == [3,21,0]
#guard (compiled.update #v[1,11,dirty]).toList == [3,147,dirty]
#guard (compiled.update #v[dirty,11,23]).toList == [dirty,42,23]
#guard (compiled.update #v[8,11,23]).toList == [8,99,23]
#guard (evalStmt 9 .nil True.intro statement compiled.profile
  (ProducerExpressions.sourceLocals #v[1,11,23])).map
  (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal)) == some (3,147,23,true)
#guard observe (Evm.run selected.realization.ir (machine [1,11,23,dirty,77])) ==
  some ([some 3,some 147,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [1,11,0,dirty,77])) ==
  some ([some 3,some 21,some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [dirty,11,23,dirty,77])) ==
  some ([some dirty.toNat,some 42,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
-- Nested conditional + sequence actually traverses both new visitor constructors.
def nested : Stmt [] [] root 3 := .if_ (.local 2) (.seq one one)
def nestedCompiled := (compile 9 nested).get (by rfl)
#guard (nestedCompiled.update #v[1,11,23]).toList == [3,147,23]
#guard (nestedCompiled.update #v[1,11,0]).toList == [1,11,0]
-- The lexical-scope/case-body boundary is an actual refusal, not coverage.
def nestedCase : Stmt [] [] root 3 := .switch (.local 0) (.cons (word 1) one .nil) .skip
#guard (compile 16 nestedCase).isNone
#guard (compile 16 (.zero 0 one : Stmt [] [] root 3)).isNone
#guard (compile 0 statement).isNone
#guard (compile 2 statement).isNone
#guard match Evm.run selected.realization.ir (machine []) with | .fault => true | _ => false
-- Host/model success alone is not an EVM1024 capacity claim.
#guard (observe (Evm.run selected.realization.ir
  (machine (1::11::23::List.replicate 1024 dirty)))).isSome
-- Real DUP/SWAP refusal boundaries are still enforced by leaf emission.
def inaccessible : Stmt [] [] root 17 := .seq
  (.switch (.local 0) (.cons (word 1) SwitchCompilation.Controls.inaccessible .nil) .skip) .skip
def inaccessibleCompiled := (compile 6 inaccessible).get (by rfl)
#guard inaccessibleCompiled.emit.isNone
end SolidityBridge.Yul.SwitchControl.Controls
