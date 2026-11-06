import SolidityBridge.Yul.SwitchCompilation
import SolidityBridge.Yul.ArithmeticSelectionControls
import SolidityBridge.Yul.JsonCompilationControls
/-! Pure switch component controls; no admission/native/G24 coverage claim. -/
namespace SolidityBridge.Yul.SwitchCompilation.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
abbrev root : Control := ⟨false,false⟩
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def setSelector : Stmt [] [] root 3 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal (word 3))
def scopedAdd : Stmt [] [] root 4 :=
  .assign (fun _ : Fin 1 => .local 2)
    (.builtin (.pure .add) (Fin.cases (.local 2) (fun _ => .literal (word 10))))
def firstBody : Stmt [] [] root 3 := .seq setSelector (.zero 1 scopedAdd)
def dirtyBody : Stmt [] [] root 3 :=
  .assign (fun _ : Fin 1 => .local 1) (.literal (word 42))
def lastBody : Stmt [] [] root 3 :=
  .assign (fun _ : Fin 1 => .local 1)
    (.builtin (.pure .mul) (Fin.cases (.local 1) (fun _ => .literal (word 7))))
def cases : Cases [] [] root 3 :=
  .cons (word 1) firstBody (.cons (word dirty.toNat) dirtyBody (.cons (word 3) lastBody .nil))
def fallback : Stmt [] [] root 3 :=
  .let_ 1 (.literal (word 99)) (.assign (fun _ : Fin 1 => .local 2) (.local 0))
def compiled := (compile 6 (.local 0) cases fallback).get (by rfl)
def statement : Stmt [] [] root 3 := .switch (.local 0) cases fallback
def block := compiled.emit.get (by rfl)
def selected := (LoopSelection.selectBlock block).get (by decide)
#check compiled.source #v[1,11,23]
#check compiled.structured block rfl #v[1,11,23] [dirty,77]
#check selected.lowering.success [1,11,23,dirty,77] [3,21,23,dirty,77]
  (machine [1,11,23,dirty,77]) rfl
#guard (compiled.update #v[1,11,23]).toList == [3,21,23]
#guard (compiled.update #v[dirty,11,23]).toList == [dirty,42,23]
#guard (compiled.update #v[3,11,23]).toList == [3,77,23]
#guard (compiled.update #v[8,11,23]).toList == [8,99,23]
#guard (evalStmt 7 .nil True.intro statement compiled.profile
  (ProducerExpressions.sourceLocals #v[1,11,23])).map
  (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal)) == some (3,21,23,true)
-- The first body changes the selector variable to3; case3 must not fall through.
#guard observe (Evm.run selected.realization.ir (machine [1,11,23,dirty,77])) ==
  some ([some 3,some 21,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [dirty,11,23,dirty,77])) ==
  some ([some dirty.toNat,some 42,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [3,11,23,dirty,77])) ==
  some ([some 3,some 77,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [8,11,23,dirty,77])) ==
  some ([some 8,some 99,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.run (compareCode (word 1)) [dirty,77] == some [0,dirty,77]
#guard Scalar.run (compareCode (word dirty.toNat)) [dirty,77] == some [1,dirty,77]
#guard Scalar.run (compareCode (word 1)) [] == none
#guard match Evm.run selected.realization.ir (machine []) with | .fault => true | _ => false
#guard (compile 0 (.local 0) cases fallback).isNone
#guard (compile 2 (.local 0) cases fallback).isNone

def emptyCompiled := (compile 3 (.local 0) (.nil : Cases [] [] root 3) fallback).get (by rfl)
def emptyBlock := emptyCompiled.emit.get (by rfl)
def emptySelected := (LoopSelection.selectBlock emptyBlock).get (by decide)
#guard observe (Evm.run emptySelected.realization.ir (machine [1,11,23,dirty,77])) ==
  some ([some 1,some 99,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)

def lastAccessible : Stmt [] [] root 17 :=
  .assign (fun _ : Fin 1 => .local 15) (.literal (word 7))
def inaccessible : Stmt [] [] root 17 :=
  .assign (fun _ : Fin 1 => .local 16) (.literal (word 7))
def wide := (compile 4 (.literal (word 1)) (.cons (word 1) lastAccessible .nil)
  (.skip : Stmt [] [] root 17)).get (by rfl)
def tooWide := (compile 4 (.literal (word 1)) (.cons (word 1) inaccessible .nil)
  (.skip : Stmt [] [] root 17)).get (by rfl)
#guard wide.emit.isSome
#guard tooWide.emit.isNone
-- Prefix capacity is separate from complete switch/runtime validity.
#guard Scalar.stackBound (compareCode (word 1)) 1022
#guard !(Scalar.stackBound (compareCode (word 1)) 1023)
-- Height-range tracking does not certify a DUP operand's existence.
-- The same empty input has capacity but run(compareCode) underflows above.
#guard Scalar.stackBound (compareCode (word 1)) 0
#guard (observe (Evm.run selected.realization.ir
  (machine (1::11::23::List.replicate 1024 dirty)))).isSome

-- Duplicate source labels remain refused by the EXISTING JSON decoder.
def caseJson (value : String) : Lean.Json := Lean.Json.mkObj
  [("nodeType",.str "YulCase"),("value",JsonCompilation.Controls.lit value),
   ("body",JsonCompilation.Controls.block #[])]
def duplicateJson := JsonCompilation.Controls.node #[Lean.Json.mkObj
  [("nodeType",.str "YulSwitch"),("expression",JsonCompilation.Controls.lit "1"),
   ("cases",.arr #[caseJson "1",caseJson "1"])]]
#guard match Solidity.Frontend.YulJson.Words.check [] 12 duplicateJson with
  | .error _ => true | _ => false
end SolidityBridge.Yul.SwitchCompilation.Controls
