import SolidityBridge.Yul.ScopedSwitch
import SolidityBridge.Yul.SwitchControlControls
/-! Original-source and selected mathematical-model scoped-switch controls;
no Solidity admission/native/G24 or full physical capacity assertion. -/
namespace SolidityBridge.Yul.ScopedSwitch.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
abbrev root := SwitchCompilation.Controls.root
abbrev dirty := SwitchCompilation.Controls.dirty
abbrev machine := SwitchCompilation.Controls.machine
abbrev observe := SwitchCompilation.Controls.observe

-- Local0 is a fresh selector, local1 a fresh dirty word; outer locals2..4.
def chosen : Stmt [] [] root 5 := .seq
  (.assign (fun _ : Fin 1 => .local 3)
    (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .local 3))))
  (.assign (fun _ : Fin 1 => .local 2) (.local 0))
def body : Stmt [] [] root 5 := .seq
  (.assign (fun _ : Fin 1 => .local 0) (.literal (word 1)))
  (.switch (.local 0) (.cons (word 1) chosen .nil) .skip)
-- Two nested prefixes, initializer once in the old context, both retired.
def nested : Stmt [] [] root 3 :=
  .let_ 1 (.literal (word dirty.toNat)) (.zero 1 body)
def compiled := (compile 9 nested).get (by rfl)
def block := compiled.emit.get (by rfl)
def selected := (LoopSelection.selectBlock block).get (by decide)
#check compiled.source #v[8,11,23]
#check compiled.structured block rfl #v[8,11,23] [dirty,77]
#guard (compiled.update #v[8,11,23]).toList == [1,dirty+11,23]
#guard (evalStmt 9 .nil True.intro nested compiled.profile
  (ProducerExpressions.sourceLocals #v[8,11,23])).map
  (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal)) ==
    some (1,dirty.toNat+11,23,true)
#guard observe (Evm.run selected.realization.ir (machine [8,11,23,dirty,77])) ==
  some ([some 1,some (dirty.toNat+11),some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
-- Initializer is evaluated in old locals: copy oldacc11, not a new zero.
def copied : Stmt [] [] root 3 := .let_ 1 (.local 1) (.zero 1 body)
def copiedCompiled := (compile 9 copied).get (by rfl)
#guard (copiedCompiled.update #v[8,11,23]).toList == [1,22,23]
-- Zero-initialized multiword prefix, with actual fresh-slot writes.
def zeroBody : Stmt [] [] root 5 := .seq
  (.assign (fun _ : Fin 1 => .local 1) (.literal (word dirty.toNat))) body
def zeroStatement : Stmt [] [] root 3 := .zero 2 zeroBody
def zeroCompiled := (compile 9 zeroStatement).get (by rfl)
def zeroBlock := zeroCompiled.emit.get (by rfl)
def zeroSelected := (LoopSelection.selectBlock zeroBlock).get (by decide)
#guard (zeroCompiled.update #v[8,11,23]).toList == [1,dirty+11,23]
#guard observe (Evm.run zeroSelected.realization.ir (machine [8,11,23,dirty,77])) ==
  some ([some 1,some (dirty.toNat+11),some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
-- Scope under conditional/sequence; false guard must preserve all old locals.
def contextual : Stmt [] [] root 3 := .seq .skip (.if_ (.local 2) nested)
def contextualCompiled := (compile 11 contextual).get (by rfl)
#guard (contextualCompiled.update #v[8,11,0]).toList == [8,11,0]
#guard (contextualCompiled.update #v[8,11,23]).toList == [1,dirty+11,23]
-- Empty prefix is identity on scope shape; previous compiler's test remains.
def emptyScope : Stmt [] [] root 3 := .zero 0 SwitchCompilation.Controls.statement
def emptyCompiled := (compile 9 emptyScope).get (by rfl)
#guard (emptyCompiled.update #v[1,11,23]).toList == [3,21,23]
#guard (SwitchControl.compile 16 emptyScope).isNone
-- Case bodies have not been generalized by this scope adapter.
#guard (compile 16 SwitchControl.Controls.nestedCase).isNone
#guard (compile 0 nested).isNone
#guard (compile 2 nested).isNone
#guard match Evm.run selected.realization.ir (machine []) with | .fault => true | _ => false
-- Prefix height capacity and model execution are explicitly separate.
#guard Scalar.stackBound (pushPrefix [dirty,1]) 1022
#guard !(Scalar.stackBound (pushPrefix [dirty,1]) 1023)
#guard (observe (Evm.run selected.realization.ir
  (machine (8::11::23::List.replicate 1024 dirty)))).isSome
-- Live shifted position15 works, position16 is intrinsically valid but refused.
def shifted (i : Fin 18) : Stmt [] [] root 17 := .zero 1
  (.switch (.literal (word 1))
    (.cons (word 1) (.assign (fun _ : Fin 1 => .local i) (.literal (word 7))) .nil) .skip)
def accessible := (compile 6 (shifted 15)).get (by rfl)
def inaccessible := (compile 6 (shifted 16)).get (by rfl)
#guard accessible.emit.isSome
#guard inaccessible.emit.isNone
end SolidityBridge.Yul.ScopedSwitch.Controls
