import SolidityBridge.Yul.RecursiveScopes
import SolidityBridge.Yul.ArithmeticSelectionControls
/-! Concrete recursive original-Yul scope/branch/sequence visitor controls.
Pure kernel/model execution only, not native/Source attachment/G24 adequacy. -/
namespace SolidityBridge.Yul.RecursiveScopes.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
abbrev root : Control := ⟨false,false⟩
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def addInner : Stmt [] [] root 5 :=
  .assign (fun _ : Fin 1 => .local 3)
    (.builtin (.pure .add) (Fin.cases (.local 3) (fun _ => .local 0)))
def nested (value : Nat) : Stmt [] [] root 3 :=
  .if_ (.local 0) (.zero 1 (.let_ 1 (.literal (word value)) addInner))
def compiled (value : Nat) := (compile 6 (nested value)).get (by rfl)
def block (value : Nat) := (compiled value).emit.get (by rfl)
def selectedNine := (LoopSelection.selectBlock (block 9)).get (by decide)
def selectedDirty := (LoopSelection.selectBlock (block dirty.toNat)).get (by decide)
#check (compiled 9).source #v[1,11,23]
#check (compiled 9).structured (block 9) rfl #v[1,11,23] [dirty,77]
#check selectedNine.lowering.success [1,11,23,dirty,77] [1,20,23,dirty,77]
  (machine [1,11,23,dirty,77]) rfl
#guard (NormalControl.compile 6 (nested 9)).isNone
#guard (compile 0 (nested 9)).isNone
#guard (compile 2 (nested 9)).isNone
#guard ((compiled 9).update #v[1,11,23]).toList == [1,20,23]
#guard ((compiled 9).update #v[0,11,23]).toList == [0,11,23]
#guard ((compiled dirty.toNat).update #v[1,11,23]).toList == [1,dirty+11,23]
#guard (evalStmt 6 .nil True.intro (nested 9) (compiled 9).profile
  (ProducerExpressions.sourceLocals #v[1,11,23])).map
  (fun result => ((result.vars 0).val,(result.vars 1).val,(result.vars 2).val,result.flow.isNormal)) ==
  some (1,20,23,true)
#guard observe (Evm.run selectedNine.realization.ir (machine [1,11,23,dirty,77])) ==
  some ([some 1,some 20,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selectedNine.realization.ir (machine [0,11,23,dirty,77])) ==
  some ([some 0,some 11,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run selectedNine.realization.ir (machine [dirty,11,23,dirty,77]))).map
  (fun out => out.1) == some [some dirty.toNat,some 20,some 23,some dirty.toNat,some 77]
#guard (observe (Evm.run selectedDirty.realization.ir (machine [1,11,23,dirty,77]))).map
  (fun out => out.1) == some [some 1,some (dirty.toNat+11),some 23,some dirty.toNat,some 77]
#guard match Evm.run selectedNine.realization.ir (machine []) with | .fault => true | _ => false

def multiply : Stmt [] [] root 4 :=
  .assign (fun _ : Fin 1 => .local 2)
    (.builtin (.pure .mul) (Fin.cases (.local 2) (fun _ => .local 0)))
def combined : Stmt [] [] root 3 :=
  .seq (nested 9) (.if_ (.local 2) (.let_ 1 (.literal (word 7)) multiply))
def combination := (compile 7 combined).get (by rfl)
def combinationBlock := combination.emit.get (by rfl)
def combinationSelected := (LoopSelection.selectBlock combinationBlock).get (by decide)
#check combination.source #v[1,11,23]
#check combination.structured combinationBlock rfl #v[1,11,23] [dirty,77]
#guard (combination.update #v[1,11,23]).toList == [1,140,23]
#guard (combination.update #v[1,11,0]).toList == [1,20,0]
#guard observe (Evm.run combinationSelected.realization.ir (machine [1,11,23,dirty,77])) ==
  some ([some 1,some 140,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (compile 6 (.for_ .skip (.literal (word 0)) .skip .skip : Stmt [] [] root 3)).isNone
#guard (compile 6 (.leave : Stmt [] [] ⟨true,false⟩ 3)).isNone
#guard (compile 6 (.break_ : Stmt [] [] ⟨false,true⟩ 3)).isNone
#guard (compile 6 (.continue_ : Stmt [] [] ⟨false,true⟩ 3)).isNone

def inaccessible : Stmt [] [] root 16 :=
  .if_ (.literal (word 1)) (.zero 1 (.assign (fun _ : Fin 1 => .local 16) (.literal (word 7))))
def lastAccessible : Stmt [] [] root 16 :=
  .if_ (.literal (word 1)) (.zero 1 (.assign (fun _ : Fin 1 => .local 15) (.literal (word 7))))
def inaccessibleCompiled := (compile 6 inaccessible).get (by rfl)
def lastCompiled := (compile 6 lastAccessible).get (by rfl)
#guard inaccessibleCompiled.emit.isNone
#guard lastCompiled.emit.isSome
-- This checks a real prefix obligation, not whole-scope capacity.
#guard Scalar.stackBound (pushPrefix [0,9]) 1022
#guard !(Scalar.stackBound (pushPrefix [0,9]) 1023)
#guard (observe (Evm.run selectedNine.realization.ir
  (machine (1::11::23::List.replicate 1024 dirty)))).isSome
end SolidityBridge.Yul.RecursiveScopes.Controls
