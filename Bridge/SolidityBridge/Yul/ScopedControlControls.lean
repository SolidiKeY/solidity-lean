import SolidityBridge.Yul.ScopedControl
import SolidityBridge.Yul.ArithmeticSelectionControls
/-! Original Yul let/zero scopes containing actual structured branches.
Synthetic kernel/model controls only; Source/G24/native adequacy is separate. -/
namespace SolidityBridge.Yul.ScopedControl.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
abbrev dirty := ArithmeticSelection.Controls.dirty
abbrev machine := ArithmeticSelection.Controls.machine
abbrev observe := ArithmeticSelection.Controls.observe

def initializer (value : Nat) : ProducerExpressions.Compiled 5
    (.literal (word value) : Expr [] [] 2 1) :=
  (PureExpressions.compile 5 _).get (by rfl)
def increment : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 3 :=
  .assign (fun _ : Fin 1 => .local 1)
    (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .local 0)))
def nested : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 3 :=
  .if_ (.local 0) (.if_ (.local 2) increment)
def body := (NormalControl.compile 5 nested).get (by rfl)
def statement (value : Nat) : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 2 :=
  .let_ 1 (.literal (word value)) nested
def block (value : Nat) := (letOneEmit (initializer value) body).get (by rfl)
def selectedSeven := (LoopSelection.selectBlock (block 7)).get (by decide)
def selectedZero := (LoopSelection.selectBlock (block 0)).get (by decide)
def selectedDirty := (LoopSelection.selectBlock (block dirty.toNat)).get (by decide)
#check letOne_source (initializer 7) body #v[11,23]
#check letOne_structured (initializer 7) body (block 7) rfl #v[11,23] [dirty,77]
#check selectedSeven.lowering.success [11,23,dirty,77] [18,23,dirty,77] (machine [11,23,dirty,77]) rfl
#guard (evalStmt 6 .nil True.intro (statement 7) ⟨(initializer 7).profile,body.profile⟩
  (ProducerExpressions.sourceLocals #v[11,23])).map
  (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal)) == some (18,23,true)
#guard (letOneUpdate (initializer 7) body #v[11,23]).toList == [18,23]
#guard (letOneUpdate (initializer 0) body #v[11,23]).toList == [11,23]
#guard (letOneUpdate (initializer dirty.toNat) body #v[11,23]).toList == [dirty+11,23]
#guard observe (Evm.run selectedSeven.realization.ir (machine [11,23,dirty,77])) ==
  some ([some 18,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selectedZero.realization.ir (machine [11,23,dirty,77])) ==
  some ([some 11,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selectedSeven.realization.ir (machine [11,0,dirty,77])) ==
  some ([some 11,some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard (observe (Evm.run selectedDirty.realization.ir (machine [11,23,dirty,77]))).map
  (fun out => out.1) == some [some (dirty.toNat+11),some 23,some dirty.toNat,some 77]
#guard match Evm.run selectedSeven.realization.ir (machine []) with | .fault => true | _ => false

def zeroFirst : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 4 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal (word (2^200+257)))
def zeroIncrement : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 4 :=
  .assign (fun _ : Fin 1 => .local 2)
    (.builtin (.pure .add) (Fin.cases (.local 2) (fun _ => .literal (word 9))))
def zeroBodyStatement := Stmt.seq zeroFirst (.if_ (.local 0) zeroIncrement)
def zeroBody := (NormalControl.compile 5 zeroBodyStatement).get (by rfl)
def zeroBlock := (zeroEmit (n:=2) (fresh:=2) zeroBody).get (by rfl)
def zeroSelected := (LoopSelection.selectBlock zeroBlock).get (by rfl)
#check zero_source (n:=2) (fresh:=2) zeroBody #v[11,23]
#check zero_structured (n:=2) (fresh:=2) zeroBody zeroBlock rfl #v[11,23] [dirty,77]
#guard (zeroUpdate (n:=2) (fresh:=2) zeroBody #v[11,23]).toList == [20,23]
#guard observe (Evm.run zeroSelected.realization.ir (machine [11,23,dirty,77])) ==
  some ([some 20,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard Scalar.run (pushPrefix [0,0]) [11,23,dirty,77] == some [0,0,11,23,dirty,77]
#guard Scalar.run (popPrefix 2) [dirty,0,20,23,dirty,77] == some [20,23,dirty,77]
#guard Scalar.run (popPrefix 2) [dirty] == none
#guard Scalar.stackBound (pushPrefix [0,0]) 1022
#guard !(Scalar.stackBound (pushPrefix [0,0]) 1023)
#guard (observe (Evm.run zeroSelected.realization.ir (machine (11::23::List.replicate 1024 dirty)))).isSome

def emptyBody := (NormalControl.compile 1 (.skip : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 2)).get (by rfl)
def emptyBlock := (zeroEmit (n:=2) (fresh:=0) emptyBody).get (by rfl)
def emptySelected := (LoopSelection.selectBlock emptyBlock).get (by rfl)
#guard observe (Evm.run emptySelected.realization.ir (machine [11,23,dirty,77])) ==
  some ([some 11,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)

-- Live positions include the freshly pushed scope word. Context17 is valid,
-- but only positions0..15 select the unchanged DUP/SWAP operations.
def wideInitializer : ProducerExpressions.Compiled 5 (.literal (word 7) : Expr [] [] 16 1) :=
  (PureExpressions.compile 5 _).get (by rfl)
def lastBody := (NormalControl.compile 5
  (.assign (fun _ : Fin 1 => .local 15) (.literal (word 1)) : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 17)).get (by rfl)
def inaccessibleBody := (NormalControl.compile 5
  (.assign (fun _ : Fin 1 => .local 16) (.literal (word 1)) : Stmt [] [] (⟨false,false⟩ : Solidity.Yul.Control) 17)).get (by rfl)
#guard (letOneEmit wideInitializer lastBody).isSome
#guard (letOneEmit wideInitializer inaccessibleBody).isNone
#guard (PureExpressions.compile 0 (.literal (word 7) : Expr [] [] 2 1)).isNone
end SolidityBridge.Yul.ScopedControl.Controls
