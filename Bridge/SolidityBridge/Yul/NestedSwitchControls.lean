import SolidityBridge.Yul.NestedSwitch
import SolidityBridge.Yul.ScopedSwitchControls
/-! Original-source/selected-model witnesses of nested switch cases/defaults
with lexical scopes. No frontend admission/native/G24/capacity claim. -/
namespace SolidityBridge.Yul.NestedSwitch.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
abbrev root := SwitchCompilation.Controls.root
abbrev dirty := SwitchCompilation.Controls.dirty
abbrev machine := SwitchCompilation.Controls.machine
abbrev observe := SwitchCompilation.Controls.observe

-- After the scoped nested switch, the full dirty accumulator chooses this arm.
def follow : Stmt [] [] root 3 := .switch (.local 1)
  (.cons (word (dirty.toNat+11))
    (.assign (fun _ : Fin 1 => .local 0) (.literal (word 3))) .nil) .skip
def arm : Stmt [] [] root 3 := .if_ (.local 2)
  (.seq ScopedSwitch.Controls.nested follow)
def fallback : Stmt [] [] root 3 := .switch (.local 0)
  (.cons (word 8) (.assign (fun _ : Fin 1 => .local 1) (.literal (word 42))) .nil) .skip
def statement : Stmt [] [] root 3 := .switch (.local 0)
  (.cons (word 1) arm
    (.cons (word 3) (.assign (fun _ : Fin 1 => .local 1) (.literal (word 999))) .nil)) fallback

def compiled := (compile 13 statement).get (by rfl)
def block := compiled.emit.get (by rfl)
def selected := (LoopSelection.selectBlock block).get (by decide)
#check compiled.source #v[1,11,23]
#check compiled.structured block rfl #v[1,11,23] [dirty,77]
-- Selector becomes3 inside the first arm; the later outercase must not run.
#guard (compiled.update #v[1,11,23]).toList == [3,dirty+11,23]
#guard (compiled.update #v[1,11,0]).toList == [1,11,0]
#guard (compiled.update #v[3,11,23]).toList == [3,999,23]
#guard (compiled.update #v[8,11,23]).toList == [8,42,23]
#guard (compiled.update #v[dirty,11,23]).toList == [dirty,11,23]
#guard (evalStmt 13 .nil True.intro statement compiled.profile
  (ProducerExpressions.sourceLocals #v[1,11,23])).map
  (fun out => ((out.vars 0).val,(out.vars 1).val,(out.vars 2).val,out.flow.isNormal)) ==
  some (3,dirty.toNat+11,23,true)
#guard observe (Evm.run selected.realization.ir (machine [1,11,23,dirty,77])) ==
  some ([some 3,some (dirty.toNat+11),some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [1,11,0,dirty,77])) ==
  some ([some 1,some 11,some 0,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [8,11,23,dirty,77])) ==
  some ([some 8,some 42,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
#guard observe (Evm.run selected.realization.ir (machine [dirty,11,23,dirty,77])) ==
  some ([some dirty.toNat,some 11,some 23,some dirty.toNat,some 77],some dirty.toNat,23,99,99,7,11,19,31,false)
-- Earlier concrete APIs retain their exact narrower domain/verdicts.
#guard (ScopedSwitch.compile 16 statement).isNone
#guard (SwitchControl.compile 16 SwitchControl.Controls.nestedCase).isNone
def formerlyRefused := (compile 9 SwitchControl.Controls.nestedCase).get (by rfl)
#guard (formerlyRefused.update #v[1,11,23]).toList == [3,21,23]
-- General compiler horizon obeys real evalCases fuel; no unlimited default.
#guard (compile 0 statement).isNone
#guard (compile 2 statement).isNone
#guard (compileArms 0 (Cases.nil : Cases [] [] root 3)).isNone
#guard (compileArms 1 (Cases.cons (word 1) (.skip : Stmt [] [] root 3) .nil)).isNone
#guard match Evm.run selected.realization.ir (machine []) with | .fault => true | _ => false
-- In-range source slots still obey the actual unchanged DUP/SWAP boundary.
def accessible := (compile 6 (ScopedSwitch.Controls.shifted 15)).get (by rfl)
def inaccessible := (compile 6 (ScopedSwitch.Controls.shifted 16)).get (by rfl)
#guard accessible.emit.isSome
#guard inaccessible.emit.isNone
-- Prefix height range is separate from operand availability and whole validity.
#guard Scalar.stackBound (SwitchCompilation.compareCode (word 1)) 0
#guard Scalar.run (SwitchCompilation.compareCode (word 1)) [] == none
#guard !(Scalar.stackBound (SwitchCompilation.compareCode (word 1)) 1023)
#guard (observe (Evm.run selected.realization.ir
  (machine (1::11::23::List.replicate 1024 dirty)))).isSome
end SolidityBridge.Yul.NestedSwitch.Controls
