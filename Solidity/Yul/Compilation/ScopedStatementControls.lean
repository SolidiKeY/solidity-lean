import Solidity.Yul.Compilation.ScopedStatements
namespace Solidity.Yul.Compilation.ScopedStatements.Controls
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions

def rhs : Expr [] [] 2 1 := .builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .local 1))
def body : Stmt [] [] ⟨false,false⟩ 3 := .seq
  (.assign (fun _ : Fin 1 => .local 1) (.builtin (.pure .exp) (Fin.cases (.local 0) (fun _ => .literal (word 2)))))
  (.assign (fun _ : Fin 1 => .local 0) (.literal (word 999)))
def statement : Stmt [] [] ⟨false,false⟩ 2 := .let_ 1 rhs body
def compiled := (compile 5 statement).get (by rfl)
def code : Program := [readSlot ⟨1,by decide⟩,readSlot ⟨1,by decide⟩,.op .ADD] ++
  ([pushWord 2,readSlot ⟨1,by decide⟩,.op .EXP] ++ writeSlot ⟨1,by decide⟩) ++
  ([pushWord 999] ++ writeSlot ⟨0,by decide⟩) ++ popPrefix 1
example : compiled.lowered.code 0 = some code := rfl
example (tail : Stack) : run code ([3,4] ++ tail) = some ([49,4] ++ tail) :=
  compiled.lowered.correct 0 code rfl #v[3,4] #v[] tail
example : evalStmt 5 .nil True.intro statement compiled.profile (sourceLocals #v[3,4]) =
    some ⟨sourceLocals #v[49,4],.normal⟩ := compiled.source #v[3,4]
example : compiled.lowered.code 1 = none := rfl
example : (compile 4 statement).isNone = true := rfl
example : (PureStatements.compile 5 statement).isNone = true := rfl
example : run code [3] = none := rfl
example : stackBound code 1021 = true := by decide
example : stackBound code 1022 = false := by decide

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def zeroBody : Stmt [] [] ⟨false,false⟩ 4 := .seq
  (.assign (fun _ : Fin 1 => .local 3) (.builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .local 2))))
  (.assign (fun _ : Fin 1 => .local 0) (.literal (word 99)))
def zeroStatement : Stmt [] [] ⟨false,false⟩ 2 := .zero 2 zeroBody
def zeroCompiled := (compile 5 zeroStatement).get (by rfl)
example : zeroCompiled.update #v[dirty,7] = #v[dirty,dirty] := by decide +kernel
example : (compile 2 (Stmt.zero (c := ⟨false,false⟩) (n := 2) 0 .skip)).isSome = true := rfl
-- Nested fresh prefixes disappear, mutations of old locals survive.
def nested : Stmt [] [] ⟨false,false⟩ 2 := .let_ 1 rhs
  (.let_ 1 (.local 0) (.assign (fun _ : Fin 1 => .local 2) (.local 0)))
def nestedCompiled := (compile 4 nested).get (by rfl)
example : nestedCompiled.update #v[3,4] = #v[7,4] := rfl
example : (compile 3 nested).isNone = true := rfl
example : (compile 3 (Stmt.if_ (c := ⟨false,false⟩) (n := 1) (.literal (word 1)) .skip)).isNone = true := rfl
def tooDeep : Stmt [] [] ⟨false,false⟩ 16 := .zero 1
  (.assign (fun _ : Fin 1 => .local 1) (.local 16))
def tooDeepCompiled := (compile 3 tooDeep).get (by rfl)
example : tooDeepCompiled.lowered.code 0 = none := rfl
example : run code ([3,4] ++ List.replicate 1020 9) = some ([49,4] ++ List.replicate 1020 9) :=
  compiled.lowered.correct 0 code rfl #v[3,4] #v[] (List.replicate 1020 9)

def lastAccessible : Stmt [] [] ⟨false,false⟩ 15 := .zero 1
  (.assign (fun _ : Fin 1 => .local 1) (.local 15))
def lastCompiled := (compile 3 lastAccessible).get (by rfl)
def lastCode : Program := [pushWord 0,readSlot ⟨15,by decide⟩] ++ writeSlot ⟨1,by decide⟩ ++ popPrefix 1
example : lastCompiled.lowered.code 0 = some lastCode := rfl
example (tail : Stack) : run lastCode ([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] ++ tail) =
    some ([15,2,3,4,5,6,7,8,9,10,11,12,13,14,15] ++ tail) :=
  lastCompiled.lowered.correct 0 lastCode rfl #v[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] #v[] tail
#print axioms compiled
#print axioms zeroCompiled
#print axioms nestedCompiled
end Solidity.Yul.Compilation.ScopedStatements.Controls
