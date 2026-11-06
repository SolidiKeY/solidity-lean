import Solidity.Yul.Compilation.ScopedRawStatements
import Solidity.Yul.Compilation.OpenExpressionControls
namespace Solidity.Yul.Compilation.ScopedRawStatements.Controls
open Backend Scalar
open Solidity.Yul.Closed
open OpenExpressions.Controls (types small flag state function)
def body : Stmt [] types ⟨false,false⟩ 2 := .seq
  (.assign (fun _ : Fin 1 => .external flag.writeRef) (.local 0))
  (.seq
    (.assign (fun _ : Fin 1 => .local 1) (.builtin (.pure .exp) (Fin.cases (.local 0) (fun _ => .literal (word 2)))))
    (.assign (fun _ : Fin 1 => .local 0) (.literal (word 999))))
def statement : Stmt [] types ⟨false,false⟩ 1 := .let_ 1 (.external small.readRef) body
def policy : Policy.StmtP .A statement := by apply (Policy.stmt_iff .A _).mp; rfl
def compiled : OpenStatements.Compiled 6 statement policy := (compile 6 statement policy).get (by rfl)
def code : Program := [readSlot ⟨1,by decide⟩,readSlot ⟨0,by decide⟩] ++ writeSlot ⟨3,by decide⟩ ++
  ([pushWord 2,readSlot ⟨1,by decide⟩,.op .EXP] ++ writeSlot ⟨1,by decide⟩) ++
  ([pushWord 999] ++ writeSlot ⟨0,by decide⟩) ++ popPrefix 1
theorem emitted : compiled.packed.lowered.code 0 = some code := rfl
example : (OpenStatements.updated compiled state).locals 0 = word 66049 := by decide +kernel
example : (OpenStatements.updated compiled state).cells small = word 257 := by decide +kernel
example : (OpenStatements.updated compiled state).cells flag = word 257 := by decide +kernel
example : (OpenStatements.updated compiled state).cells (.selector function) = word (2^32+1) := by decide +kernel
example : (OpenStatements.updated compiled state).cells (.address function) = word (2^256-1) := by decide +kernel
example (input : WordState types 1) (tail : Stack) :
    DirectBindings.eval 6 compiled.support policy input = some ⟨OpenStatements.updated compiled input,.normal⟩ ∧
    run code ((OpenExpressions.encoded input).toList ++ tail) =
      some ((compiled.packed.update (OpenExpressions.encoded input)).toList ++ tail) :=
  ScopedRawStatements.executes compiled input code emitted tail
example : compiled.packed.lowered.code 1 = none := rfl
example : (compile 5 statement policy).isNone = true := rfl
example : run code [] = none := rfl
theorem capacity_exact (height : Int) : stackBound code height = true ↔ 0 ≤ height ∧ height+3 ≤ 1024 := by
  simp only [code,readSlot,writeSlot,popPrefix,pushWord,stackBound,heightTrace,stackDelta,numericDelta,Scalar.unary,Scalar.binary,Scalar.ternary,
    List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,Option.isSome_some,Option.isSome_none,
    Bool.false_eq_true,if_true,if_false,safeHeight,decide_eq_true_eq,List.cons_append,List.nil_append]
  omega
example : stackBound code 1021 = true := by decide
example : stackBound code 1022 = false := by decide
#print axioms compiled
end Solidity.Yul.Compilation.ScopedRawStatements.Controls
