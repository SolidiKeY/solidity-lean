import Solidity.Yul.Compilation.ExpressionShapes

/-! Original intrinsic Yul subtraction and its actual visitor/lowering. Word
order, live shifted depth, operand sufficiency and capacity are independent. -/
namespace Solidity.Yul.Compilation.ExpressionShapes.Controls
open Backend Scalar LabelExec Closed ProducerExpressions

def args : Fin 2 → Solidity.Yul.Expr [] [] 2 1 :=
  Fin.cases (.local 0) (fun _ => .local 1)
def expression : Solidity.Yul.Expr [] [] 2 1 := .builtin (.pure .sub) args
def compiled : ProducerExpressions.Compiled 2 expression :=
  ProducerExpressions.binary subBridge (localExpr 0 0) (localExpr 0 1)
def code := (compiled.lowered.code 0).get (by rfl)
def shiftedCode := (compiled.lowered.code 14).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_visit : ProducerExpressions.compile 2 expression = some compiled := by rfl

theorem actual_code : code = [.op (.DUP 1),.op (.DUP 1),.op .SUB] := by rfl

theorem shape : CodeShape code 2 3 :=
  ExpressionShapes.binary selectSub (lowerLocal (0 : Fin 2)) (lowerLocal (1 : Fin 2)) rfl
    (local_shape 0) (local_shape 1) 0 code (Option.some_get (by rfl)).symm

theorem shifted_shape : CodeShape shiftedCode 16 17 :=
  ExpressionShapes.binary selectSub (lowerLocal (0 : Fin 2)) (lowerLocal (1 : Fin 2)) rfl
    (local_shape 0) (local_shape 1) 14 shiftedCode (Option.some_get (by rfl)).symm

theorem source (a b : Scalar.Word) :
    evalExpr 2 .nil True.intro expression compiled.profile (sourceLocals #v[a,b]) =
      some (fun _ => (a-b).toFin) := compiled.source #v[a,b]

theorem target_run (a b : Scalar.Word) (caller : Stack) :
    run code ([a,b] ++ caller) = some ((a-b) :: ([a,b] ++ caller)) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    compiled.lowered.correct 0 code (Option.some_get (by rfl)).symm #v[a,b] #v[] caller

/-- The shifted physical DUP16 case preserves the whole newer prefix as well
as both old locals/caller; allocation offsets are not identified with depth. -/
theorem shifted_run (a b : Scalar.Word) (newer : Vector Scalar.Word 14) (caller : Stack) :
    run shiftedCode (newer.toList ++ ([a,b] ++ caller)) =
      some ((a-b) :: (newer.toList ++ ([a,b] ++ caller))) :=
  compiled.lowered.correct 14 shiftedCode (Option.some_get (by rfl)).symm #v[a,b] newer caller

theorem capacity_exact (height : Int) :
    stackBound code height = true ↔ 0 ≤ height ∧ height+2 ≤ 1024 := by
  change ([height,height+1,(height+1)+1,((height+1)+1)+(-1)].all safeHeight) = true ↔ _
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

/-- Entry1023/final1024 fit, while the real intermediate1025 is refused. -/
theorem overflow_separate :
    run code ([dirty,5] ++ List.replicate 1021 0) =
      some ((dirty-5) :: ([dirty,5] ++ List.replicate 1021 0)) ∧ stackBound code 1023 = false :=
  ⟨target_run dirty 5 _,by decide⟩

#guard compiled.lowered.code 15 == none
#guard run code [dirty] == none
#guard stackBound code 1
#guard run code [dirty,5,88] == some [dirty-5,dirty,5,88]
#guard run code [5,dirty,88] == some [5-dirty,5,dirty,88]
#guard !(run code [dirty,5,88] == some [5-dirty,dirty,5,88])
#guard (dirty-5).toNat = 2^200+252
#guard stackBound code 1022
#guard !(stackBound code 1023)
#check source dirty 5
#check target_run dirty 5 [88,dirty]
#check ShapeCapacity.code_frame shape #v[dirty,5]
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.actual_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_code
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shape
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.shifted_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_shape
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_run
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.capacity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capacity_exact
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.Controls.overflow_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_separate
end Solidity.Yul.Compilation.ExpressionShapes.Controls
