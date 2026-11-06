import Solidity.Yul.Compilation.ArithmeticVisitorShapes

/-! Nested original arithmetic visitor: child metadata is derived recursively,
not supplied for this witness. Only target operand/resource facts are added. -/
namespace Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls
open Backend Scalar LabelExec Closed ProducerExpressions

def leftArgs : Fin 2 → Solidity.Yul.Expr [] [] 2 1 :=
  Fin.cases (.local 0) (fun _ => .literal (Solidity.Yul.word 3))
def rightArgs : Fin 2 → Solidity.Yul.Expr [] [] 2 1 :=
  Fin.cases (.local 1) (fun _ => .literal (Solidity.Yul.word 7))
def args : Fin 2 → Solidity.Yul.Expr [] [] 2 1 :=
  Fin.cases (.builtin (.pure .mul) leftArgs) (fun _ => .builtin (.pure .add) rightArgs)
def expression : Solidity.Yul.Expr [] [] 2 1 := .builtin (.pure .sub) args
def compiled := (ProducerExpressions.compile 3 expression).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def shiftedCode := (compiled.lowered.code 13).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_visit : ProducerExpressions.compile 3 expression = some compiled :=
  (Option.some_get (by rfl)).symm

theorem actual_code : code = [pushWord 7,.op (.DUP 2),.op .ADD,
    pushWord 3,.op (.DUP 2),.op .MUL,.op .SUB] := by rfl

theorem shape : CodeShape code 2 3 :=
  visit_shape 3 expression compiled actual_visit 0 code (Option.some_get (by rfl)).symm

theorem shifted_shape : CodeShape shiftedCode 15 16 :=
  visit_shape 3 expression compiled actual_visit 13 shiftedCode (Option.some_get (by rfl)).symm

theorem source (a b : Scalar.Word) :
    evalExpr 3 .nil True.intro expression compiled.profile (sourceLocals #v[a,b]) =
      some (fun _ => ((a*3)-(b+7)).toFin) := compiled.source #v[a,b]

theorem target_run (a b : Scalar.Word) (caller : Stack) :
    run code ([a,b] ++ caller) = some (((a*3)-(b+7)) :: ([a,b] ++ caller)) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    compiled.lowered.correct 0 code (Option.some_get (by rfl)).symm #v[a,b] #v[] caller

theorem shifted_run (a b : Scalar.Word) (newer : Vector Scalar.Word 13) (caller : Stack) :
    run shiftedCode (newer.toList ++ ([a,b] ++ caller)) =
      some (((a*3)-(b+7)) :: (newer.toList ++ ([a,b] ++ caller))) :=
  compiled.lowered.correct 13 shiftedCode (Option.some_get (by rfl)).symm #v[a,b] newer caller

theorem trace (h : Int) : heightTrace code h = [h,h+1,h+2,h+1,h+2,h+3,h+2,h+1] := by
  change [h,h+1,(h+1)+1,((h+1)+1)+(-1),(((h+1)+1)+(-1))+1,
    ((((h+1)+1)+(-1))+1)+1,(((((h+1)+1)+(-1))+1)+1)+(-1),
    ((((((h+1)+1)+(-1))+1)+1)+(-1))+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem capacity_exact (height : Int) :
    stackBound code height = true ↔ 0 ≤ height ∧ height+3 ≤ 1024 := by
  simp only [stackBound,trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

/-- Entry1022/final1023 fit; nested operand evaluation peaks at1025. -/
theorem overflow_separate :
    run code ([dirty,5] ++ List.replicate 1020 0) =
      some (((dirty*3)-(5+7)) :: ([dirty,5] ++ List.replicate 1020 0)) ∧
    stackBound code 1022 = false := ⟨target_run dirty 5 _,by decide⟩

#guard (ProducerExpressions.compile 2 expression).isNone
#guard compiled.lowered.code 14 == none
#guard run code [dirty] == none
#guard stackBound code 1
#guard run code [dirty,5,88] == some [(dirty*3)-(5+7),dirty,5,88]
#guard !(run code [dirty,5,88] == some [(5+7)-(dirty*3),dirty,5,88])
#guard ((dirty*3)-(5+7)).toNat = 3*2^200+759
#guard stackBound code 1021
#guard !(stackBound code 1022)
#check source dirty 5
#check target_run dirty 5 [88,dirty]
#check ShapeCapacity.code_frame shape #v[dirty,5]
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.actual_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_code
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shape
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.shifted_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_shape
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_run
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms trace
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.capacity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capacity_exact
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls.overflow_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_separate
end Solidity.Yul.Compilation.ArithmeticVisitorShapes.Controls
