import Solidity.Yul.Compilation.StatementVisitorShapes
import Solidity.Yul.Compilation.ArithmeticVisitorShapesControls

/-! Original statement sequence with a real read-after-write dependency.
The second RHS reads the first assignment's updated local, not old inputs. -/
namespace Solidity.Yul.Compilation.StatementVisitorShapes.Controls
open Backend Scalar LabelExec Closed ProducerExpressions
abbrev arithmetic := ArithmeticVisitorShapes.Controls.compiled
abbrev arithmeticExpr := ArithmeticVisitorShapes.Controls.expression

def firstTargets : Fin 1 → Solidity.Yul.Target [] 2 := fun _ => .local 0
def secondTargets : Fin 1 → Solidity.Yul.Target [] 2 := fun _ => .local 1
def secondArgs : Fin 2 → Solidity.Yul.Expr [] [] 2 1 :=
  Fin.cases (.local 1) (fun _ => .local 0)
def secondExpr : Solidity.Yul.Expr [] [] 2 1 := .builtin (.pure .sub) secondArgs
def secondRhs : ProducerExpressions.Compiled 3 secondExpr :=
  ProducerExpressions.binary subBridge (localExpr 1 1) (localExpr 1 0)
def first : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .assign firstTargets arithmeticExpr
def second : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .assign secondTargets secondExpr
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .seq first second
def firstCompiled : ProducerStatements.Compiled 4 first :=
  ProducerStatements.assignTargets firstTargets arithmetic
def secondCompiled : ProducerStatements.Compiled 4 second :=
  ProducerStatements.assignTargets secondTargets secondRhs
def compiled : ProducerStatements.Compiled 5 statement :=
  ProducerStatements.seq firstCompiled secondCompiled
def code := (compiled.lowered.code 0).get (by rfl)
def shiftedCode := (compiled.lowered.code 13).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def result (a b : Scalar.Word) : Scalar.Word := (a*3)-(b+7)

theorem actual_visit : ProducerStatements.compile 5 statement = some compiled := by rfl

theorem actual_code : code = [pushWord 7,.op (.DUP 2),.op .ADD,
    pushWord 3,.op (.DUP 2),.op .MUL,.op .SUB,.op (.SWAP 0),.op .POP,
    .op (.DUP 0),.op (.DUP 2),.op .SUB,.op (.SWAP 1),.op .POP] := by rfl

theorem shape : CodeShape code 2 2 :=
  visit_shape 5 statement compiled actual_visit 0 code (Option.some_get (by rfl)).symm

theorem shifted_shape : CodeShape shiftedCode 15 15 :=
  visit_shape 5 statement compiled actual_visit 13 shiftedCode (Option.some_get (by rfl)).symm

theorem updated (a b : Scalar.Word) :
    compiled.update #v[a,b] = #v[result a b,b-result a b] := by rfl

theorem source (a b : Scalar.Word) :
    evalStmt 5 .nil True.intro statement compiled.profile (sourceLocals #v[a,b]) =
      some ⟨sourceLocals #v[result a b,b-result a b],.normal⟩ := compiled.source #v[a,b]

theorem target_run (a b : Scalar.Word) (caller : Stack) :
    run code ([a,b] ++ caller) = some ([result a b,b-result a b] ++ caller) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    compiled.lowered.correct 0 code (Option.some_get (by rfl)).symm #v[a,b] #v[] caller

theorem shifted_run (a b : Scalar.Word) (newer : Vector Scalar.Word 13) (caller : Stack) :
    run shiftedCode (newer.toList ++ ([a,b] ++ caller)) =
      some (newer.toList ++ ([result a b,b-result a b] ++ caller)) :=
  compiled.lowered.correct 13 shiftedCode (Option.some_get (by rfl)).symm #v[a,b] newer caller

theorem trace (h : Int) : heightTrace code h = [h,h+1,h+2,h+1,h+2,h+3,h+2,h+1,h+1,h,h+1,h+2,h+1,h+1,h] := by
  change [h,(h)+(1),((h)+(1))+(1),(((h)+(1))+(1))+(-1),((((h)+(1))+(1))+(-1))+(1),(((((h)+(1))+(1))+(-1))+(1))+(1),((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1),(((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1),((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0),(((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0))+(-1),((((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0))+(-1))+(1),(((((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0))+(-1))+(1))+(1),((((((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0))+(-1))+(1))+(1))+(-1),(((((((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0))+(-1))+(1))+(1))+(-1))+(0),((((((((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0))+(-1))+(1))+(1))+(-1))+(0))+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem capacity_exact (height : Int) :
    stackBound code height = true ↔ 0 ≤ height ∧ height+3 ≤ 1024 := by
  simp only [stackBound,trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

/-- Scalar entry/final1022 fit, but nested RHS evaluation peaks at1025. -/
theorem overflow_separate :
    run code ([dirty,5] ++ List.replicate 1020 0) =
      some ([result dirty 5,5-result dirty 5] ++ List.replicate 1020 0) ∧
    stackBound code 1022 = false := ⟨target_run dirty 5 _,by decide⟩

#guard (ProducerStatements.compile 4 statement).isNone
#guard compiled.lowered.code 14 == none
#guard run code [dirty] == none
#guard stackBound code 1
#guard run code [dirty,5,88] == some [result dirty 5,5-result dirty 5,88]
#guard !(run code [dirty,5,88] == some [result dirty 5,5-dirty,88])
#guard (result dirty 5).toNat = 3*2^200+759
#guard stackBound code 1021
#guard !(stackBound code 1022)
#check source dirty 5
#check target_run dirty 5 [88,dirty]
#check ShapeCapacity.code_frame shape #v[dirty,5]
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.actual_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_code
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shape
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.shifted_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_shape
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.updated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms updated
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_run
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms trace
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.capacity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capacity_exact
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.Controls.overflow_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_separate
end Solidity.Yul.Compilation.StatementVisitorShapes.Controls
