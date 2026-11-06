import Solidity.Yul.Compilation.WordVisitorShapes

/-! Original mixed DIV/MOD/EQ/NOT compiler witness. Zero divisors return real
word results; complement high bits, operand order and caller remain explicit. -/
namespace Solidity.Yul.Compilation.WordVisitorShapes.Controls
open Backend Scalar LabelExec Closed ProducerExpressions

def operands : Fin 2 → Solidity.Yul.Expr [] [] 2 1 :=
  Fin.cases (.local 0) (fun _ => .local 1)
def pair : Fin 2 → Solidity.Yul.Expr [] [] 2 1 :=
  Fin.cases (.builtin (.pure .div) operands) (fun _ => .builtin (.pure .mod) operands)
def expression : Solidity.Yul.Expr [] [] 2 1 :=
  .builtin (.pure .not) (fun _ => .builtin (.pure .eq) pair)
def compiled := (WordExpressions.compile 4 expression).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def shiftedCode := (compiled.lowered.code 13).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def maxMinusOne : Scalar.Word := BitVec.ofNat 256 (2^256-2)
def maxWord : Scalar.Word := BitVec.ofNat 256 (2^256-1)
def result (a b : Scalar.Word) : Scalar.Word :=
  ~~~(Scalar.flag (selectDiv.value a b == selectMod.value a b))

theorem actual_visit : WordExpressions.compile 4 expression = some compiled :=
  (Option.some_get (by rfl)).symm

theorem actual_code : code = [.op (.DUP 1),.op (.DUP 1),.op .MOD,
    .op (.DUP 2),.op (.DUP 2),.op .DIV,.op .EQ,.op .NOT] := by rfl

theorem shape : CodeShape code 2 3 :=
  visit_shape 4 expression compiled actual_visit 0 code (Option.some_get (by rfl)).symm

theorem shifted_shape : CodeShape shiftedCode 15 16 :=
  visit_shape 4 expression compiled actual_visit 13 shiftedCode (Option.some_get (by rfl)).symm

theorem source (a b : Scalar.Word) :
    evalExpr 4 .nil True.intro expression compiled.profile (sourceLocals #v[a,b]) =
      some (fun _ => (result a b).toFin) := compiled.source #v[a,b]

theorem target_run (a b : Scalar.Word) (caller : Stack) :
    run code ([a,b] ++ caller) = some (result a b :: ([a,b] ++ caller)) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    compiled.lowered.correct 0 code (Option.some_get (by rfl)).symm #v[a,b] #v[] caller

theorem shifted_run (a b : Scalar.Word) (newer : Vector Scalar.Word 13) (caller : Stack) :
    run shiftedCode (newer.toList ++ ([a,b] ++ caller)) =
      some (result a b :: (newer.toList ++ ([a,b] ++ caller))) :=
  compiled.lowered.correct 13 shiftedCode (Option.some_get (by rfl)).symm #v[a,b] newer caller

/-- The quotient and remainder are zero for every dividend; EQ is1 and NOT preserves
all256 bits, yielding2^256-2 rather than a cleaned Boolean or a panic. -/
theorem result_zero (a : Scalar.Word) : result a 0 = maxMinusOne := by
  change (~~~(1 : Scalar.Word)) = maxMinusOne
  decide

theorem target_zero (a : Scalar.Word) (caller : Stack) :
    run code ([a,0] ++ caller) = some (maxMinusOne :: ([a,0] ++ caller)) := by
  have ran := target_run a 0 caller
  rw [result_zero] at ran
  exact ran

theorem trace (h : Int) : heightTrace code h = [h,h+1,h+2,h+1,h+2,h+3,h+2,h+1,h+1] := by
  change [h,(h)+(1),((h)+(1))+(1),(((h)+(1))+(1))+(-1),((((h)+(1))+(1))+(-1))+(1),(((((h)+(1))+(1))+(-1))+(1))+(1),((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1),(((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1),((((((((h)+(1))+(1))+(-1))+(1))+(1))+(-1))+(-1))+(0)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem capacity_exact (height : Int) :
    stackBound code height = true ↔ 0 ≤ height ∧ height+3 ≤ 1024 := by
  simp only [stackBound,trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

theorem overflow_separate :
    run code ([dirty,0] ++ List.replicate 1020 0) =
      some (maxMinusOne :: ([dirty,0] ++ List.replicate 1020 0)) ∧
    stackBound code 1022 = false := ⟨target_zero dirty _,by decide⟩

#guard (WordExpressions.compile 3 expression).isNone
#guard compiled.lowered.code 14 == none
#guard run code [dirty] == none
#guard stackBound code 1
#guard run code [dirty,0,88] == some [maxMinusOne,dirty,0,88]
#guard result 3 2 == maxMinusOne
#guard !(result 3 2 == maxWord)
#guard result dirty 5 == maxWord
#guard maxMinusOne.toNat = 2^256-2
#guard stackBound code 1021
#guard !(stackBound code 1022)
#check source dirty 0
#check target_zero dirty [88,dirty]
#check ShapeCapacity.code_frame shape #v[dirty,0]
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.actual_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_code
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shape
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.shifted_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_shape
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_run
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.result_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms result_zero
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.target_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_zero
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.capacity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capacity_exact
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.Controls.overflow_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_separate
end Solidity.Yul.Compilation.WordVisitorShapes.Controls
