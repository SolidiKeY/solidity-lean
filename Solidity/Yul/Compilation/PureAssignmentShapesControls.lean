import Solidity.Yul.Compilation.PureAssignmentShapes
import Solidity.Yul.Compilation.PureVisitorShapesControls

/-! Normal full-pure assignment and read-after-write sequence witnesses.
Raw high bits are written unchanged; original closed-source horizons, target
operand bounds and all-prefix capacity remain distinct. -/
namespace Solidity.Yul.Compilation.PureAssignmentShapes.Controls
open Backend Scalar LabelExec Closed ProducerExpressions
abbrev combined := PureVisitorShapes.Controls.expression
abbrev baseResult := PureVisitorShapes.Controls.result
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def orArgs : Fin 2 → Solidity.Yul.Expr [] [] 3 1 := Fin.cases (.local 0) (fun _ => combined)
def expression : Solidity.Yul.Expr [] [] 3 1 := .builtin (.pure .or) orArgs
def targets : Fin 1 → Solidity.Yul.Target [] 3 := fun _ => .local 2
def readTargets : Fin 1 → Solidity.Yul.Target [] 3 := fun _ => .local 1
def readExpr : Solidity.Yul.Expr [] [] 3 1 := .local 2
def first : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .assign targets expression
def second : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .assign readTargets readExpr
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .seq first second
def firstCompiled : ProducerStatements.Compiled 5 first :=
  (PureExpressions.assignment (fuel := 4) targets expression).get (by rfl)
def secondCompiled : ProducerStatements.Compiled 5 second :=
  (PureExpressions.assignment (fuel := 4) readTargets readExpr).get (by rfl)
def compiled : ProducerStatements.Compiled 6 statement := ProducerStatements.seq firstCompiled secondCompiled
def code := (compiled.lowered.code 0).get (by rfl)
def shiftedCode := (compiled.lowered.code 12).get (by rfl)
def payload (a b k : Scalar.Word) : Scalar.Word := a ||| baseResult a b k

theorem first_visit : PureExpressions.assignment (fuel := 4) targets expression = some firstCompiled :=
  (Option.some_get (by rfl)).symm

theorem second_visit : PureExpressions.assignment (fuel := 4) readTargets readExpr = some secondCompiled :=
  (Option.some_get (by rfl)).symm

theorem shape : CodeShape code 3 3 :=
  sequence_shape targets readTargets expression readExpr firstCompiled secondCompiled first_visit second_visit
    0 code (Option.some_get (by rfl)).symm

theorem shifted_shape : CodeShape shiftedCode 15 15 :=
  sequence_shape targets readTargets expression readExpr firstCompiled secondCompiled first_visit second_visit
    12 shiftedCode (Option.some_get (by rfl)).symm

/-- The second assignment reads slot2 after it was updated by the first. -/
theorem update (a b k : Scalar.Word) : compiled.update #v[a,b,k] = #v[a,payload a b k,payload a b k] := by rfl

theorem source (a b k : Scalar.Word) :
    evalStmt 6 .nil True.intro statement compiled.profile (sourceLocals #v[a,b,k]) =
      some ⟨sourceLocals #v[a,payload a b k,payload a b k],.normal⟩ := compiled.source #v[a,b,k]

theorem target_run (a b k : Scalar.Word) (caller : Stack) :
    run code ([a,b,k]++caller) = some ([a,payload a b k,payload a b k]++caller) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    compiled.lowered.correct 0 code (Option.some_get (by rfl)).symm #v[a,b,k] #v[] caller

theorem shifted_run (a b k : Scalar.Word) (newer : Vector Scalar.Word 12) (caller : Stack) :
    run shiftedCode (newer.toList++([a,b,k]++caller)) =
      some (newer.toList++([a,payload a b k,payload a b k]++caller)) :=
  compiled.lowered.correct 12 shiftedCode (Option.some_get (by rfl)).symm #v[a,b,k] newer caller

/-- With zero modulus the OR preserves every dirty input bit in both writes. -/
theorem payload_zero (a b : Scalar.Word) : payload a b 0 = a := by
  change a ||| (0 : Scalar.Word) = a
  exact BitVec.or_zero

theorem dirty_payload : payload dirty dirty 0 = dirty := payload_zero dirty dirty

theorem target_zero (a b : Scalar.Word) (caller : Stack) :
    run code ([a,b,0]++caller) = some ([a,a,a]++caller) :=
  (target_run a b 0 caller).trans
    (congrArg (fun value : Scalar.Word => some ([a,value,value]++caller)) (payload_zero a b))

/-- Both selected locals contain the full dirty word; reading old slot2=0
instead of the completed first write would not satisfy this result. -/
theorem dirty_run (caller : Stack) :
    run code ([dirty,dirty,0]++caller) = some ([dirty,dirty,dirty]++caller) :=
  target_zero dirty dirty caller

def literalExpr : Solidity.Yul.Expr [] [] 3 1 := .literal dirty.toFin
def literalStmt : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .assign targets literalExpr
def literalCompiled : ProducerStatements.Compiled 2 literalStmt :=
  (PureExpressions.assignment (fuel := 1) targets literalExpr).get (by rfl)
def literalCode := (literalCompiled.lowered.code 13).get (by rfl)

theorem literal_emission : literalCode = [pushWord dirty,.op (.SWAP 15),.op .POP] := by rfl

theorem literal_shape : CodeShape literalCode 16 16 :=
  assignment_shape targets literalExpr literalCompiled (Option.some_get (by rfl)).symm
    13 literalCode (Option.some_get (by rfl)).symm

theorem literal_run (a b k : Scalar.Word) (newer : Vector Scalar.Word 13) (caller : Stack) :
    run literalCode (newer.toList++([a,b,k]++caller)) =
      some (newer.toList++([a,b,dirty]++caller)) :=
  literalCompiled.lowered.correct 13 literalCode (Option.some_get (by rfl)).symm #v[a,b,k] newer caller

theorem literal_trace (h : Int) : heightTrace literalCode h = [h,h+1,h+1,h] := by
  change [h,h+1,(h+1)+0,((h+1)+0)+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem literal_capacity (h : Int) :
    stackBound literalCode h = true ↔ 0 ≤ h ∧ h+1 ≤ 1024 := by
  simp only [stackBound,literal_trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

def literalPacket : Code 1023 1023 :=
  packet targets literalExpr literalCompiled (Option.some_get (by rfl)).symm 13 1007 literalCode
    (Option.some_get (by rfl)).symm ((literal_capacity 1023).mpr ⟨by decide,by decide⟩)

theorem packet_instructions : literalPacket.instructions = literalCode := by rfl

theorem literal_oversized (a b k : Scalar.Word) (newer : Vector Scalar.Word 13)
    (caller : Vector Scalar.Word 1008) :
    run literalCode (newer.toList++([a,b,k]++caller.toList)) =
      some (newer.toList++([a,b,dirty]++caller.toList)) ∧
    stackBound literalCode 1024 ≠ true := by
  refine ⟨literal_run a b k newer caller.toList,?_⟩
  intro accepted
  have bound := (literal_capacity 1024).mp accepted
  omega

theorem literal_underflow : run literalCode [] = none := by rfl

#guard (PureExpressions.assignment (fuel := 3) targets expression (c := ⟨false,false⟩)).isNone
#guard compiled.lowered.code 13 = none
#guard literalCompiled.lowered.code 14 = none

/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.first_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms first_visit
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.second_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_visit
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shape
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.shifted_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shifted_shape
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms update
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_run
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.payload_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms payload_zero
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.dirty_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dirty_payload
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.target_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_zero
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.dirty_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dirty_run
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literal_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literal_emission
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literal_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literal_shape
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literal_run
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literal_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literal_trace
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literal_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literal_capacity
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.packet_instructions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms packet_instructions
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literal_oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literal_oversized
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literal_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literal_underflow
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.Controls.literalPacket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms literalPacket

end Solidity.Yul.Compilation.PureAssignmentShapes.Controls
