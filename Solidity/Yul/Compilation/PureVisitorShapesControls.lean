import Solidity.Yul.Compilation.PureVisitorShapes

/-! Actual original-AST pure visitor combinations: ternary ADDMOD over
software BYTE/CLZ, and unbounded-intermediate modular arithmetic controls.
These are closed-Yul/scalar results, not native or logical Source/G24 runs. -/
namespace Solidity.Yul.Compilation.PureVisitorShapes.Controls
open Backend Scalar LabelExec Closed ProducerExpressions

def pair : Fin 2 → Solidity.Yul.Expr [] [] 3 1 := Fin.cases (.local 0) (fun _ => .local 1)
def arguments : Fin 3 → Solidity.Yul.Expr [] [] 3 1 :=
  Fin.cases (.builtin (.pure .byte) pair)
    (Fin.cases (.builtin (.pure .clz) (fun _ => .local 0)) (fun _ => .local 2))
def expression : Solidity.Yul.Expr [] [] 3 1 := .builtin (.pure .addmod) arguments
def compiled := (PureExpressions.compile 3 expression).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def shiftedCode := (compiled.lowered.code 12).get (by rfl)
def result (a b k : Scalar.Word) : Scalar.Word :=
  selectAddMod.value (indexedByteWindow a b) a.clz k
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_visit : PureExpressions.compile 3 expression = some compiled :=
  (Option.some_get (by rfl)).symm

theorem shape : CodeShape code 3 4 :=
  visit_shape 3 expression compiled actual_visit 0 code (Option.some_get (by rfl)).symm

theorem shifted_shape : CodeShape shiftedCode 15 16 :=
  visit_shape 3 expression compiled actual_visit 12 shiftedCode (Option.some_get (by rfl)).symm

theorem source (a b k : Scalar.Word) :
    evalExpr 3 .nil True.intro expression compiled.profile (sourceLocals #v[a,b,k]) =
      some (fun _ => (result a b k).toFin) := compiled.source #v[a,b,k]

theorem target_run (a b k : Scalar.Word) (caller : Stack) :
    run code ([a,b,k]++caller) = some (result a b k::([a,b,k]++caller)) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    compiled.lowered.correct 0 code (Option.some_get (by rfl)).symm #v[a,b,k] #v[] caller

theorem shifted_run (a b k : Scalar.Word) (newer : Vector Scalar.Word 12) (caller : Stack) :
    run shiftedCode (newer.toList++([a,b,k]++caller)) =
      some (result a b k::(newer.toList++([a,b,k]++caller))) :=
  compiled.lowered.correct 12 shiftedCode (Option.some_get (by rfl)).symm #v[a,b,k] newer caller

theorem result_zero (a b : Scalar.Word) : result a b 0 = 0 := by rfl

theorem target_zero (a b : Scalar.Word) (caller : Stack) :
    run code ([a,b,0]++caller) = some (0::([a,b,0]++caller)) :=
  (target_run a b 0 caller).trans
    (congrArg (fun value : Scalar.Word => some (value::([a,b,0]++caller))) (result_zero a b))

/-- Numeric result of the original combination; the discriminating dirty-index
control below additionally uses all-ones byte data. -/
theorem dirty_result : result dirty dirty 257 = 55 := by decide

def plainArgs : Fin 3 → Solidity.Yul.Expr [] [] 3 1 :=
  Fin.cases (.local 0) (Fin.cases (.local 1) (fun _ => .local 2))
def plainExpr : Solidity.Yul.Expr [] [] 3 1 := .builtin (.pure .addmod) plainArgs
def plainCompiled := (PureExpressions.compile 2 plainExpr).get (by rfl)
def plainCode := (plainCompiled.lowered.code 0).get (by rfl)

theorem plain_emission : plainCode = [.op (.DUP 2),.op (.DUP 2),.op (.DUP 2),.op .ADDMOD] := by rfl

theorem plain_shape : CodeShape plainCode 3 4 :=
  visit_shape 2 plainExpr plainCompiled (Option.some_get (by rfl)).symm
    0 plainCode (Option.some_get (by rfl)).symm

theorem plain_run (a b k : Scalar.Word) (caller : Stack) :
    run plainCode ([a,b,k]++caller) = some (selectAddMod.value a b k::([a,b,k]++caller)) := by
  simpa only [Vector.toList_empty,List.nil_append] using
    plainCompiled.lowered.correct 0 plainCode (Option.some_get (by rfl)).symm #v[a,b,k] #v[] caller

def maxWord : Scalar.Word := BitVec.ofNat 256 (2^256-1)

/-- Truncating the dirty index to its low byte1 would select255, notzero. -/
theorem dirty_index_guard : indexedByteWindow dirty maxWord = 0 ∧
    indexedByteWindow 1 maxWord = 255 := by decide

theorem dirty_full_result : result dirty maxWord 257 = 55 ∧
    selectAddMod.value (indexedByteWindow 1 maxWord) dirty.clz 257 = 53 := by decide

theorem dirty_full_run (caller : Stack) :
    run code ([dirty,maxWord,257]++caller) = some (55::([dirty,maxWord,257]++caller)) :=
  (target_run dirty maxWord 257 caller).trans
    (congrArg (fun value : Scalar.Word => some (value::([dirty,maxWord,257]++caller))) dirty_full_result.1)

/-- ADDMOD uses an unbounded sum; wrapped ADD first would yield256 instead. -/
theorem unbounded_sum : selectAddMod.value maxWord maxWord 257 = 0 ∧
    selectMod.value (maxWord+maxWord) 257 = 256 := by decide

theorem plain_trace (h : Int) : heightTrace plainCode h = [h,h+1,h+2,h+3,h+1] := by
  change [h,h+1,(h+1)+1,((h+1)+1)+1,(((h+1)+1)+1)+(-2)] = _
  simp only [Int.add_assoc,Int.reduceAdd]

theorem plain_capacity (h : Int) :
    stackBound plainCode h = true ↔ 0 ≤ h ∧ h+3 ≤ 1024 := by
  simp only [stackBound,plain_trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

def plainPacket : Code 1021 1022 :=
  packet plainExpr plainCompiled (Option.some_get (by rfl)).symm 0 1018 plainCode
    (Option.some_get (by rfl)).symm ((plain_capacity 1021).mpr ⟨by decide,by decide⟩)

theorem packet_instructions : plainPacket.instructions = plainCode := by rfl

theorem operand_missing : run plainCode [1] = none := by rfl

theorem capacity_not_operands : stackBound plainCode 1 = true :=
  (plain_capacity 1).mpr ⟨by decide,by decide⟩

theorem oversized (a b k : Scalar.Word) (caller : Vector Scalar.Word 1019) :
    run plainCode ([a,b,k]++caller.toList) =
      some (selectAddMod.value a b k::([a,b,k]++caller.toList)) ∧
    stackBound plainCode 1022 ≠ true := by
  refine ⟨plain_run a b k caller.toList,?_⟩
  intro accepted
  have bound := (plain_capacity 1022).mp accepted
  omega

#guard (PureExpressions.compile 2 expression).isNone
#guard compiled.lowered.code 13 = none
#guard (PureExpressions.compile 3 (Solidity.Yul.Expr.builtin (n := 3) .mload (fun _ => .local 0))).isNone

/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms shape
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.shifted_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shifted_shape
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_run
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.result_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms result_zero
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.target_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_zero
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.dirty_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dirty_result
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.plain_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms plain_emission
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.plain_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms plain_shape
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.plain_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms plain_run
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.dirty_index_guard' does not depend on any axioms -/
#guard_msgs in #print axioms dirty_index_guard
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.dirty_full_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dirty_full_result
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.dirty_full_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dirty_full_run
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.unbounded_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms unbounded_sum
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.plain_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms plain_trace
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.plain_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms plain_capacity
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.packet_instructions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms packet_instructions
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.operand_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms operand_missing
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.capacity_not_operands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_not_operands
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms oversized
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.Controls.plainPacket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms plainPacket

end Solidity.Yul.Compilation.PureVisitorShapes.Controls
