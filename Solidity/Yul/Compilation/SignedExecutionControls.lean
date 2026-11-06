import Solidity.Yul.Compilation.SignedExecution
/-! Actual original expression/statement witnesses for general signed execution.
Overflow/zero/sign/dirty controls do not substitute for the universal theorem. -/
namespace Solidity.Yul.Compilation.SignedExecution.Controls
open Solidity.Yul Solidity.Yul.Closed ProducerExpressions
open Backend Scalar MachineAdapter

def binary (op : Solidity.Yul.Pure 2) (a b : Expr [] [] 2 1) : Expr [] [] 2 1 :=
 .builtin (.pure op) (Fin.cases a (fun _ => b))
def pair (op : Solidity.Yul.Pure 2) : Expr [] [] 2 1 := binary op (.local 0) (.local 1)
def expr : Expr [] [] 2 1 :=
 binary .add (pair .sdiv) (binary .add (pair .smod) (binary .add (pair .slt) (pair .sgt)))
def compiled := (PureExpressions.compile 6 expr).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def model := (SignedMachine.selectCode code).get (by rfl)
def shiftedCode := (compiled.lowered.code 5).get (by rfl)
def shiftedModel := (SignedMachine.selectCode shiftedCode).get (by rfl)
def minimum : Scalar.Word := BitVec.ofNat 256 (2^255)
def negativeOne : Scalar.Word := BitVec.ofInt 256 (-1)
def negativeTwo : Scalar.Word := BitVec.ofInt 256 (-2)
def negativeThree : Scalar.Word := BitVec.ofInt 256 (-3)
def negativeSeven : Scalar.Word := BitVec.ofInt 256 (-7)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^255+257)

theorem actual_visit : PureExpressions.compile 6 expr = some compiled := (Option.some_get (by rfl)).symm
theorem actual_emission : compiled.lowered.code 0 = some code := (Option.some_get (by rfl)).symm
theorem actual_selection : SignedMachine.selectCode code = some model := (Option.some_get (by rfl)).symm

theorem source (locals : Vector Scalar.Word 2) :
 evalExpr 6 .nil True.intro expr compiled.profile (sourceLocals locals) =
   some (fun _ => (compiled.value locals).toFin) := compiled.source locals

theorem model_run (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run model {m with stack := locals.toList.map coreWord++caller} =
   .ok {m with stack := coreWord (compiled.value locals)::(locals.toList.map coreWord++caller)} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
   loweredExpr_machine compiled.lowered 0 code model actual_emission actual_selection locals #v[] m caller

theorem shifted_run (locals : Vector Scalar.Word 2) (newer : Vector Scalar.Word 5)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run shiftedModel {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := coreWord (compiled.value locals)::((newer.toList++locals.toList).map coreWord++caller)} 0 :=
 loweredExpr_machine compiled.lowered 5 shiftedCode shiftedModel
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals newer m caller


def boundaryCode := (compiled.lowered.code 13).get (by rfl)
def boundaryModel := (SignedMachine.selectCode boundaryCode).get (by rfl)

theorem boundary_run (locals : Vector Scalar.Word 2) (newer : Vector Scalar.Word 13)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run boundaryModel {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := coreWord (compiled.value locals)::((newer.toList++locals.toList).map coreWord++caller)} 0 :=
 loweredExpr_machine compiled.lowered 13 boundaryCode boundaryModel
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals newer m caller

theorem negative_value : compiled.value #v[negativeSeven,3] = negativeTwo := by decide
theorem negative_divisor_value : compiled.value #v[negativeSeven,negativeThree] = 2 := by decide
theorem overflow_value : compiled.value #v[minimum,negativeOne] = minimum+1 := by decide
theorem zero_divisor_value : compiled.value #v[negativeSeven,0] = 1 := by decide
theorem zero_value : compiled.value #v[0,0] = 0 := by decide
theorem dirty_distinct : compiled.value #v[dirty,3] ≠ compiled.value #v[257,3] := by decide

theorem negative_run (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run model {m with stack := [coreWord negativeSeven,coreWord 3]++caller} =
 .ok {m with stack := coreWord negativeTwo::([coreWord negativeSeven,coreWord 3]++caller)} 0 :=
 (model_run #v[negativeSeven,3] m caller).trans (congrArg (fun x : Scalar.Word =>
   Evm.Out.ok {m with stack := coreWord x::([coreWord negativeSeven,coreWord 3]++caller)} 0) negative_value)

def stmt : Stmt [] [] ⟨false,false⟩ 2 :=
 .seq (.assign (fun _ : Fin 1 => .local 0) expr)
   (.assign (fun _ : Fin 1 => .local 1) (.builtin (.pure .not) (fun _ => .local 0)))
def statementCompiled := (ScopedStatements.compile 8 stmt).get (by rfl)
def statementCode := (statementCompiled.lowered.code 0).get (by rfl)
def statementModel := (SignedMachine.selectCode statementCode).get (by rfl)

theorem statement_run (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run statementModel {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (statementCompiled.update locals).toList.map coreWord++caller} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
 loweredStmt_machine statementCompiled.lowered 0 statementCode statementModel
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals #v[] m caller

theorem statement_update : statementCompiled.update #v[negativeSeven,3] = #v[negativeTwo,1] := by decide

theorem oversized (m : Evm.Machine) (caller : Vector Evm.Word 1023) :
 Evm.run model {m with stack := [coreWord dirty,coreWord 0]++caller.toList} =
 .ok {m with stack := coreWord (compiled.value #v[dirty,0])::([coreWord dirty,coreWord 0]++caller.toList)} 0 ∧
 ([coreWord dirty,coreWord 0]++caller.toList).length > 1024 := by
 constructor
 · exact model_run #v[dirty,0] m caller.toList
 · simp only [List.length_append,List.length_cons,List.length_nil,Vector.length_toList]; omega

def observed (a b : Scalar.Word) := match Evm.run model
 {Evm.Machine.init with stack := [coreWord a,coreWord b,.slot (.root 17)]} with
 | .ok m skip => some (m.stack,skip)
 | _ => none
#guard observed negativeSeven 3 = some ([coreWord negativeTwo,coreWord negativeSeven,coreWord 3,.slot (.root 17)],0)
#guard observed minimum negativeOne = some ([coreWord (minimum+1),coreWord minimum,coreWord negativeOne,.slot (.root 17)],0)
#guard observed negativeSeven 0 = some ([coreWord 1,coreWord negativeSeven,coreWord 0,.slot (.root 17)],0)
#guard observed dirty 3 = some ([coreWord (compiled.value #v[dirty,3]),coreWord dirty,coreWord 3,.slot (.root 17)],0)
#guard (WordMachine.selectCode code).isNone
#guard (PureExpressions.compile 3 expr).isNone
#guard (compiled.lowered.code 14).isNone
#guard (compiled.lowered.code 16).isNone
#guard match Evm.run model Evm.Machine.init with | .fault => true | _ => false
#guard match Evm.Instr.step .sdiv {Evm.Machine.init with stack := [coreWord 2]} with | .fault => true | _ => false
#guard match Evm.Instr.step .smod {Evm.Machine.init with stack := [.slot (.root 17),coreWord 1]} with | .fault => true | _ => false
#guard (SignedMachine.selectInstr (.op .SAR)).isNone
#guard (SignedMachine.selectInstr (.op .SIGNEXTEND)).isNone
#guard (SignedMachine.selectInstr (.op .SSTORE)).isNone
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.boundary_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_run
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.actual_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_emission
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_selection
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.model_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_run
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.negative_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms negative_value
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.negative_divisor_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms negative_divisor_value
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.overflow_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_value
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.zero_divisor_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_divisor_value
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.zero_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_value
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.dirty_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_distinct
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.negative_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms negative_run
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.statement_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statement_run
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.statement_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statement_update
/-- info: 'Solidity.Yul.Compilation.SignedExecution.Controls.oversized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oversized
end Solidity.Yul.Compilation.SignedExecution.Controls
